#include "GraphComputeShaderManager.h"

#include <glad/glad.h>
#include "Constants.h"
#include "Util.h"
#include "Application.h"

enum ShaderType
{
	COMPUTE_SHADER1, COMPUTE_SHADER2, COMPUTE_SHADER3
};

static unsigned int CompileShader(bool isFirst, const std::filesystem::path& path, const std::string& insertText);
static unsigned int CompileShader(bool isFirst, const std::filesystem::path& path) { return CompileShader(isFirst, path, ""); }

GraphComputeShaderManager::GraphComputeShaderManager(const std::string& name, float width, float height)
	: m_Name{ name }
{
	m_Width = Util::ConvertToPixelValue(width, true);
	m_Height = Util::ConvertToPixelValue(height, false);
	m_CompShader2 = CreateOtherComputeShader(m_Name + "2");
	m_CompShader3 = CreateOtherComputeShader(m_Name + "3");

	glGenTextures(1, &m_IntermediateTexture);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, m_IntermediateTexture);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, m_Width, m_Height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(0, m_IntermediateTexture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
}

GraphComputeShaderManager::~GraphComputeShaderManager()
{
	glDeleteTextures(1, &m_IntermediateTexture);
	glDeleteProgram(m_CompShader2);
}

void GraphComputeShaderManager::SetGraphSize(float width, float height)
{
	m_Width = Util::ConvertToPixelCoordinate(width, true);
	m_Height = Util::ConvertToPixelCoordinate(height, true);
}

void GraphComputeShaderManager::SetUniform(unsigned int loc, const std::array<float, 4>& vec) const
{
	glUniform4f(loc, vec[0], vec[1], vec[2], vec[3]);
}

static std::vector<unsigned int> CompileShadersRecursive(std::shared_ptr<OrAnd> currentObj, const std::filesystem::path& path)
{
	if (currentObj->isEnd)
	{
		return { CompileShader(true, path, currentObj->content)};
	}
	std::vector<unsigned int> ret = CompileShadersRecursive(currentObj->s1, path);
	std::vector<unsigned int> ret2 = CompileShadersRecursive(currentObj->s2, path);
	ret.insert(ret.end(), ret2.begin(), ret2.end());
	return ret;
}

std::pair<std::vector<unsigned int>, std::vector<unsigned int>> GraphComputeShaderManager::CreateFirstCompShaders(const std::string& name, std::shared_ptr<OrAnd> equations) const
{
	std::vector<unsigned int> programs;
	std::vector<unsigned int> textures;

	std::filesystem::path path = AssetsFolder / "shaders" / name;
	path += ".comp";
	std::vector<unsigned int> cs = CompileShadersRecursive(equations, path);
	programs.reserve(cs.size());
	textures.reserve(cs.size());
	for (unsigned int shader : cs)
	{
		programs.push_back(glCreateProgram());
		glAttachShader(programs.back(), shader);
		glLinkProgram(programs.back());
		int result;
		glGetProgramiv(programs.back(), GL_LINK_STATUS, &result);
		if (result == GL_FALSE)
		{
			int length;
			glGetProgramiv(programs.back(), GL_INFO_LOG_LENGTH, &length);

			char* log = new char[length];
			glGetProgramInfoLog(programs.back(), length, &length, log);
			std::cerr << "Failed to link shader " << path << ": " << log << '\n';
			Util::ExitDueToFailure();
		}
		glDetachShader(programs.back(), shader);
		glDeleteShader(shader);

		textures.push_back(CreateTexture());
	}
	return {programs, textures};
}

static unsigned int CompileShader(bool isFirst, const std::filesystem::path& path, const std::string& insertText)
{
	std::ifstream file(path);
	if (!file.is_open())
	{
		std::cerr << "File " << path.string() << " could not be opened\n";
		Util::ExitDueToFailure();
	}
	std::stringstream source;
	std::string line;
	while (std::getline(file, line))
	{
		source << line << '\n';
	}
	GLuint shader = glCreateShader(GL_COMPUTE_SHADER);
	std::string sourceC = source.str();

	// If the shader is the first compute shader, the formula should be inserted
	if (isFirst) {
		sourceC.replace(sourceC.find("[EQUATION]"), 10, insertText);
	}

	const char* s = sourceC.c_str();
	glShaderSource(shader, 1, &s, nullptr);
	glCompileShader(shader);
	int result;
	glGetShaderiv(shader, GL_COMPILE_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetShaderInfoLog(shader, length, &length, log);
		std::cerr << "Failed to compile compute shader (" << path.string() << "): " << log << '\n';
		Util::ExitDueToFailure();
	}
	return shader;
}

static unsigned int counter = 0;

unsigned int GraphComputeShaderManager::RunRecursive(Graph* graph, std::shared_ptr<OrAnd> currentObj, float midCoordX, float midCoordY, float unitLengthPixels) const
{
	if (currentObj->isEnd)
	{
		glBindImageTexture(0, m_IntermediateTexture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glUseProgram(graph->GetCompShader1()[counter]);
		// Left Right Top Bottom
		SetUniform(1, std::array<float, 4>{ midCoordX - 0.5f * m_Width / unitLengthPixels,
			midCoordX + 0.5f * m_Width / unitLengthPixels,
			midCoordY + 0.5f * m_Height / unitLengthPixels,
			midCoordY - 0.5f * m_Height / unitLengthPixels });
		glDispatchCompute(m_Width, m_Height, 1);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);

		glUseProgram(m_CompShader2);
		glBindImageTexture(1, graph->GetTextures()[counter], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glDispatchCompute(m_Width, m_Height, 1);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);
		return counter++;
	}
	else
	{
		unsigned int first = RunRecursive(graph, currentObj->s1, midCoordX, midCoordY, unitLengthPixels);
		unsigned int second = RunRecursive(graph, currentObj->s1, midCoordX, midCoordY, unitLengthPixels);

		glUseProgram(m_CompShader3);
		glBindImageTexture(0, graph->GetTextures()[first], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glBindImageTexture(1, graph->GetTextures()[second], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glUniform1i(0, !currentObj->isOr);
		glDispatchCompute(m_Width, m_Height, 1);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);
		return first;
	}
}

unsigned int GraphComputeShaderManager::CreateOtherComputeShader(const std::string& name) const
{
	unsigned int program = glCreateProgram();

	std::filesystem::path path = AssetsFolder / "shaders" / name;
	path += ".comp";
	unsigned int shader = CompileShader(false, path);
	glAttachShader(program, shader);
	glLinkProgram(program);
	int result;
	glGetProgramiv(program, GL_LINK_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(program, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(program, length, &length, log);
		std::cerr << "Failed to link shader " << path << ": " << log << '\n';
		Util::ExitDueToFailure();
	}
	glDetachShader(program, shader);
	glDeleteShader(shader);
	return program;
}

void GraphComputeShaderManager::RunComputeShaders(Graph* graph, float midCoordX, float midCoordY, float unitLengthPixels) const
{
	counter = 0;
	//glBindImageTexture(0, m_IntermediateTexture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	/*//Run 1st shader
	for (unsigned int i{ 0 }; i < graph->GetCompShader1().size(); ++i)
	{
		//glBindImageTexture(i % m_MaxNumberOfTextureUnits, m_IntermediateTexture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glUseProgram(graph->GetCompShader1()[i]);
		// Left Right Top Bottom
		SetUniform(1, std::array<float, 4>{ midCoordX - 0.5f * m_Width / unitLengthPixels,
			midCoordX + 0.5f * m_Width / unitLengthPixels,
			midCoordY + 0.5f * m_Height / unitLengthPixels,
			midCoordY - 0.5f * m_Height / unitLengthPixels });
		glDispatchCompute(m_Width, m_Height, 1);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);

		glUseProgram(m_CompShader2);
		glBindImageTexture(1, graph->GetTextures()[i], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);
	}*/

	unsigned int output = RunRecursive(graph, graph->GetOrAnd(), midCoordX, midCoordY, unitLengthPixels);
	if (output != 0)
	{
		std::cerr << "Output should have been 0! error!";
		Util::ExitDueToFailure();
	}
}

unsigned int GraphComputeShaderManager::CreateTexture() const
{
	unsigned int texture;
	glGenTextures(1, &texture);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, texture);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, m_Width, m_Height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(0, texture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	return texture;
}
