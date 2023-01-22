#include "GraphComputeShaderManager.h"

#include <glad/glad.h>
#include "Constants.h"
#include "Util.h"
#include "Application.h"

enum ShaderType
{
	COMPUTE_SHADER1, COMPUTE_SHADER2
};

static int CompileShader(ShaderType type, const std::filesystem::path& path, const std::string& insertText);
static int CompileShader(ShaderType type, const std::filesystem::path& path) { return CompileShader(type, path, ""); }

GraphComputeShaderManager::GraphComputeShaderManager(const std::string& name, float width, float height)
	: m_Name{name}
{
	m_Width = Util::ConvertToPixelCoordinate(width, true);
	m_Height = Util::ConvertToPixelCoordinate(height, false);
	m_CompShader2 = CreateCompShader(m_Name + "2", "");

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
	glDeleteShader(m_CompShader2);
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

unsigned int GraphComputeShaderManager::CreateCompShader(const std::string name, const std::string& insertText) const
{
	unsigned int shaderProgram = glCreateProgram();

	std::filesystem::path path = AssetsFolder / "shaders" / name;
	path += ".comp";
	int cs = CompileShader((name.back() == '1' ? COMPUTE_SHADER1 : COMPUTE_SHADER2), path, insertText);
	glAttachShader(shaderProgram, cs);
	glLinkProgram(shaderProgram);
	int result;
	glGetProgramiv(shaderProgram, GL_LINK_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(shaderProgram, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(shaderProgram, length, &length, log);
		throw std::runtime_error(std::string("Failed to link shader ") + path.string() + ": " + log);
	}
	glDetachShader(shaderProgram, cs);
	glDeleteShader(cs);
	return shaderProgram;
}

static int CompileShader(ShaderType type, const std::filesystem::path& path, const std::string& insertText)
{
	std::ifstream file(path);
	if (!file.is_open())
	{
		throw std::runtime_error("File " + path.string() + " could not be opened");
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
	if (type == COMPUTE_SHADER1) {
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
		throw std::runtime_error("Failed to compile compute shader (" + path.string() + "): " + log);
	}
	return shader;
}

void GraphComputeShaderManager::RunComputeShader(Graph* graph) const
{
	//Util::Timer t("Running compute shader");
	glBindImageTexture(0, m_IntermediateTexture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glBindImageTexture(1, graph->GetTexture(), 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	//Run 1st shader
	glUseProgram(graph->GetCompShader1());
	// Left Right Top Bottom
	auto [midCoordX, midCoordY] = graph->GetMidCoord();
	float unitLengthPixels = graph->GetUnitLengthPixels();
	SetUniform(1, std::array<float, 4>{ midCoordX - 0.5f * m_Width / unitLengthPixels,
		midCoordX + 0.5f * m_Width / unitLengthPixels,
		midCoordY + 0.5f * m_Height / unitLengthPixels,
		midCoordY - 0.5f * m_Height / unitLengthPixels });
	glDispatchCompute(m_Width, m_Height, 1);

	//wait until program finishes
	glMemoryBarrier(GL_ALL_BARRIER_BITS);

	//Run 2nd shader
	glUseProgram(m_CompShader2);
	glDispatchCompute(m_Width, m_Height, 1);
	glMemoryBarrier(GL_ALL_BARRIER_BITS);
}
