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
	m_CompShader4 = CreateOtherComputeShader(m_Name + "4");

	glGenTextures(1, &m_IntermediateTexture1);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, m_IntermediateTexture1);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, m_Width, m_Height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(0, m_IntermediateTexture1, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	int level = 0, mipmapWidth = m_Width, mipmapHeight = m_Height;
	while (mipmapWidth != 1 && mipmapHeight != 1)
	{
		unsigned int val;
		glGenTextures(1, &val);
		glActiveTexture(GL_TEXTURE0);
		glBindTexture(GL_TEXTURE_2D, val);

		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

		glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, mipmapWidth, mipmapHeight, 0, GL_RED, GL_FLOAT, NULL);
		glBindImageTexture(0, val, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glGenerateTextureMipmap(val);
		m_IntermediateTextures2.push_back(val);

		mipmapWidth = std::max(mipmapWidth / 2, 1);
		mipmapHeight = std::max(mipmapHeight / 2, 1);
		++level;
	}
}

GraphComputeShaderManager::~GraphComputeShaderManager()
{
	glDeleteTextures(1, &m_IntermediateTexture1);
	for (unsigned int i : m_IntermediateTextures2)
		glDeleteTextures(1, &i);
	glDeleteProgram(m_CompShader2);
}

void GraphComputeShaderManager::SetGraphSize(int width, int height)
{
	m_Width = width;
	m_Height = height;
	glDeleteTextures(1, &m_IntermediateTexture1);
	for (unsigned int i : m_IntermediateTextures2)
		glDeleteTextures(1, &i);
	m_IntermediateTextures2.resize(0);
	int level = 0, mipmapWidth = m_Width, mipmapHeight = m_Height;
	while (mipmapWidth != 1 && mipmapHeight != 1)
	{
		unsigned int val;
		glGenTextures(1, &val);
		glActiveTexture(GL_TEXTURE0);
		glBindTexture(GL_TEXTURE_2D, val);

		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

		glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, mipmapWidth, mipmapHeight, 0, GL_RED, GL_FLOAT, NULL);
		//glBindImageTexture(0, val, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		//glGenerateTextureMipmap(val);
		m_IntermediateTextures2.push_back(val);

		mipmapWidth = std::max(mipmapWidth / 2, 1);
		mipmapHeight = std::max(mipmapHeight / 2, 1);
		++level;
	}
	unsigned int val;
	glGenTextures(1, &val);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, val);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, mipmapWidth, mipmapHeight, 0, GL_RED, GL_FLOAT, NULL);
	m_IntermediateTextures2.push_back(val);
	m_IntermediateTexture1 = CreateTexture();
}

void GraphComputeShaderManager::SetUniform(unsigned int loc, const std::array<float, 4>& vec) const
{
	glUniform4f(loc, vec[0], vec[1], vec[2], vec[3]);
}

void GraphComputeShaderManager::CreateShader(Graph* graph, const std::string& name) const
{
	graph->m_CompShader1 = glCreateProgram();
	graph->m_Texture = CreateTexture();

	std::filesystem::path path = AssetsFolder / "shaders" / name;
	path += "1.comp";
	unsigned int shader = CompileShader(true, path, graph->getElement().getShader());
	glAttachShader(graph->m_CompShader1, shader);
	glLinkProgram(graph->m_CompShader1);
	int result;
	glGetProgramiv(graph->m_CompShader1, GL_LINK_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(graph->m_CompShader1, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(graph->m_CompShader1, length, &length, log);
		std::cerr << "Failed to link shader " << path << ": " << log << '\n';
		Util::ExitDueToFailure();
	}
	glDetachShader(graph->m_CompShader1, shader);
	glDeleteShader(shader);
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
	glBindImageTexture(0, m_IntermediateTexture1, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glBindImageTexture(1, m_IntermediateTextures2[0], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	Util::Timer t("Running compute shader1");
	//Run 1st shader
	glUseProgram(graph->m_CompShader1);
	// Left Right Top Bottom
	SetUniform(1, std::array<float, 4>{ midCoordX - 0.5f * m_Width / unitLengthPixels,
		midCoordX + 0.5f * m_Width / unitLengthPixels,
		midCoordY + 0.5f * m_Height / unitLengthPixels,
		midCoordY - 0.5f * m_Height / unitLengthPixels });
	glUniform2f(0, m_Width, m_Height);
	glDispatchCompute(std::ceil(m_Width/32.0f), std::ceil(m_Height/32.0f), 1);
	glMemoryBarrier(GL_ALL_BARRIER_BITS);
	glFinish();
	t.Stop();

	t.Restart("Running compute shader2");
	glUseProgram(m_CompShader2);
	glDispatchCompute(std::ceil(m_Width/32.0f), std::ceil(m_Height/32.0f), 1);
	glMemoryBarrier(GL_ALL_BARRIER_BITS);
	glFinish();
	t.Stop();

	t.Restart("Running compute shader3");
	//int prevMipmapWidth = m_Width, prevMipmapHeight = m_Height;
	int i = 0, mipmapWidth = m_Width / 2, mipmapHeight = m_Height / 2;
	glUseProgram(m_CompShader3);
	for (; i < m_IntermediateTextures2.size()-1; ++i)
	{
		glBindImageTexture(0, m_IntermediateTextures2[i], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		glBindImageTexture(1, m_IntermediateTextures2[i+1], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
		//glUniform2i(1, prevMipmapWidth, prevMipmapHeight);
		glUniform2i(0, mipmapWidth, mipmapHeight);
		//glUniform1i(0, level);
		glDispatchCompute(std::ceil(mipmapWidth / 8.0f), std::ceil(mipmapHeight / 8.0f), 1);
		glMemoryBarrier(GL_ALL_BARRIER_BITS);

		mipmapWidth = std::max(mipmapWidth / 2, 1);
		//prevMipmapWidth = std::max(prevMipmapWidth / 2, 1);
		mipmapHeight = std::max(mipmapHeight / 2, 1);
		//prevMipmapHeight = std::max(prevMipmapHeight / 2, 1);
	}
	glFinish();
	t.Stop();

	t.Restart("Running compute shader4");
	glUseProgram(m_CompShader4);
	glBindImageTexture(0, m_IntermediateTextures2[0], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glBindImageTexture(1, m_IntermediateTextures2[i], 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glBindImageTexture(2, graph->m_Texture, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glDispatchCompute(std::ceil(m_Width / 32.0f), std::ceil(m_Height / 32.0f), 1);
	glFinish();
	t.Stop();
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
