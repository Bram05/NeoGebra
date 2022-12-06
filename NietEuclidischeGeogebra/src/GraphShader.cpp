// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "GraphShader.h"

#include "Constants.h"
#include "Application.h"

enum ShaderType
{
	VERTEX_SHADER, FRAGMENT_SHADER, COMPUTE_SHADER
};

static int CompileShader(ShaderType type, const std::string &path);

GraphShader::GraphShader(const std::string name)
	: m_Name{name}
{
	CreateShader(name);
	m_CompShader1 = CreateCompShader(name + "1");
	m_CompShader2 = CreateCompShader(name + "2");
}

void GraphShader::CreateShader(const std::string name)
{
	m_Shader = glCreateProgram();
	std::string path = AssetsFolder + "/shaders/" + name;
	int vs = CompileShader(VERTEX_SHADER, path + ".vert");
	int fs = CompileShader(FRAGMENT_SHADER, path + ".frag");
	glAttachShader(m_Shader, vs);
	glAttachShader(m_Shader, fs);
	glLinkProgram(m_Shader);
	int result;
	glGetProgramiv(m_Shader, GL_LINK_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(m_Shader, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(m_Shader, length, &length, log);
		throw std::runtime_error(std::string("Failed to link shader ") + path + "(.vert/.frag)" + ": " + log);
	}
	glDetachShader(m_Shader, vs);
	glDetachShader(m_Shader, fs);
	glDeleteShader(vs);
	glDeleteShader(fs);
	glUseProgram(m_Shader);
}

unsigned int GraphShader::CreateCompShader(const std::string name) 
{
	unsigned int shader = glCreateProgram();
	std::string path = AssetsFolder + "/shaders/" + name;
	int cs = CompileShader(COMPUTE_SHADER, path + ".comp");
	glAttachShader(shader, cs);
	glLinkProgram(shader);
	int result;
	glGetProgramiv(shader, GL_LINK_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(shader, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(shader, length, &length, log);
		throw std::runtime_error(std::string("Failed to link shader ") + path + ".comp" + ": " + log);
	}
	glDetachShader(shader, cs);
	glDeleteShader(cs);
	glUseProgram(shader);

	return shader;
}

GraphShader::~GraphShader()
{
	glDeleteProgram(m_Shader);
}

void GraphShader::Bind()
{
	glUseProgram(m_Shader);
}

void GraphShader::UnBind()
{
	glUseProgram(0);
}

void GraphShader::SetTexture(unsigned int texture)
{
	glBindTexture(GL_TEXTURE_2D, texture);
}

void GraphShader::SetUniform(const std::string& name, const Maths::Matrix<2, 2>& mat) const
{
	int loc = GetUniformLocation(name);
	glUniformMatrix2fv(loc, 1, GL_FALSE, &mat.m_Data[0]);
}

void GraphShader::SetUniform(const std::string& name, const std::array<float, 4>& arr) const
{
	int loc = GetUniformLocation(name);
	glUniform4f(loc, arr[0], arr[1], arr[2], arr[3]);
}

static int CompileShader(ShaderType type, const std::string& path)
{
	GLuint glType;
	switch (type)
	{
	case VERTEX_SHADER:
		glType = GL_VERTEX_SHADER; break;
	case FRAGMENT_SHADER:
		glType = GL_FRAGMENT_SHADER; break;
	case COMPUTE_SHADER:
		glType = GL_COMPUTE_SHADER; break;
	default:
		throw std::runtime_error(std::string("Unknown shader type ") + std::to_string(type));
	}
	std::ifstream file(path);
	if (!file.is_open())
	{
		throw std::runtime_error("File " + path + " could not be opened");
	}
	std::stringstream source;
	std::string line;
	while (std::getline(file, line))
	{
		source << line << '\n';
	}
	GLuint shader = glCreateShader(glType);
	std::string sourceC = source.str();
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
		throw std::runtime_error(std::string("Failed to compile ") + (type == VERTEX_SHADER ? "vertex" : (type == FRAGMENT_SHADER ? "fragment" : "compute")) + " shader (" + path + "): " + log);
	}
	return shader;
}

int GraphShader::GetUniformLocation(const std::string& name) const
{
	auto it = m_UniformLocations.find(name);
	if (it == m_UniformLocations.end())
	{
		int loc = glGetUniformLocation(m_Shader, name.c_str());
		if (loc == -1)
			throw std::runtime_error("Uniform " + name + " for shader " + m_Name + " was not found or is not used");
		m_UniformLocations.insert({name, loc});
		return loc;
	}
	return it->second;
}

unsigned int GraphShader::RunComp(line Eq, float normWidth, float normHeight, int graphWindowLeftX, int graphWindowRightX, int graphWindowTopY, int graphWindowBottomY)
{
	auto [windowWidth, windowHeight] = Application::Get()->GetWindow()->GetSize();
	
	int width = static_cast<int>(windowWidth * normWidth / 2);
	int height = static_cast<int>(windowHeight * normHeight / 2); 

	//Create first texture
	unsigned int texture1;
	glGenTextures(1, &texture1);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, texture1);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, width, height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(0, texture1, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	//Create second texture
	unsigned int texture2;
	glGenTextures(1, &texture2);
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, texture2);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, width, height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(1, texture2, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	glUseProgram(m_CompShader1);
	glDispatchCompute(width, height, 1);

	//wait until program finishes
	glMemoryBarrier(GL_ALL_BARRIER_BITS);

	glUseProgram(m_CompShader2);
	glDispatchCompute(width, height, 1);

	//wait until program finishes
	glMemoryBarrier(GL_ALL_BARRIER_BITS);

	return texture2;
}
