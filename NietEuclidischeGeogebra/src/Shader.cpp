#include "Shader.h"

#include "Constants.h"

enum ShaderType
{
	VERTEX_SHADER, FRAGMENT_SHADER
};

static int CompileShader(ShaderType type, const std::string &path);

Shader::Shader(const std::string name)
{
	m_Shader = glCreateProgram();
	int vs = CompileShader(VERTEX_SHADER, AssetsFolder + "/shaders/" + name + ".vs");
	int fs = CompileShader(FRAGMENT_SHADER, AssetsFolder + "/shaders/" + name + ".frags");
	glAttachShader(m_Shader, vs);
	glAttachShader(m_Shader, fs);
	glLinkProgram(m_Shader);
	int result;
	glGetProgramiv(m_Shader, GL_COMPILE_STATUS, &result);
	if (result == GL_FALSE)
	{
		int length;
		glGetProgramiv(m_Shader, GL_INFO_LOG_LENGTH, &length);

		char* log = new char[length];
		glGetProgramInfoLog(m_Shader, length, &length, log);
		throw std::runtime_error(std::string("Failed to link shader ") + name + ": " + log);
	}
	glDeleteShader(vs);
	glDeleteShader(fs);
}

Shader::~Shader()
{
	glDeleteProgram(m_Shader);
}

void Shader::Bind()
{
	glUseProgram(m_Shader);
}

void Shader::UnBind()
{
	glUseProgram(0);
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
		throw std::runtime_error(std::string("Failed to compile ") + (type == VERTEX_SHADER ? "vertex" : "fragment") + " shader (" + path + "): " + log);
	}
	return shader;
}