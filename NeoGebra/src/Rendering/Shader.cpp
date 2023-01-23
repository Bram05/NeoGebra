// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "Shader.h"

#include "Constants.h"
#include "Util.h"

enum ShaderType
{
	VERTEX_SHADER, FRAGMENT_SHADER
};

static int CompileShader(ShaderType type, const std::filesystem::path& path);

Shader::Shader(const std::string name)
	: m_Name{ name }
{
	m_Shader = glCreateProgram();
	std::filesystem::path vertexPath = AssetsFolder / "shaders" / name;
	vertexPath += ".vert";
	std::filesystem::path fragmentPath = AssetsFolder / "shaders" / name;
	fragmentPath += ".frag";

	int vs = CompileShader(VERTEX_SHADER, vertexPath);
	int fs = CompileShader(FRAGMENT_SHADER, fragmentPath);
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
		std::cerr << "Failed to link shader " << name << ": " << log << '\n';
		Util::ExitDueToFailure();
	}
	glDetachShader(m_Shader, vs);
	glDetachShader(m_Shader, fs);
	glDeleteShader(vs);
	glDeleteShader(fs);
	glUseProgram(m_Shader);
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

void Shader::SetUniform(const std::string& name, const std::array<float, 4>& arr) const
{
	int loc = GetUniformLocation(name);
	glUniform4f(loc, arr[0], arr[1], arr[2], arr[3]);
}

void Shader::SetUniform(const std::string& name, const std::array<float, 2>& arr) const
{
	int loc = GetUniformLocation(name);
	glUniform2f(loc, arr[0], arr[1]);
}

void Shader::SetUniform(const std::string& name, int i) const
{
	int loc = GetUniformLocation(name);
	glUniform1i(loc, i);
}

static int CompileShader(ShaderType type, const std::filesystem::path& path)
{
	GLuint glType;
	switch (type)
	{
	case VERTEX_SHADER:
		glType = GL_VERTEX_SHADER; break;
	case FRAGMENT_SHADER:
		glType = GL_FRAGMENT_SHADER; break;
	default:
		std::cerr << "Unknown shader type " << std::to_string(type) << '\n';
		Util::ExitDueToFailure();
	}
	std::ifstream file(path);
	if (!file.is_open())
	{
		std::cerr << "Shader " << path << " could not be opened\n";
		Util::ExitDueToFailure();
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
		std::cout << log << std::endl;
		std::cerr << "Failed to compile " << (type == VERTEX_SHADER ? "vertex" : "fragment") << " shader (" << path << "): " << log << '\n';
		Util::ExitDueToFailure();
	}
	return shader;
}

int Shader::GetUniformLocation(const std::string& name) const
{
	auto it = m_UniformLocations.find(name);
	if (it == m_UniformLocations.end())
	{
		int loc = glGetUniformLocation(m_Shader, name.c_str());
		if (loc == -1)
			std::cout << "Uniform " + name + " for shader " + m_Name + " was not found or is not used\n";
		m_UniformLocations.insert({ name, loc });
		return loc;
	}
	return it->second;
}
