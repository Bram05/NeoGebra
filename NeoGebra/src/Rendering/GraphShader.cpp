// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "GraphShader.h"

#include "Constants.h"
#include "Application.h"
#include "Util.h"

enum ShaderType
{
	VERTEX_SHADER, FRAGMENT_SHADER
};

static int CompileShader(ShaderType type, const std::filesystem::path& path, const std::string& insertText);
static int CompileShader(ShaderType type, const std::filesystem::path& path) { return CompileShader(type, path, ""); }

GraphShader::GraphShader(const std::string name)
	: m_Name{ name }
{
	CreateShader(name);
}

void GraphShader::CreateShader(const std::string name)
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

void GraphShader::SetUniform(const std::string& name, const std::array<float, 4>& arr) const
{
	int loc = GetUniformLocation(name);
	glUniform4f(loc, arr[0], arr[1], arr[2], arr[3]);
}

void GraphShader::SetUniform(const std::string& name, int val) const {
	int loc = GetUniformLocation(name);
	glUniform1i(loc, val);
}

void GraphShader::SetUniform(const std::string& name, float val) const
{
	int loc = GetUniformLocation(name);
	glUniform1f(loc, val);
}

void GraphShader::SetUniform(const std::string& name, const std::array<std::array<float, 7>, 7>& arr) const {
	int loc = GetUniformLocation(name + "[0][0]");
	for (int i = 0; i < 7; ++i) {
		std::array<float, 7> subArr = arr[i];
		glUniform1fv(loc + 7 * i, 7, &subArr[0]);
	}
}

void GraphShader::SetUniform(const int loc, const std::array<float, 4>& arr) const
{
	glUniform4f(loc, arr[0], arr[1], arr[2], arr[3]);
}

static int CompileShader(ShaderType type, const std::filesystem::path& path, const std::string& insertText)
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
		std::cerr << "Failed to compile " << (type == VERTEX_SHADER ? "vertex" : (type == FRAGMENT_SHADER ? "fragment" : "compute")) << " shader (" << path << "): " << log << '\n';
		Util::ExitDueToFailure();
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
		{
			// This isn't really an unrecoverable situation but it is easier to just crash
			// It really shouldn't happen anyway
			std::cerr << "Uniform " << name << " for shader " << m_Name << " was not found or is not used\n";
			Util::ExitDueToFailure();
		}
		m_UniformLocations.insert({ name, loc });
		return loc;
	}
	return it->second;
}
