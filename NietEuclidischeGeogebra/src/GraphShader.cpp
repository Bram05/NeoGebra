// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "GraphShader.h"

#include "Constants.h"
#include "Application.h"

enum ShaderType
{
	VERTEX_SHADER, FRAGMENT_SHADER, COMPUTE_SHADER1, COMPUTE_SHADER2, COMPUTE_SHADER3
};

static int CompileShader(ShaderType type, const std::string& path, const std::string& insertText);
static int CompileShader(ShaderType type, const std::string& path) { return CompileShader(type, path, ""); }

GraphShader::GraphShader(const std::string name)
	: m_Name{ name }
{
	CreateShader(name);
	CreateCompShader(m_Name + "2", "", m_CompShader2);
	CreateCompShader(m_Name + "3", "", m_CompShader3);
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

void GraphShader::CreateCompShader(const std::string name, const std::string& insertText, unsigned int& shaderProgram)
{
	// If it exists, delete old shader
	if (shaderProgram != NULL) {
		glDeleteProgram(shaderProgram);
	}

	shaderProgram = glCreateProgram();

	std::string path = AssetsFolder + "/shaders/" + name;
	int cs = CompileShader((name.back() == '1' ? COMPUTE_SHADER1 : (name.back() == '2' ? COMPUTE_SHADER2 : COMPUTE_SHADER3)), path + ".comp", insertText);
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
		throw std::runtime_error(std::string("Failed to link shader ") + path + ".comp" + ": " + log);
	}
	glDetachShader(shaderProgram, cs);
	glDeleteShader(cs);
	glUseProgram(shaderProgram);
}

GraphShader::~GraphShader()
{
	glDeleteProgram(m_Shader);
	glDeleteProgram(m_CompShader2);
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

void GraphShader::SetUniform2d(const std::string& name, const std::array<std::array<int, 7>, 7>& arr) const {
	int loc = GetUniformLocation(name + "[0][0]");
	for (int i = 0; i < 7; ++i) {
		std::array<int, 7> subArr = arr[i];
		glUniform1iv(loc + 7 * i, 7, &subArr[0]);
	}
}

void GraphShader::SetUniform(const int loc, const std::array<float, 4>& arr) const
{
	glUniform4f(loc, arr[0], arr[1], arr[2], arr[3]);
}

static int CompileShader(ShaderType type, const std::string& path, const std::string& insertText)
{
	GLuint glType;
	switch (type)
	{
	case VERTEX_SHADER:
		glType = GL_VERTEX_SHADER; break;
	case FRAGMENT_SHADER:
		glType = GL_FRAGMENT_SHADER; break;
	case COMPUTE_SHADER1:
	case COMPUTE_SHADER2:
	case COMPUTE_SHADER3:
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

	// If the shader is the first compute shader, the formula should be inserted
	if (type == COMPUTE_SHADER1) {
		sourceC.replace(sourceC.find("[EQUATION]"), 10, insertText);
		std::cout << sourceC << '\n';
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
		m_UniformLocations.insert({ name, loc });
		return loc;
	}
	return it->second;
}

unsigned int GraphShader::RunComp(float normWidth, float normHeight, float midCoordX, float midCoordY, float unitLengthPixels, unsigned int compShader1)
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
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);

	glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, width, height, 0, GL_RED, GL_FLOAT, NULL);
	glBindImageTexture(1, texture2, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);


	//Run 1st shader
	glUseProgram(compShader1);
	// Left Right Top Bottom
	SetUniform(1, std::array<float, 4>{ midCoordX - 0.5f * width / unitLengthPixels,
		midCoordX + 0.5f * width / unitLengthPixels,
		midCoordY + 0.5f * height / unitLengthPixels,
		midCoordY - 0.5f * height / unitLengthPixels });
	glDispatchCompute(width, height, 1);

	//wait until program finishes
	glMemoryBarrier(GL_ALL_BARRIER_BITS);

	//float* data = new float[width * height*2];
	//glGetTextureImage(texture1, 0, GL_RED, GL_FLOAT, width*height*sizeof(float), data);
	//float biggest{0.0f};
	//for (int x{ 0 }; x < width; ++x)
	//{
	//	for (int y{ 0 }; y < height; ++y)
	//	{
	//		if (data[x*width+y] > biggest && data[x * width + y] != std::numeric_limits<float>::infinity())
	//			biggest = std::max(biggest, data[x * width + y]);
	//	}
	//}


	//Run 2nd shader
	glUseProgram(m_CompShader2);
	//glUniform1f(glGetUniformLocation(m_CompShader2, "u_BiggestErr"), biggest);
	glDispatchCompute(width, height, 1);

	glMemoryBarrier(GL_ALL_BARRIER_BITS);

	glBindImageTexture(1, texture1, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);
	glBindImageTexture(0, texture2, 0, GL_FALSE, 0, GL_READ_WRITE, GL_R32F);

	//glUseProgram(m_CompShader3);
	//glDispatchCompute(width, height, 1);

	glMemoryBarrier(GL_ALL_BARRIER_BITS);
	//glDeleteTextures(1, &texture2);
	//return texture2;
	//return texture1;

	float* data = new float[width * height * 2];
	glGetTextureImage(texture2, 0, GL_RED, GL_FLOAT, width * height * sizeof(float), data);
	std::cout << "Middle: " << data[width / 2 * width + (height / 2)] << '\n';

	std::ofstream out("power1000.xls");
	if (!out)
	{
		std::cerr << "err!";
		return texture1;
	}
	out << std::setprecision(2);

	for (int x{ 0 }; x < width; ++x)
	{
		for (int y{ 0 }; y < height; ++y)
		{
			out << data[x * width + y] << '\t';
		}
		out << '\n';
	}

	return texture1;
}
