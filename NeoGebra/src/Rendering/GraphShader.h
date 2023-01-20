// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "Maths/Model.h"


// Handles an OpenGL shader object
// The shaders are written in GLSL
class GraphShader
{
public:
	// name = the name of shader. For shader assets/shaders/example.vs name would be: example
	GraphShader(const std::string name);
	~GraphShader();

	// Bind and unbind the shader
	void Bind();
	void UnBind();

	// Set the texture for the shader
	void SetTexture(unsigned int texture);

	// Set the uniform for the shader
	void SetUniform(const std::string& name, const std::array<float, 4>& arr) const;
	void SetUniform(const std::string& name, int val) const;
	void SetUniform(const std::string& name, float val) const;
	void SetUniform(const std::string& name, const std::array<std::array<float, 7>, 7>& arr) const;
	void SetUniform(const int loc, const std::array<float, 4>& arr) const;

	unsigned int RunComp(float normWidth, float normHeight, float midCoordX, float midCoordY, float unitLengthPixels, unsigned int compShader1);
	static void CreateCompShader(const std::string name, const std::string& insertText, unsigned int& shaderProgram);
private:
	void CreateShader(const std::string name);
	GLuint m_Shader;
	GLuint m_CompShader2 = NULL;
	GLuint m_CompShader3 = NULL;
	mutable std::map<std::string, int> m_UniformLocations;
	std::string m_Name;
	int GetUniformLocation(const std::string& name) const;
};