// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "Maths/Matrix.h"

// Handles an OpenGL shader object
// The shaders are written in GLSL
class Shader
{
public:
	// name = the name of shader. For shader assets/shaders/example.vs name would be: example
	Shader(const std::string name);
	~Shader();

	// Bind and unbind the shader
	void Bind();
	void UnBind();

	// Set the uniform for the shader
	void SetUniform(const std::string& name, const Maths::Matrix<2,2>& mat) const;

private:
	GLuint m_Shader;
	mutable std::map<std::string, int> m_UniformLocations;
	std::string m_Name;
	
	int GetUniformLocation(const std::string& name) const;
};