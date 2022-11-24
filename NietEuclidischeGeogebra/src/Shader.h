#pragma once

#include <glad/glad.h>

#include "Maths/Matrix.h"

class Shader
{
public:
	Shader(const std::string path);
	~Shader();

	void Bind();
	void UnBind();

	void SetUniform(const std::string& name, const Maths::Matrix<2,2>& mat) const;

private:
	GLuint m_Shader;
	mutable std::map<std::string, int> m_UniformLocations;
	std::string m_Name;
	
	int GetUniformLocation(const std::string& name) const;
};