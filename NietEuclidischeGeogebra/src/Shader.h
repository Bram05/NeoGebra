#pragma once

#include <glad/glad.h>

class Shader
{
public:
	Shader(const std::string path);
	~Shader();

	void Bind();
	void UnBind();

private:
	GLuint m_Shader;
};