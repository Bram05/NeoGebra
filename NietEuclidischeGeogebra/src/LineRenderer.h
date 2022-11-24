#pragma once

#include <glad/glad.h>

#include "Shader.h"
#include "Maths/Matrix.h"

struct Point
{
	int x, y;
};

struct Line
{
	Maths::Matrix<2, 2> transformationMat;
};

class LineRenderer
{
public:
	LineRenderer();
	~LineRenderer();

	void Render();

	void AddLine(const Line& l);
private:
	std::vector<Line> lines;

	GLuint m_VertexBuffer;
	GLuint m_VertexArrayObject;
	Shader m_Shader;
};