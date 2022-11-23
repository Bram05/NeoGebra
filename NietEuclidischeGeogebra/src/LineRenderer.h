#pragma once

#include <glad/glad.h>

#include "Shader.h"

struct Point
{
	int x, y;
};

struct Line
{
	Point p1, p2;
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