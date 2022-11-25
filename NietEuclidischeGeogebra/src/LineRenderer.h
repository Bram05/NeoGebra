#pragma once

#include <glad/glad.h>

#include "Shader.h"
#include "Maths/Matrix.h"

struct Point
{
	float x, y;
};

class LineRenderer;

class Line
{
public:
	Line(Point begin, Point end);
	~Line();

	Point GetBegin() const { return m_Begin; }
	Point GetEnd() const { return m_End; }

	void SetLocation(Point newBegin, Point newEnd);

private:
	Point m_Begin, m_End;
	GLuint m_Vao;
	GLuint m_Vb;
	friend LineRenderer;
};

class LineRenderer
{
public:
	LineRenderer();
	~LineRenderer();

	void AddToRenderQueue(std::shared_ptr<Line> line);

	void RenderQueue();
private:
	std::queue<std::shared_ptr<Line>> m_RenderQueue;
	Shader m_Shader;
};