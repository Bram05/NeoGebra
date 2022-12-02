// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "Shader.h"
#include "Objects.h"

class LineRenderer;

// Represents an OpenGL object for rendering a line
class Line
{
public:
	Line(Point begin, Point end);
	~Line();

	// Getters and setters
	Point GetBegin() const { return m_Begin; }
	Point GetEnd() const { return m_End; }

	void SetLocation(Point newBegin, Point newEnd);

private:
	Point m_Begin, m_End;
	GLuint m_Vao;
	GLuint m_Vb;
	friend LineRenderer;
};

// Underlying renderer for all lines
class LineRenderer
{
public:
	LineRenderer();
	~LineRenderer();

	// Add the line to the queue to be rendered this frame
	void AddToRenderQueue(const std::shared_ptr<Line>& line);

	// Render all the lines
	void RenderQueue();
private:
	std::queue<std::shared_ptr<Line>> m_RenderQueue;
	Shader m_Shader;
};