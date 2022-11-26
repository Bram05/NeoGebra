// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "LineRenderer.h"

#include "Application.h"

LineRenderer::LineRenderer()
	: m_Shader("lineShader")
{
}

LineRenderer::~LineRenderer()
{
}

void LineRenderer::AddToRenderQueue(std::shared_ptr<Line> line)
{
	m_RenderQueue.push(line);
}

void LineRenderer::RenderQueue()
{
	m_Shader.Bind();
	glLineWidth(10.0f);
	while (m_RenderQueue.size() != 0)
	{
		std::shared_ptr<Line> l = m_RenderQueue.front();
		m_RenderQueue.pop();

		glBindVertexArray(l->m_Vao);
		glDrawArrays(GL_LINES, 0, 2);
	}
}

Line::Line(Point begin, Point end)
	: m_Begin{begin}, m_End{end}
{
	float buffer[4] = {
		begin.x, begin.y,
		end.x, end.y
	};
	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 0, 0);
}

Line::~Line()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteVertexArrays(1, &m_Vao);
}

void Line::SetLocation(Point newBegin, Point newEnd)
{
	float buffer[4] = {
		newBegin.x, newBegin.y,
		newEnd.x, newEnd.y
	};
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferSubData(GL_ARRAY_BUFFER, 0, sizeof(buffer), buffer);
}