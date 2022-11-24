#include "LineRenderer.h"

constexpr float BufferData[]
{
	0.2f, 0.0f,
	0.0f, 0.2f
};

LineRenderer::LineRenderer()
	: m_Shader("lineShader")
{
	glGenVertexArrays(1, &m_VertexArrayObject);
	glBindVertexArray(m_VertexArrayObject);

	glGenBuffers(1, &m_VertexBuffer);
	glBindBuffer(GL_ARRAY_BUFFER, m_VertexBuffer);
	glBufferData(GL_ARRAY_BUFFER, sizeof(BufferData), BufferData, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 0, 0);
}

LineRenderer::~LineRenderer()
{
	glDeleteBuffers(1, &m_VertexBuffer);
	glDeleteVertexArrays(1, &m_VertexArrayObject);
}

void LineRenderer::Render()
{
	glLineWidth(10.0f);
	for (const Line& l : lines)
	{
		m_Shader.SetUniform("u_Mat", l.transformationMat);
		glDrawArrays(GL_LINES, 0, 2);
	}
}

void LineRenderer::AddLine(const Line& l)
{
	lines.push_back(l);
}
