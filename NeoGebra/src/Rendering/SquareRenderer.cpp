// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "SquareRenderer.h"

Square::Square(float leftX, float rightX, float topY, float bottomY, const std::array<float, 4>& colour)
	: m_LeftX{ leftX }, m_RightX{ rightX }, m_TopY{ topY }, m_BottomY{ bottomY }, m_Colour{ colour }
{
	float buffer[8] = {
		leftX, topY,
		leftX, bottomY,
		rightX, bottomY,
		rightX, topY
	};

	// this buffer is technically not specific for every square but I think it's fine like this because of how small it is
	unsigned int indices[6] = {
		0, 1, 2,
		2, 3, 0
	};
	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 0, 0);

	glGenBuffers(1, &m_Ib);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, m_Ib);
	glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(indices), indices, GL_STATIC_DRAW);
}

Square::~Square()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteBuffers(1, &m_Ib);
	glDeleteVertexArrays(1, &m_Vao);
}

void Square::SetPosition(float leftX, float rightX, float topY, float bottomY)
{
	float buffer[8] = {
		leftX, topY,
		leftX, bottomY,
		rightX, bottomY,
		rightX, topY
	};
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, sizeof(buffer), buffer, GL_STATIC_DRAW);
}

SquareRenderer::SquareRenderer()
	: m_Shader("squareShader")
{
}

SquareRenderer::~SquareRenderer()
{
}

void SquareRenderer::AddToRenderQueue(const std::shared_ptr<Square>& square)
{
	m_RenderQueue.push(square);
}

void SquareRenderer::RenderQueue()
{
	m_Shader.Bind();
	while (!m_RenderQueue.empty())
	{
		std::shared_ptr<Square> square{ m_RenderQueue.front() };
		m_RenderQueue.pop();

		m_Shader.SetUniform("u_Colour", square->m_Colour);
		std::array<float, 2> middle = { (square->GetRightX() + square->GetLeftX()) / 2, (square->GetTopY() + square->GetBottomY()) / 2 };
		std::array<float, 2> params = { 1 / std::pow(square->GetRightX() - middle[0], 10.0f), 1 / std::pow(square->GetTopY() - middle[1], 10.0f) };
		m_Shader.SetUniform("u_Middle", middle);
		m_Shader.SetUniform("u_Params", params);
		glBindVertexArray(square->m_Vao);
		glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, 0);
	}
}
