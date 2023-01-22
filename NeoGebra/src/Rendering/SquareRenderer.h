// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "Shader.h"
#include "Objects.h"

class SquareRenderer;

// Represents an OpenGL object for rendering a line
class Square
{
public:
	Square(float leftX, float rightX, float topY, float bottomY, const std::array<float, 4>& colour);
	~Square();

	// Getters and setters
	float GetLeftX() const { return m_LeftX; }
	float GetTopY() const { return m_TopY; }
	float GetRightX() const { return m_RightX; }
	float GetBottomY() const { return m_BottomY; }

	void SetPosition(float leftX, float rightX, float topY, float bottomY);

	std::array<float, 4> m_Colour;
private:
	float m_LeftX, m_RightX, m_TopY, m_BottomY;
	GLuint m_Vao;
	GLuint m_Vb;
	GLuint m_Ib;
	friend SquareRenderer;
};

// Underlying renderer for all lines
class SquareRenderer
{
public:
	SquareRenderer();
	~SquareRenderer();

	// Add the line to the queue to be rendered this frame
	void AddToRenderQueue(const std::shared_ptr<Square>& line);

	// Render all the lines
	void RenderQueue();
private:
	std::queue<std::shared_ptr<Square>> m_RenderQueue;
	Shader m_Shader;
};