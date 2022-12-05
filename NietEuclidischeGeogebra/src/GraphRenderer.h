// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "Shader.h"
#include "GraphShader.h"
#include "Objects.h"

class GraphRenderer;

// Represents an OpenGL object for rendering a line
class Graph
{
public:
	Graph(float leftX, float rightX, float topY, float bottomY, int graphWindowLeftX, int graphWindowRightX, int graphWindowTopY, int graphWindowBottomY, const std::array<float, 4>& colour);
	~Graph();

	// Getters and setters
	double GetLeftX() const { return m_LeftX; }
	double GetTopY() const { return m_TopY; }
	double GetRightX() const { return m_RightX; }
	double GetBottomY() const { return m_BottomY; }

	void SetPosition(float leftX, float rightX, float topY, float bottomY);
	void updateGraphWindow(int windowLeftX, int windowRightX, int windowTopY, int WindowBottomY);

	std::array<float, 4> m_Colour;
private:
	float m_LeftX, m_RightX, m_TopY, m_BottomY;
	int m_GraphWindowLeftX, m_GraphWindowRightX, m_GraphWindowTopY, m_GraphWindowBottomY;
	GLuint m_Vao;
	GLuint m_Vb;
	GLuint m_Ib;
	friend GraphRenderer;
};

// Underlying renderer for all lines
class GraphRenderer
{
public:
	GraphRenderer();
	~GraphRenderer();

	// Add the line to the queue to be rendered this frame
	void AddToRenderQueue(const std::shared_ptr<Graph>& graph);

	// Render all the lines
	void RenderQueue();
private:
	std::queue<std::shared_ptr<Graph>> m_RenderQueue;
	Shader m_Shader;
	GraphShader m_GraphShader;
};