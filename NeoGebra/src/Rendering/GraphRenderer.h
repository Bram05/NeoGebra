// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "GraphShader.h"
#include "Objects.h"
#include "Maths/Model.h"
#include "Maths/Equation.h"
#include "GraphComputeShaderManager.h"

class GraphRenderer;

// Represents an OpenGL object for rendering a graph
// These graphs are the graphs that are seen in the middle of the screen
class Graph
{
public:
	//ToDo: change to line/point
	Graph(NEElement& el, const GraphComputeShaderManager& manager, float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, const RGBColour& colour);
	~Graph();

	// Getters and setters
	unsigned int GetCompShader1() const { return m_CompShader1; }
	unsigned int GetTexture() const { return m_Texture; }

	RGBColour getColour() const { return m_Colour; };
	void setColour(const RGBColour& colour) { m_Colour = colour; }
	NEElement& getElement() const { return m_El; };
private:
	RGBColour m_Colour;
	NEElement& m_El;
	GLuint m_Vao;
	GLuint m_Vb;
	GLuint m_Ib;
	unsigned int m_CompShader1 = NULL;
	unsigned int m_Texture;
	friend GraphRenderer;
};

// Underlying renderer for all graph
class GraphRenderer
{
public:
	GraphRenderer();
	~GraphRenderer();

	//Add the graph to the queue to be rendered this frame
	void AddToRenderQueue(const std::shared_ptr<Graph>& graph);

	void setLineThickness(int pixels);
	void setPointSize(int pixels);

	// Render all the lines
	void RenderQueue();
private:
	std::queue<std::shared_ptr<Graph>> m_RenderQueue;
	int m_LineThickness;
	int m_PointSize;
	std::array<std::array<float, 7>, 7> m_Kernel;
	GraphShader m_Shader;
	friend Graph;
};

bool operator==(const NEElement e, const std::shared_ptr<Graph> g);
bool operator!=(const NEElement e, const std::shared_ptr<Graph> g);
bool operator==(const std::shared_ptr<Graph> g, const NEElement e);
bool operator!=(const std::shared_ptr<Graph> g, const NEElement e);