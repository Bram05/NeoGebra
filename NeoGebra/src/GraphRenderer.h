// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>

#include "GraphShader.h"
#include "Objects.h"
#include "Model.h"

class GraphRenderer;

// Represents an OpenGL object for rendering a line
class Graph
{
public:
	//ToDo: change to line/point
	Graph(NEElement& el, float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, const RGBColour& colour);
	~Graph();

	// Getters and setters
	double GetLeftX() const { return m_LeftX; }
	double GetTopY() const { return m_TopY; }
	double GetRightX() const { return m_RightX; }
	double GetBottomY() const { return m_BottomY; }

	void GenTexture(float leftX, float rightX, float topY, float bottomY, float midCoordX, float midCoordY, float unitLengthPixels, GraphRenderer* rendPtr);

	RGBColour getColour() const { return m_Colour; };
	void setColour(const RGBColour& colour) { m_Colour = colour; }
	NEElement& getElement() const { return m_El; };
private:
	RGBColour m_Colour;
	float m_LeftX, m_RightX, m_TopY, m_BottomY;
	float m_MidCoordX, m_MidCoordY, m_UnitLengthPixels;
	NEElement& m_El;
	GLuint m_Vao;
	GLuint m_Vb;
	GLuint m_Ib;
	unsigned int m_CompShader1 = NULL;
	unsigned int m_Texture = NULL;
	friend GraphRenderer;
};

// Underlying renderer for all lines
class GraphRenderer
{
public:
	GraphRenderer();
	~GraphRenderer();

	//Add the line to the queue to be rendered this frame
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