#pragma once

#include "LineRenderer.h"

class Application;

class Renderer
{
private:
	Renderer();

public:
	void AddLine(const Line& line);
	void Render(float r, float g, float b, float a);

	void Resize(int width, int height);

	~Renderer();
	friend Application;

private:
	LineRenderer* m_LineRenderer;
};