#pragma once

#include "LineRenderer.h"

class Application;

class Renderer
{
private:
	Renderer();

public:
	void AddLine(const Line& line);
	void BeginRenderPass(float r, float g, float b, float a);

	void Resize(int width, int height);

	void Render(std::shared_ptr<Line> line);
	LineRenderer* GetLineRenderer() { return m_LineRenderer; }

	~Renderer();
	friend Application;

private:
	LineRenderer* m_LineRenderer;
};