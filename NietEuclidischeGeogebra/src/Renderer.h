// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "LineRenderer.h"
#include "UI/WindowUI.h"

class Application;

// A class to to handle all the rendering for a window
// It doesn't render anything but dispatches it to underlying renderers
class Renderer
{
private:
	Renderer();

public:
	// Begins the rendering
	// This method calls the underlying renderers to render their queues
	void RenderQueues();

	// Update for resizing the window
	void Resize(int width, int height);

	// Add the object to the corresponding renderers queue
	void Render(std::shared_ptr<Line> line);

	~Renderer();
	friend Application;

private:
	LineRenderer* m_LineRenderer;
};