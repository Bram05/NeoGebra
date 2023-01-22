// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"

// The menu at the top of the screen
class MenuUI : public UIElement
{
public:
	MenuUI(float leftX, float rightX, float topY, float bottomY);
	~MenuUI();
private:
	std::vector<std::shared_ptr<Line>> m_Lines;
protected:
	void RenderPass(Renderer* r) override;
};