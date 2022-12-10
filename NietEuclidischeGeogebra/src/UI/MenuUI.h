// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "LineRenderer.h"
#include "TextRenderer.h"
// Represents what will eventually be the part where equations can be written
class MenuUI : public UIElement
{
public:
	MenuUI(double leftX, double rightX, double topY, double bottomY);
	~MenuUI();
private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	//TextC text;
protected:
	void RenderPass(Renderer* r ) override;
};