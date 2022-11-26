// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

// Represents what will eventually be the part where equations can be written
class EquationUI : public UIElement
{
public:
	EquationUI(double topLeftX, double topLeftY, double bottomRightX, double bottomRightY);
	~EquationUI();

	void RenderPass() override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
};