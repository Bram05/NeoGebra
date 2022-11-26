#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

class EquationUI : public UIElement
{
public:
	EquationUI(double topLeftX, double topLeftY, double bottomRightX, double bottomRightY);
	~EquationUI();

	void RenderPass() override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
};