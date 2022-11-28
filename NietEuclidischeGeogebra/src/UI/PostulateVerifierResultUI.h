#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

class PostulateVerifierResultUI : public UIElement
{
public:
	PostulateVerifierResultUI(double topLeftX, double topLeftY, double bottomRightX, double bottomRightY);
	~PostulateVerifierResultUI();

	void RenderPass(Renderer* r) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
};