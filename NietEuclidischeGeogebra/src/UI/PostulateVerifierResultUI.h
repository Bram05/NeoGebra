#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

class PostulateVerifierResultUI : public UIElement
{
public:
	PostulateVerifierResultUI(double leftX, double rightX, double topY, double bottomY);
	~PostulateVerifierResultUI();

	void RenderPass(Renderer* r) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
};