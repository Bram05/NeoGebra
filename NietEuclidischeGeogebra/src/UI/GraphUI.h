#pragma once

#include "UIElement.h"

class GraphUI : public UIElement
{
public:
	GraphUI(float leftX, float rightX, float topY, float bottomY);
	~GraphUI();

protected:
	void RenderPass(Renderer* r) override;
	void ResizeWindow(int width, int height) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;

	void UpdateLines();
};