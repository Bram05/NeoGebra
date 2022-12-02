#pragma once

#include "UIElement.h"
#include "SquareRenderer.h"

class ButtonUI : public UIElement
{
public:
	ButtonUI(double leftX, double rightX, double topY, double bottomY);
	~ButtonUI();

	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void WasClicked(float x, float y) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;
private:
	std::shared_ptr<Square> m_Background;
};