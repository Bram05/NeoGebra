#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

class ButtonUI : public UIElement
{
public:
	ButtonUI(double leftX, double rightX, double topY, double bottomY);
	~ButtonUI();

protected:
	virtual void WasClicked(float x, float y) override;
};