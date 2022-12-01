#pragma once

#include "UIElement.h"
#include "LineRenderer.h"

class PostulateVerifierResultUI : public UIElement
{
public:
	PostulateVerifierResultUI(double leftX, double rightX, double topY, double bottomY);
	~PostulateVerifierResultUI();
};