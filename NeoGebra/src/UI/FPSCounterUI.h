#pragma once

#include "UIElement.h"
#include "Rendering/TextRenderer.h"

class FPSCounterUI : public UIElement
{
public:
	FPSCounterUI(float leftX, float rightX, float topY, float bottomY);

	void SetCounter(float fps);
	virtual void RenderPass(Renderer* r) override;

private:
	std::shared_ptr<Text> m_Text;
};