#pragma once

#include "UIElement.h"
#include "SquareRenderer.h"

class TabUI;

class PermaButtonUI : public UIElement
{
public:
	PermaButtonUI(float leftX, float rightX, float topY, float bottomY, int value, TabUI* parent);
	~PermaButtonUI();

	void SetActivation(bool value);
	virtual void RenderPass(Renderer* r);

protected:
	virtual void WasClicked(float x, float y) override;

private:
	std::shared_ptr<Square> m_Background;
	bool m_IsActivated{false};
	int m_Value;
	TabUI* m_Parent;
};