#pragma once

#include "UIElement.h"
#include "SquareRenderer.h"
#include "TextRenderer.h"

class TabUI;

class PermaButtonUI : public UIElement
{
public:
	PermaButtonUI(float leftX, float rightX, float topY, float bottomY, int value, TabUI* parent, const std::string& text);
	~PermaButtonUI();

	void SetActivation(bool value);
	virtual void RenderPass(Renderer* r);

protected:
	virtual void WasClicked(float x, float y) override;

private:
	std::shared_ptr<Square> m_Background;
	std::shared_ptr<Text> m_Text;
	bool m_IsActivated{false};
	int m_Value;
	TabUI* m_Parent;
};