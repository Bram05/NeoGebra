#pragma once

#include "UIElement.h"
#include "SquareRenderer.h"
#include "TextRenderer.h"

class ButtonUI : public UIElement
{
public:
	ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(int,int) = nullptr, std::string text = "Null");
	~ButtonUI();
	
	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void WasClicked(float x, float y) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;
private:
	std::shared_ptr<Square> m_Background;
	std::vector<std::shared_ptr<Text>> m_Texts;
	std::string m_Text;
	void(*m_Action)(int, int);
};