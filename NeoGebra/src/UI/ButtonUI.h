// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "SquareRenderer.h"
#include "TextRenderer.h"

class ButtonUI : public UIElement
{
public:
	ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(void*), void* obj, const std::string& text);
	ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(void*), void* obj, const AdvancedString& text);
	~ButtonUI();

	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void WasClicked(float x, float y) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;
private:
	std::shared_ptr<Square> m_Background;
	std::vector<std::shared_ptr<Text>> m_Texts;
	void(*m_Action)(void*);
	void* m_Obj;
};