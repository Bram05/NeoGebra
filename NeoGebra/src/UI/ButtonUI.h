// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/SquareRenderer.h"
#include "Rendering/TextRenderer.h"

class ButtonUI : public UIElement
{
public:
	ButtonUI(float leftX, float rightX, float topY, float bottomY, void(*func)(void*), void* obj, const std::string& text, const std::array<float, 4>& backgroundColour = { 0.0f,1.0f,1.0f,1.0f }, const std::array<float, 4>& hoveredColour = { 0.5f,0.5f,0.5f, 1.0f });
	ButtonUI(float leftX, float rightX, float topY, float bottomY, void(*func)(void*), void* obj, const AdvancedString& text, const std::array<float, 4>& backgroundColour = { 0.0f,1.0f,1.0f,1.0f }, const std::array<float, 4>& hoveredColour = { 0.5f,0.5f,0.5f, 1.0f });
	~ButtonUI();

	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void WasClicked(float x, float y) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;
private:
	std::shared_ptr<Square> m_Background;
	std::array<float, 4> m_NormalBackgroundColour;
	std::array<float, 4> m_HoveredBackgroundColour;
	std::vector<std::shared_ptr<Text>> m_Texts;
	void(*m_Action)(void*);
	void* m_Obj;
};