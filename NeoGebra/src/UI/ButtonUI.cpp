// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ButtonUI.h"
#include "Rendering/Renderer.h"
#include "Application.h"
#include "Util.h"

ButtonUI::ButtonUI(float leftX, float rightX, float topY, float bottomY, void(*func)(void*), void* obj, const std::string& text, const std::array<float, 4>& backgroundColour, const std::array<float, 4>& hoveredColour)
	: ButtonUI(leftX, rightX, topY, bottomY, func, obj, AdvancedString(text), backgroundColour, hoveredColour) {}

ButtonUI::ButtonUI(float leftX, float rightX, float topY, float bottomY, void(*func)(void*), void* obj, const AdvancedString& text, const std::array<float, 4>& backgroundColour, const std::array<float, 4>& hoveredColour)
	: UIElement(leftX, rightX, topY, bottomY, "ButtonUI"),
	m_Background(std::make_shared<Square>(leftX, rightX, topY, bottomY, backgroundColour)),
	m_Obj(obj),
	m_NormalBackgroundColour(backgroundColour),
	m_HoveredBackgroundColour(hoveredColour)
{
	m_Action = func;
	m_Texts.push_back(std::make_shared<Text>(text, leftX + 0.005f, rightX, bottomY + 0.04f, 36.0f));
}

ButtonUI::~ButtonUI()
{
}

void ButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
	for (std::shared_ptr<Text>& text : m_Texts)
	{
		r->AddToRenderQueue(text);
	}
	UIElement::RenderPass(r);
}

void ButtonUI::WasClicked(float x, float y)
{
	UserInput(if (m_Action) { m_Action(m_Obj); });
}

void ButtonUI::IsHovered(float x, float y)
{
	m_Background->m_Colour = m_HoveredBackgroundColour;
}

void ButtonUI::NotHoveredAnymore()
{
	m_Background->m_Colour = m_NormalBackgroundColour;
}
