// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ToggleButtonUI.h"

#include "Rendering/Renderer.h"

constexpr std::array<float, 4> offColour = { 0.0f,0.0f,0.0f, 1.0f };
constexpr std::array<float, 4> onColour = { 0.7f,0.7f,0.7f, 1.0f };

ToggleButtonUI::ToggleButtonUI(float leftX, float rightX, float topY, float bottomY, bool defaultValue, const AdvancedString& text, void(*callback)(void*, bool), void* obj)
	: UIElement(leftX, rightX, topY, bottomY, "ToggleButtonUI"), m_Background{ std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array<float,4>{ 0.0f,1.0f,1.0f,1.0f }) },
	m_Callback{ callback }, m_Obj{ obj }, m_IsOn{ defaultValue }, m_Text{ std::make_shared<Text>(text, leftX + 0.01f, rightX, bottomY + 0.03f, 36.0f) }
{
	if (m_IsOn)
	{
		m_Background->m_Colour = onColour;
		m_Text->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Text->SetText("Verify elements");
	}
	else
	{
		m_Background->m_Colour = offColour;
		m_Text->m_Colour = { 1.0f,1.0f,1.0f,1.0f };
		m_Text->SetText("Don't verify elements");
	}
}

ToggleButtonUI::~ToggleButtonUI()
{
}

void ToggleButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}

void ToggleButtonUI::IsHovered(float x, float y)
{
	//m_Background->m_Colour = { 0.5f,0.2f,0.4f, 1.0f };
}

void ToggleButtonUI::NotHoveredAnymore()
{
	/*if (m_IsOn)
		m_Background->m_Colour = { 0.6f,0.6f,0.6f, 1.0f };
	else
		m_Background->m_Colour = { 0.3f,0.3f,0.3f, 1.0f };*/
}

void ToggleButtonUI::WasClicked(float x, float y)
{
	m_IsOn = !m_IsOn;
	if (m_IsOn)
	{
		m_Background->m_Colour = onColour;
		m_Text->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Text->SetText("Verify elements");
	}
	else
	{
		m_Background->m_Colour = offColour;
		m_Text->m_Colour = { 1.0f,1.0f,1.0f,1.0f };
		m_Text->SetText("Don't verify elements");
	}
	m_Callback(m_Obj, m_IsOn);
}
