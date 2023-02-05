// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ToggleButtonUI.h"

#include "Rendering/Renderer.h"

ToggleButtonUI::ToggleButtonUI(float leftX, float rightX, float topY, float bottomY, bool defaultValue, void(*callback)(void*,bool), void* obj)
	: UIElement(leftX, rightX, topY, bottomY, "ToggleButtonUI"), m_Background{ std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array<float,4>{ 0.0f,1.0f,1.0f,1.0f }) },
	m_Callback{ callback }, m_Obj{ obj }, m_IsOn{ defaultValue }
{
	if (m_IsOn)
		m_Background->m_Colour = { 0.5f,0.5f,0.5f, 1.0f };
	else
		m_Background->m_Colour = { 0.1f,0.1f,0.1f, 1.0f };
}

ToggleButtonUI::~ToggleButtonUI()
{
}

void ToggleButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
}

void ToggleButtonUI::IsHovered(float x, float y)
{
	m_Background->m_Colour = { 0.5f,0.2f,0.4f, 1.0f };
}

void ToggleButtonUI::NotHoveredAnymore()
{
	if (m_IsOn)
		m_Background->m_Colour = { 0.5f,0.5f,0.5f, 1.0f };
	else
		m_Background->m_Colour = { 0.1f,0.1f,0.1f, 1.0f };
}

void ToggleButtonUI::WasClicked(float x, float y)
{
	m_IsOn != m_IsOn;
	m_Callback(m_Obj, m_IsOn);
}
