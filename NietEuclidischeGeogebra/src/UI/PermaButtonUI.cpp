#include "PermaButtonUI.h"

#include "Renderer.h"
#include "TabUI.h"

PermaButtonUI::PermaButtonUI(float leftX, float rightX, float topY, float bottomY, int value, TabUI* parent, const std::string& text)
	: UIElement(leftX, rightX, topY, bottomY, "PermaButton"),
	m_Background(std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array<float, 4>{0.0f, 1.0f, 1.0f, 1.0f})),
	m_Value(value),
	m_Parent(parent),
	m_Text(std::make_shared<Text>(text, leftX + 0.02f, rightX - 0.02f, bottomY + 0.02f, 30))
{
}

PermaButtonUI::~PermaButtonUI()
{
}

void PermaButtonUI::SetActivation(bool value)
{
	m_IsActivated = value;
	if (m_IsActivated)
	{
		m_Background->m_Colour = { 0.5f, 0.5f, 0.5f, 1.0f };
	}
	else
	{
		m_Background->m_Colour = { 0.0f, 1.0f, 1.0f, 1.0f };
	}
}

void PermaButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}

void PermaButtonUI::WasClicked(float x, float y)
{
	if (m_IsActivated)
		return;
	SetActivation(true);
	m_Parent->ButtonClicked(m_Value);
}

void PermaButtonUI::IsHovered(float x, float y)
{
	if (!m_IsActivated)
		m_Background->m_Colour = { 0.0f, 0.8f, 0.8f, 1.0f };
}

void PermaButtonUI::NotHoveredAnymore()
{
	if (!m_IsActivated)
		m_Background->m_Colour = { 0.0f, 1.0f, 1.0f, 1.0f };
}
