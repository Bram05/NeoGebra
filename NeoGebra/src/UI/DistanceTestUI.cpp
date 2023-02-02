#pragma once

#include "DistanceTestUI.h"
#include "TextInputField.h"
#include "Rendering/Renderer.h"

DistanceTestUI::DistanceTestUI(float left, float right, float top, float bottom, void(*enterCallback)(void*), void* obj)
	: UIElement(left, right, top, bottom, "DistanceTestUI")
{
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(left, right - 0.1f, top, bottom, enterCallback, obj));
	m_Text = std::make_shared<Text>(AdvancedString("= "), right - 0.09f, right, bottom + 0.02f, 35.0f);
}

void DistanceTestUI::SetDistance(float d)
{
	m_Text->SetText(AdvancedString("=") + std::to_string(d));
}

void DistanceTestUI::RemoveDistance()
{
	m_Text->SetText(AdvancedString("="));
}

void DistanceTestUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}
