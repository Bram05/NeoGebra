#pragma once

#include "TestUI.h"
#include "TextInputField.h"
#include "Rendering/Renderer.h"

TestUI::TestUI(float left, float right, float top, float bottom, void(*enterCallback)(void*), void* obj)
	: UIElement(left, right, top, bottom, "TestUI")
{
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(left, right - 0.1f, top, bottom, enterCallback, obj));
	m_Text = std::make_shared<Text>(AdvancedString("= "), right - 0.09f, right, bottom + 0.02f, 35.0f);
}

void TestUI::SetOutput(const AdvancedString& output)
{
	m_Text->SetText(AdvancedString("= ") + output);
}

void TestUI::RemoveOutput()
{
	m_Text->SetText(AdvancedString("="));
}

void TestUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}
