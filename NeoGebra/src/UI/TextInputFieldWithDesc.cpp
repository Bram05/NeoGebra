// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "TextInputFieldWithDesc.h"

TextInputFieldWithDesc::TextInputFieldWithDesc(float leftX, float rightX, float topY, float bottomY, const AdvancedString& text, float width, void(*enterCallback)(void*), void* obj, float textSize, const AdvancedString& defaultText)
	: UIElement(leftX, rightX, topY, bottomY, "TextInputFieldWithDesc"), m_Text(std::make_shared<Text>(text, leftX + 0.01f, leftX + width - 0.01f, bottomY + 0.037f, textSize))
{
	m_SubUIElements.push_back({ std::make_shared<TextInputField>(leftX + width, rightX - 0.006f, topY, bottomY, enterCallback, obj, defaultText), true });
}

TextInputFieldWithDesc::~TextInputFieldWithDesc()
{
}

void TextInputFieldWithDesc::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}
