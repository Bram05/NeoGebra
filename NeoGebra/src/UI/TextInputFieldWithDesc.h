// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"

// A text input field with a leading description before it
class TextInputFieldWithDesc : public UIElement
{
public:
	TextInputFieldWithDesc(float leftX, float rightX, float topY, float bottomY, const AdvancedString& text, float width, void(*enterCallback)(void*) = nullptr, void* obj = nullptr, float textSize = 43.0f, const AdvancedString& defaultText = AdvancedString(""));
	~TextInputFieldWithDesc();

	const AdvancedString& GetText() const { return ((TextInputField*)m_SubUIElements[0].element.get())->GetText(); }
	void SetText(const AdvancedString& text) { ((TextInputField*)m_SubUIElements[0].element.get())->SetText(text); }
protected:
	virtual void RenderPass(Renderer* r);

private:
	std::shared_ptr<Text> m_Text;
};