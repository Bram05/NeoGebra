#pragma once

#include "UIElement.h"
#include "TextInputField.h"
#include "TextRenderer.h"

class TextInputFieldWithDesc : public UIElement
{
public:
	TextInputFieldWithDesc(float leftX, float rightX, float topY, float bottomY, const std::string& text, float width, void(*enterCallback)(void*) = nullptr, void* obj = nullptr);
	~TextInputFieldWithDesc();

	const AdvancedString& GetText() const { return ((TextInputField*)m_SubUIElements[0].element.get())->GetText(); }
protected:
	virtual void RenderPass(Renderer* r);

private:
	std::shared_ptr<Text> m_Text;
};