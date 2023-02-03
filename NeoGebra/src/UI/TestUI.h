#pragma once

#include "UIElement.h"
#include "Rendering/TextRenderer.h"
#include "TextInputField.h"

class TestUI : public UIElement
{
public:
	TestUI(float left, float right, float top, float bottom, void(*enterCallback)(void*), void* obj);
	virtual ~TestUI() {}

	void SetOutput(const AdvancedString& output);
	void RemoveOutput();
	const AdvancedString& GetText() const { return ((TextInputField*)m_SubUIElements[0].element.get())->GetText(); }

protected:
	virtual void RenderPass(Renderer* r) override;

private:
	std::shared_ptr<Text> m_Text;
};