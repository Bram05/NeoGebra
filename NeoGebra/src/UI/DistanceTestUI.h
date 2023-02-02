#pragma once

#include "UIElement.h"
#include "Rendering/TextRenderer.h"
#include "TextInputField.h"

class DistanceTestUI : public UIElement
{
public:
	DistanceTestUI(float left, float right, float top, float bottom, void(*enterCallback)(void*), void* obj);
	virtual ~DistanceTestUI() {}

	void SetDistance(float d);
	void RemoveDistance();
	const AdvancedString& GetText() const { return ((TextInputField*)m_SubUIElements[0].element.get())->GetText(); }

protected:
	virtual void RenderPass(Renderer* r) override;

private:
	std::shared_ptr<Text> m_Text;
};