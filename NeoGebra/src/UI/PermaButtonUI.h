// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/SquareRenderer.h"
#include "Rendering/TextRenderer.h"

class TabUI;

// A button that will stay on permanently after it is clicked, unless it is deactivated from code
// This is meant for TabUI
class PermaButtonUI : public UIElement
{
public:
	PermaButtonUI(float leftX, float rightX, float topY, float bottomY, int value, TabUI* parent, const std::string& text);
	~PermaButtonUI();

	void SetActivation(bool value);
	virtual void RenderPass(Renderer* r);

protected:
	virtual void WasClicked(float x, float y) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;

private:
	std::shared_ptr<Square> m_Background;
	std::shared_ptr<Text> m_Text;
	bool m_IsActivated{false};
	int m_Value;
	TabUI* m_Parent;
};