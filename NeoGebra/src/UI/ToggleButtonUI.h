// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"

#include "Rendering/SquareRenderer.h"

// A button that can be toggle to change some setting
class ToggleButtonUI : public UIElement
{
public:
	ToggleButtonUI(float leftX, float rightX, float topY, float bottomY, bool defaultValue, void(*callback)(void*,bool) = nullptr, void* obj = nullptr);
	virtual ~ToggleButtonUI();

	virtual void RenderPass(Renderer* r) override;
	virtual void IsHovered(float x, float y) override;
	virtual void NotHoveredAnymore() override;
	virtual void WasClicked(float x, float y) override;

private:
	std::shared_ptr<Square> m_Background;
	void(*m_Callback)(void*,bool);
	void* m_Obj;
	bool m_IsOn;
};