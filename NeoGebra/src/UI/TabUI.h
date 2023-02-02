// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "PermaButtonUI.h"

// A set of three permaButtons
// This is used for the three buttons: point, line, model
// A clicked button will stay on, until one of the others is clicked
class TabUI : public UIElement
{
public:
	TabUI(float leftX, float rightX, float topY, float bottomY, int startingButton, void(*callback)(void*,int), void* obj, const std::vector<AdvancedString>& texts);
	~TabUI();

	void ButtonClicked(int value);

private:
	std::vector<std::shared_ptr<PermaButtonUI>> m_Buttons;
	void(*m_Callback)(void*, int);
	void* m_Obj;
};