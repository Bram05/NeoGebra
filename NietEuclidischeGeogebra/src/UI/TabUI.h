#pragma once

#include "UIElement.h"
#include "PermaButtonUI.h"

class TabUI : public UIElement
{
public:
	TabUI(float leftX, float rightX, float topY, float bottomY, void(*callback)(void*,int), void* obj);
	~TabUI();

	void ButtonClicked(int value);

private:
	std::vector<std::shared_ptr<PermaButtonUI>> m_Buttons;
	void(*m_Callback)(void*, int);
	void* m_Obj;
};