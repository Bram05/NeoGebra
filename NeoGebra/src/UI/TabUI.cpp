// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "TabUI.h"

TabUI::TabUI(float leftX, float rightX, float topY, float bottomY, int startingButton, void(*callback)(void*, int), void* obj, const std::vector<AdvancedString>& texts)
	: UIElement(leftX, rightX, topY, bottomY, "TabUI"), m_Callback{ callback }, m_Obj{ obj }
{
	const float padding{ 0.02f };
	unsigned int numButtons = texts.size();
	float width{ rightX - leftX - (numButtons - 1) * padding - 4 * padding };
	width /= numButtons;
	for (int i = 0; i < numButtons; i++)
	{
		m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + (2 + i) * padding + i * width, leftX + (2 + i) * padding + (i + 1) * width, topY, bottomY, i, this, texts[i]));
	}

	for (const std::shared_ptr<PermaButtonUI>& button : m_Buttons)
		m_SubUIElements.emplace_back(button);

	m_Buttons[startingButton]->SetActivation(true);
}

TabUI::~TabUI()
{
}

void TabUI::ButtonClicked(int value)
{
	for (int i{ 0 }; i < m_Buttons.size(); ++i)
	{
		if (i == value)
			continue;
		m_Buttons[i]->SetActivation(false);
	}
	m_Callback(m_Obj, value);
}
