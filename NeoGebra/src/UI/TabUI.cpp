// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "TabUI.h"

#include <typeinfo>

constexpr int numButtons{ 2 };
TabUI::TabUI(float leftX, float rightX, float topY, float bottomY, int startingButton, void(*callback)(void*, int), void* obj)
	: UIElement(leftX, rightX, topY, bottomY, "TabUI"), m_Callback{callback}, m_Obj{obj}
{
	const float padding{ 0.02f };
	float width{ rightX - leftX - 2 * (2 * padding) - 2 * padding };
	width /= 3;
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 2 * padding, leftX + 2 * padding + width, topY - 0.05f, std::max(topY - 0.3f, bottomY + 0.05f), 0, this, "Points"));
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 3 * padding + width, leftX + 3 * padding + 2 * width, topY - 0.05f, std::max(topY - 0.3f, bottomY + 0.05f), 1, this, "Lines"));
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 4 * padding + 2 * width, leftX + 4 * padding + 3 * width, topY - 0.05f, std::max(topY - 0.3f, bottomY + 0.05f), 2, this, "Model"));

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
