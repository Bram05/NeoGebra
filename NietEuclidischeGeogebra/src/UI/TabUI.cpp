#include "TabUI.h"

#include <typeinfo>

constexpr int numButtons{ 2 };
TabUI::TabUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "TabUI")
{
	const float padding{ 0.06f };
	float width{ rightX - 2 * 0.06f - leftX };
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 0.06f, (rightX + leftX) / 2 - 0.5 * padding, topY - 0.05f, std::max(topY - 0.3f, bottomY + 0.05f), 0, this));
	m_Buttons.push_back(std::make_shared<PermaButtonUI>((rightX + leftX) / 2 + 0.5 * padding, rightX - 0.06f, topY - 0.05f, std::max(topY - 0.3f, bottomY + 0.05f), 1, this));

	for (const std::shared_ptr<PermaButtonUI>& button : m_Buttons)
		m_SubUIElements.push_back(button);
}

TabUI::~TabUI()
{
}

void TabUI::RenderPass(Renderer* r)
{
	UIElement::RenderPass(r);
}

void TabUI::ButtonClicked(int value)
{
	for (int i{ 0 }; i < m_Buttons.size(); ++i)
	{
		if (i == value)
			continue;
		m_Buttons[i]->SetActivation(false);
	}
}
