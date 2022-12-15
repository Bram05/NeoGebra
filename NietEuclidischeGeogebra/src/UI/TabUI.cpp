#include "TabUI.h"

#include <typeinfo>

TabUI::TabUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "TabUI")
{
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 0.1f, leftX + 0.3f, topY - 0.1f, topY - 0.2f, 0, this));
	m_Buttons.push_back(std::make_shared<PermaButtonUI>(leftX + 0.35f, leftX + 0.5f, topY - 0.1f, topY - 0.2f, 1, this));

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
