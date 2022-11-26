#include "WindowUI.h"

WindowUI::WindowUI()
{
	m_UIElements.push_back(std::make_shared<EquationUI>(-1.0f, 1.0f, -0.5f, 0.0f));
}

WindowUI::~WindowUI()
{
}

void WindowUI::RenderPass()
{
	for (std::shared_ptr<UIElement> element : m_UIElements)
	{
		element->RenderPass();
	}
}