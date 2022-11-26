#pragma once

#include "EquationUI.h"
#include "UIElement.h"

class WindowUI
{
public:
	WindowUI();
	~WindowUI();

	void RenderPass();

private:
	std::vector<std::shared_ptr<UIElement>> m_UIElements;
};