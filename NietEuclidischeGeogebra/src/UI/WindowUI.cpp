// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "WindowUI.h"

#include "PostulateVerifierResultUI.h"
#include "EquationUI.h"

WindowUI::WindowUI()
{
	m_UIElements.push_back(std::make_shared<EquationUI>(-1.0f, -0.5f, 1.0f, -1.0f));
	m_UIElements.push_back(std::make_shared<PostulateVerifierResultUI>(0.5f, 1.0f, 1.0f, -1.0f));
}

WindowUI::~WindowUI()
{
}

void WindowUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<UIElement> element : m_UIElements)
	{
		element->RenderPass(r);
	}
}

std::shared_ptr<UIElement> WindowUI::MouseClicked(float x, float y)
{
	for (std::shared_ptr<UIElement>& element : m_UIElements)
	{
		std::shared_ptr<UIElement> el = Hit(element, x, y);
		if (el)
		{
			el->WasClicked(x, y);
			return el;
		}
	}
	return nullptr;
}

std::shared_ptr<UIElement> WindowUI::MouseMoved(float x, float y)
{
	for (std::shared_ptr<UIElement>& element : m_UIElements)
	{
		std::shared_ptr<UIElement> el = Hit(element, x, y);
		if (el)
		{
			if (!el->m_MouseIsHovering)
			{
				el->IsHovered(x, y);
				el->m_MouseIsHovering = true;
				if (m_CurrentlyHoveredElement)
				{
					m_CurrentlyHoveredElement->NotHoveredAnymore();
					m_CurrentlyHoveredElement->m_MouseIsHovering = false;
				}
				m_CurrentlyHoveredElement = el;
			}
			return el;
		}
	}
	if (m_CurrentlyHoveredElement)
	{
		m_CurrentlyHoveredElement->NotHoveredAnymore();
		m_CurrentlyHoveredElement->m_MouseIsHovering = false;
		m_CurrentlyHoveredElement = nullptr;
	}
	return nullptr;
}

std::shared_ptr<UIElement> WindowUI::Hit(const std::shared_ptr<UIElement>& element, float x, float y)
{
	if (x > element->m_LeftX && x < element->m_RightX && y > element->m_BottomY && y < element->m_TopY)
	{
		for (const std::shared_ptr<UIElement>& element : element->m_SubUIElements)
		{
			std::shared_ptr<UIElement> res = Hit(element, x, y);
			if (res)
			{
				return res;
			}
		}
		return element;
	}
	return nullptr;
}
