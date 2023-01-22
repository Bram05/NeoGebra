// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "WindowUI.h"

#include "PostulateVerifierResultUI.h"
#include "EquationUI.h"
#include "ButtonUI.h"
#include "GraphUI.h"
#include "MenuUI.h"
#include "TabUI.h"
#include "ErrorBox.h"


void tabTest(void* obj, int x) {
		std::cout << x <<  "\n";
}

WindowUI::WindowUI()
{
	m_UIElements.push_back(std::make_shared<EquationUI>(-1.0f, -0.5f, 0.9f, -1.0f));
	m_UIElements.push_back(std::make_shared<PostulateVerifierResultUI>(0.5f, 1.0f, 0.9f, -0.5f));
	m_UIElements.push_back(std::make_shared<ErrorBox>(0.5f, 1.0f, -0.5f, -1.0f));
	m_UIElements.push_back(std::make_shared<GraphUI>(-0.5f, 0.5f, 0.9f, -1.0f));
	m_GraphUIIndex = m_UIElements.size() - 1;
	m_UIElements.push_back(std::make_shared<MenuUI>(-1.0f, 1.0f, 1.0f, 0.9f));
}

void WindowUI::AddError(std::string error) {
	(*(std::shared_ptr<ErrorBox>*)&m_UIElements[2])->updateError(error);
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
	m_MouseDown = true;
	for (std::shared_ptr<UIElement>& element : m_UIElements)
	{
		std::shared_ptr<UIElement> el = Hit(element, x, y);
		if (el)
		{
			el->WasClicked(x, y);
			if (!el->m_IsSelected && el->GetName() != "ButtonUI")
			{
				if (m_SelectedElement)
				{
					m_SelectedElement->NotSelectedAnymore();
					m_SelectedElement->m_IsSelected = false;
				}
				el->IsSelected();
				el->m_IsSelected = true;
				el->m_IsBeingDragged = true;
				m_SelectedElement = el;
			}
			return el;
		}
	}
	if (m_SelectedElement)
	{
		m_SelectedElement->NotSelectedAnymore();
		m_SelectedElement->m_IsSelected = false;
		m_SelectedElement = nullptr;
	}
	return nullptr;
}

void WindowUI::MouseReleased()
{
	m_MouseDown = false;
	if (m_SelectedElement != nullptr) {
		m_SelectedElement->m_IsBeingDragged = false;
	}
}

std::shared_ptr<UIElement> WindowUI::MouseMoved(float x, float y)
{	
	if (m_MouseDown && m_SelectedElement != nullptr) {
		m_SelectedElement->DraggedUpdate(x, y);
	}

	for (std::shared_ptr<UIElement>& element : m_UIElements)
	{
		std::shared_ptr<UIElement> el = Hit(element, x, y);
		if (el)
		{
			if (!el->m_MouseIsHovering)
			{
				if (m_CurrentlyHoveredElement)
				{
					m_CurrentlyHoveredElement->NotHoveredAnymore();
					m_CurrentlyHoveredElement->m_MouseIsHovering = false;
				}
				el->IsHovered(x, y);
				el->m_MouseIsHovering = true;
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

void WindowUI::TextInput(unsigned int codepoint)
{
	if (m_SelectedElement)
	{
		m_SelectedElement->TextInput(codepoint);
	}
}

void WindowUI::SpecialKeyInput(int key, int scancode, int action, int mods)
{
	if (m_SelectedElement)
	{
		m_SelectedElement->SpecialKeyInput(key, scancode, action, mods);
	}
}

void WindowUI::ResizeWindow(int width, int height)
{
	for (std::shared_ptr<UIElement>& el : m_UIElements)
	{
		el->ResizeWindow(width, height);
	}
}

void WindowUI::UpdateGraphUI()
{
	for (std::shared_ptr<UIElement>& el : m_UIElements)
	{
		el->UpdateGraphUI();
	}
}

GraphUI* WindowUI::GetGraphUI()
{
	return (GraphUI*)m_UIElements[m_GraphUIIndex].get();
}

void WindowUI::InsertKey(int codepoint)
{
	if (m_SelectedElement)
		m_SelectedElement->TextInput(codepoint);
}

std::shared_ptr<UIElement> WindowUI::Hit(const std::shared_ptr<UIElement>& element, float x, float y)
{
	if (x > element->m_LeftX && x < element->m_RightX && y > element->m_BottomY && y < element->m_TopY)
	{
		for (const SubUIElement& nextElement : element->m_SubUIElements)
		{
			if (!nextElement.shouldRender)
				continue;
			std::shared_ptr<UIElement> res = Hit(nextElement.element, x, y);
			if (res)
			{
				return res;
			}
		}
		return element;
	}
	return nullptr;
}
