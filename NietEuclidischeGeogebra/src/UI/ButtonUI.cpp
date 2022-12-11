#include "ButtonUI.h"

#include "Renderer.h"

#include "Application.h"

ButtonUI::ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(int, int))
	: UIElement(leftX, rightX, topY, bottomY, "ButtonUI"),
	  m_Background(std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array{0.0f, 0.6f, 1.0f, 1.0f}))
{
	m_Action = func;
}

ButtonUI::~ButtonUI()
{
}

void ButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
}

void ButtonUI::WasClicked(float x, float y)
{

	if (m_Action != nullptr) {
		m_Action(1,2);
	}
	else {
		std::cout << "niks" << "\n";
	}
	
}

void ButtonUI::IsHovered(float x, float y)
{
	m_Background->m_Colour = { 0.0f, 0.0f, 0.0f, 1.0f };
}

void ButtonUI::NotHoveredAnymore()
{
	m_Background->m_Colour = { 1.0f, 1.0f, 0.0f, 1.0f };
}
