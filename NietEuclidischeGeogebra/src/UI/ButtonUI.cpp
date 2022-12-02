#include "ButtonUI.h"

#include "Renderer.h"

#include "Application.h"

ButtonUI::ButtonUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "ButtonUI"),
	  m_Background(std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array{1.0f, 1.0f, 0.0f, 1.0f}))
{
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
	std::cout << "Button clicked! Closing application" << '\n';
	Application::Get()->GetWindow()->SetShouldClose(true);
}

void ButtonUI::IsHovered(float x, float y)
{
	m_Background->m_Colour = { 0.0f, 0.0f, 0.0f, 1.0f };
}

void ButtonUI::NotHoveredAnymore()
{
	m_Background->m_Colour = { 1.0f, 1.0f, 0.0f, 1.0f };
}
