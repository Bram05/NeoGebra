#include "ButtonUI.h"

#include "Renderer.h"

ButtonUI::ButtonUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "ButtonUI")
{
}

ButtonUI::~ButtonUI()
{
}

void ButtonUI::WasClicked(float x, float y)
{
	std::cout << "Button clicked!" << '\n';
}