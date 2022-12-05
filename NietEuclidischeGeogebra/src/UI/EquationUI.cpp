// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "EquationUI.h"

#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "TextRenderer.h"

EquationUI::EquationUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI"), text(500, 500, "red")
{

	m_SubUIElements.push_back(std::make_shared<ButtonUI>(leftX+0.2f, (leftX + 0.4f), topY-0.5f, (topY - 1.0f)));
	m_SubUIElements.push_back(std::make_shared<TextInputField>(leftX, rightX, topY, topY - 0.2f));
	text.createMessage("Roses are red, violets are blue", 200,200,18);
	
}

EquationUI::~EquationUI()
{
}

void EquationUI::RenderPass(Renderer* r)
{
	text.drawMessage(0);
	UIElement::RenderPass(r);
}

