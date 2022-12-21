// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "EquationUI.h"

#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "KeyboardUI.h"
EquationUI::EquationUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI")//, text(500, 500, "red")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	m_SubUIElements.push_back(std::make_shared<ButtonUI>(leftX + 0.2f, (leftX + 0.4f), topY - 0.5f, (topY - 1.0f)));
	m_SubUIElements.push_back(std::make_shared<TextInputField>(leftX, rightX, topY, topY - 0.2f));
	m_SubUIElements.push_back(std::make_shared<KeyboardUI>(leftX, rightX, topY-0.2f, topY-0.4f));
	//m_Texts.push_back(std::make_shared<Text>("ABCDEFGHIJKLMNOPQRSTUVWXYZ", -1.0f, 0.0f, 0.5f, 72));
	//m_Texts.push_back(std::make_shared<Text>("abcdefghijklmnopqrstuvwxyz123456789", -1.0f, 0.0f, -0.5f, 100));
	//m_Texts.push_back(std::make_shared<Text>(std::vector<int>{8704, 8707}, -1.0f, 0.0f, 0.0f, 72));
	//m_Lines.push_back(std::make_shared<Line>(Point(-1.0f, 0.5f), Point(0.0f, 0.5f)));
}

EquationUI::~EquationUI()
{
}

void EquationUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	for (std::shared_ptr<Text>& text : m_Texts)
	{
		r->AddToRenderQueue(text);
	}
	UIElement::RenderPass(r);
}


