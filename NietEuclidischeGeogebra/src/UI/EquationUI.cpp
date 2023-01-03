// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "PostulateVerifier/PostulateVerifier.h"

#include "EquationUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "KeyboardUI.h"
#include "TabUI.h"

static void ButtonClickedCallback(void* obj, int value)
{
	((EquationUI*)obj)->ButtonClicked(value);
}

static void UpdateGraphs(void* obj)
{
	((EquationUI*)obj)->UpdateGraphsFromInput();
}

EquationUI::EquationUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	//m_SubUIElements.push_back({std::make_shared<ButtonUI>(leftX + 0.2f, (leftX + 0.4f), topY - 0.5f, (topY - 1.0f))});
	m_SubUIElements.push_back({ std::make_shared<TextInputField>(leftX, rightX, topY - 0.2f, topY - 0.4f) });
	m_TextInputField1Index = m_SubUIElements.size() - 1;
	m_SubUIElements.push_back({ std::make_shared<TextInputField>(leftX, rightX, topY - 0.4f, topY - 0.6f) });
	m_TextInputField2Index = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<KeyboardUI>(leftX, rightX, bottomY + 0.25f, bottomY));
	m_SubUIElements.emplace_back(std::make_shared<TabUI>(leftX, rightX, topY, topY - 0.2f, 0, &ButtonClickedCallback, this));
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.4f, bottomY + 0.3f, UpdateGraphs, this, "Update graphs"));
	//m_Texts.push_back(std::make_shared<Text>("ABCDEFGHIJKLMNOPQRSTUVWXYZ", -1.0f, 0.0f, 0.5f, 72));
	//m_Texts.push_back(std::make_shared<Text>("abcdefghijklmnopqrstuvwxyz123456789", -1.0f, 0.0f, -0.5f, 100));
	//m_Texts.push_back(std::make_shared<Text>(std::vector<int>{8704, 8707}, -1.0f, 0.0f, 0.0f, 72));
	//m_Lines.push_back(std::make_shared<Line>(Point(-1.0f, 0.5f), Point(0.0f, 0.5f)));
}

EquationUI::~EquationUI()
{
}

void EquationUI::ButtonClicked(int value)
{
	m_SubUIElements[m_TextInputField1Index].shouldRender = value == 0;
	m_SubUIElements[m_TextInputField2Index].shouldRender = value == 0;
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

void EquationUI::UpdateGraphsFromInput()
{
	const std::vector<std::pair<int, float>>& text1{ ((TextInputField*)(m_SubUIElements[m_TextInputField1Index].element.get()))->GetText() };
	const std::vector<std::pair<int, float>>& text2{ ((TextInputField*)(m_SubUIElements[m_TextInputField2Index].element.get()))->GetText() };

	std::string t1;
	for (auto [v, f] : text1)
		t1.push_back(v);
	std::string t2;
	for (auto [v, f] : text2)
		t2.push_back(v);

	new NELine({ std::stof(t1), std::stof(t2)}, Application::Get()->GetModelManager()->GetModel(), {255, 255, 0, 255}, false);
	Application::Get()->GetWindowUI()->UpdateGraphUI();
}
