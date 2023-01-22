// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "MenuUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"

void AddPoint(void*) {
	new NEPoint({ 0,  0 }, Application::Get()->GetModel(), { 255,0,0,255 });
	Application::Get()->GetWindowUI()->UpdateGraphUI();
}
void AddLine(void*) {
	new NELine({ -1.25,  0 }, Application::Get()->GetModel());
	Application::Get()->GetWindowUI()->UpdateGraphUI();
}

MenuUI::MenuUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")//, text(500, 500, "red")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	float buttonWidth = 0.125f;
	float indent = 0.025f;

	std::vector<void(*)(void*)> functions = { &AddPoint,&AddLine ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint ,&AddPoint };//wtf is deze syntax
	std::vector<std::string> textList = { "Point", "Line", "Add", "Add", "Add", "Add","Add","Add", "Add", "Add", "Add","Add","Add" };
	for (int i = 0; i < 12; i++) {
		m_SubUIElements.push_back({ std::make_shared<ButtonUI>(leftX + indent + i * buttonWidth, (leftX + i * buttonWidth + buttonWidth), topY - 0.01f, (topY - 0.09f), functions[i], this, textList[i]) });
	}

}

MenuUI::~MenuUI()
{
}

void MenuUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}

	UIElement::RenderPass(r);
}