// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "MenuUI.h"

#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "TextRenderer.h"

void TestFunction2(int x, int y) {
	std::cout << "TestFunction2 has been executed, values: " << x << ", " << y << "\n";
}

MenuUI::MenuUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")//, text(500, 500, "red")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	//width = 0.125
	// distance = 0.025
	float buttonWidth = 0.125f;
	float indent = 0.025f;
	std::vector<void(*)(int, int)> functions;//wtf is deze syntax
	std::vector<std::string> textList = { "File", "Open", "Edit", "View", "Hi", "Among","Us","Riad", "Bram", "Jer", "Ome","Yo","Rood" };
	for (int i = 0; i < 12; i++) {
		functions.push_back(&TestFunction2);//voor nu zo, later moeten we natuurlijk elke apart zetten
		m_SubUIElements.push_back(std::make_shared<ButtonUI>(leftX + indent + i * buttonWidth, (leftX + i * buttonWidth + buttonWidth), topY - 0.01, (topY - 0.09f), functions[i], textList[i]));

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
	//text.drawMessage(0);
	UIElement::RenderPass(r);
}