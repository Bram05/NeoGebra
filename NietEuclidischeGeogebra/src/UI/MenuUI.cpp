// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "MenuUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "TextRenderer.h"

int value = 0;

void TestFunction2(int x, int y) {
	std::cout << "TestFunction2 has been executed, values: " << x << ", " << y << "\n";
	value+= y;
	std::cout << "Value added by 1, new value " << value << "\n";
	
}
void TestFunction3(int x, int y) {
	std::cout << "TestFunction2 has been executed, values: " << x << ", " << y << "\n";
	value-=y;
	std::cout << "Value extracted by 1, new value " << value << "\n";
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
	 
	std::vector<void(*)(int, int)> functions = {&TestFunction2,&TestFunction3 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 ,&TestFunction2 };//wtf is deze syntax
	std::vector<std::string> textList = {"Add", "Min", "Add", "Add", "Add", "Add","Add","Add", "Add", "Add", "Add","Add","Add"};
	for (int i=0; i < 12; i++) {
	 	m_SubUIElements.push_back(std::make_shared<ButtonUI>(leftX+ indent +i* buttonWidth, (leftX + i * buttonWidth + buttonWidth), topY-0.01, (topY - 0.09f), functions[i], textList[i]));
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
	m_Texts.push_back(std::make_shared<Text>(std::to_string(value), -1 + 1.6, 1, 0.5f, 144));
	for (std::shared_ptr<Text>& text: m_Texts)
	{
		r->AddToRenderQueue(text);
		m_Texts.erase(m_Texts.begin()+0);
	}

	UIElement::RenderPass(r);
}