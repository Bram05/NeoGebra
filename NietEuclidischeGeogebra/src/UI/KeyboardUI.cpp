// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "KeyboardUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "TextRenderer.h"

void insertKey(int x, int y) {
	
	std::cout << x << " " << y << "\n";
}

float c_leftX = -1.0f;
float c_topY = 0.5f;
std::vector<void(*)(int, int)> functions = { &insertKey,&insertKey, &insertKey, &insertKey, &insertKey,&insertKey,&insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey, &insertKey };//wtf is deze syntax
std::vector<std::string> textList = { "a", "a", "a", "a", "b","b", "b", "b", "c", "c","c", "c" , "d", "d","d", "d" , "e", "e" , "e" , "e" , "f", "f" , "f" , "f" };



void KeyboardUI::LoadTab(int i) {
	m_Tab = i;
}

KeyboardUI::KeyboardUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "KeyboardUI")//, text(500, 500, "red")
{    
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
	 
	//width = 0.125
	// distance = 0.025
	float buttonWidth = 0.1f;
	float indent = 0.0175f;
	 
	std::vector<void(*)(int, int)> functions = {&insertKey,&insertKey, &insertKey, &insertKey, &insertKey,&insertKey,&insertKey, &insertKey, &insertKey, &insertKey };//wtf is deze syntax
	std::vector<std::string> textList = {"a", "b", "c", "f", "x","(", ")", "d", "e", "g","h", "i" };
	int x = 0;
	for (int i=0; i < 10; i++) {
		if (i <= 4) {
			m_SubUIElements.push_back({std::make_shared<ButtonUI>(leftX + indent + i * buttonWidth, (leftX + i * buttonWidth + buttonWidth), topY - 0.01, (topY - 0.09f), functions[i], textList[i])});
			continue;
		}																																	
		m_SubUIElements.push_back({std::make_shared<ButtonUI>(leftX + indent + x * buttonWidth, (leftX + x * buttonWidth + buttonWidth), topY - 0.01-0.1f, (topY - 0.09f-0.1f), functions[i], textList[i])});
		x++;		
	}
}    

KeyboardUI::~KeyboardUI()
{
}

void KeyboardUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	UIElement::RenderPass(r);
}