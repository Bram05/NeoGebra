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
	
	float buttonWidth = 0.1f;
	float indent = 0.01f;
	float buttonHeight = 0.085f;
	int element = 0;
	for (int y = 0; y < 2; y++) {
		for (int i = 0; i < 4; i++) {
			try{
				m_SubUIElements.push_back(std::make_shared<ButtonUI>(c_leftX + indent + i * buttonWidth, (c_leftX + i * buttonWidth + buttonWidth), c_topY - 2 * indent - buttonHeight * y, (c_topY - indent - buttonHeight - buttonHeight * y), functions[element + m_Tab * 8], textList[element + m_Tab * 8]));
				element++;
			}
			catch (const std::exception& e) {
				std::cout << "error";
			}
			
		}
	}
	


	UIElement::RenderPass(r);
}