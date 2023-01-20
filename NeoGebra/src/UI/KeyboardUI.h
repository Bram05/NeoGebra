// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "Maths/Equation.h"

// Represents what will eventually be the part where equations can be written
class KeyboardUI : public UIElement
{
public:
	KeyboardUI(double leftX, double rightX, double topY, double bottomY);
	~KeyboardUI();
	void LoadTab(int i);
	
private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::vector<std::shared_ptr<Text>> m_Texts; 

	int m_Tab = 2;//Controls what page will be displayed

	
	//TextC text;
protected:
	void RenderPass(Renderer* r) override;
	
};