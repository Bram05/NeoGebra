// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "Maths/Equation.h"

// The keyboard of mathematical symbols at the bottom of the screen
class KeyboardUI : public UIElement
{
public:
	KeyboardUI(float leftX, float rightX, float topY, float bottomY);
	~KeyboardUI();
	
private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::vector<std::shared_ptr<Text>> m_Texts; 

protected:
	void RenderPass(Renderer* r) override;
	
};