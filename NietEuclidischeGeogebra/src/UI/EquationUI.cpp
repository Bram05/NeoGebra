// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "EquationUI.h"

#include "Application.h"

EquationUI::EquationUI(double topLeftX, double topLeftY, double bottomRightX, double bottomRightY)
	: UIElement(topLeftX, topLeftY, bottomRightX, bottomRightY)
{
	m_Lines.push_back(std::make_shared<Line>(Point(topLeftX, topLeftY), Point(topLeftX, bottomRightY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(topLeftX, topLeftY), Point(bottomRightX, topLeftY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(bottomRightX, bottomRightY), Point(bottomRightX, topLeftY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(bottomRightX, bottomRightY), Point(topLeftX, bottomRightY))); // bottom
}

EquationUI::~EquationUI()
{
}

void EquationUI::RenderPass()
{
	for (std::shared_ptr<Line>& l : m_Lines)
	{
		Application::Get()->GetRenderer()->Render(l);
	}
}
