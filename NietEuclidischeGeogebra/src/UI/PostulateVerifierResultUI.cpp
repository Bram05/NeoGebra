#include "PostulateVerifierResultUI.h"

#include "Application.h"

PostulateVerifierResultUI::PostulateVerifierResultUI(double topLeftX, double topLeftY, double bottomRightX, double bottomRightY)
	: UIElement(topLeftX, topLeftY, bottomRightX, bottomRightY)
{
	m_Lines.push_back(std::make_shared<Line>(Point(topLeftX, topLeftY), Point(topLeftX, bottomRightY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(topLeftX, topLeftY), Point(bottomRightX, topLeftY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(bottomRightX, bottomRightY), Point(bottomRightX, topLeftY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(bottomRightX, bottomRightY), Point(topLeftX, bottomRightY))); // bottom
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
	for (const std::shared_ptr<Line>& l : m_Lines)
	{
		r->Render(l);
	}
}
