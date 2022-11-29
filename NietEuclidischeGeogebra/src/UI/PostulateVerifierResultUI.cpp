#include "PostulateVerifierResultUI.h"

#include "Application.h"

PostulateVerifierResultUI::PostulateVerifierResultUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateVerifierResultUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
	for (const std::shared_ptr<Line>& l : m_Lines)
	{
		r->AddToRenderQueue(l);
	}
}
