// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "PostulateVerifierResultUI.h"

#include "Application.h"

PostulateVerifierResultUI::PostulateVerifierResultUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateVerifierResultUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
	m_Lines.push_back(std::make_shared<Line>(Point(leftX+0.1f, bottomY+0.1f), Point(rightX-0.1f, topY-0.1f), std::array<float,4>{1.0f, 1.0f, 0.0f, 1.0f}, 0.05f));
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	UIElement::RenderPass(r);
}
