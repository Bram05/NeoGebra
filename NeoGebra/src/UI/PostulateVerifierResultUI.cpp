// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "PostulateVerifierResultUI.h"

#include "Application.h"

static void CheckPostulates(void* obj)
{
	((PostulateVerifierResultUI*)obj)->VerifyPostulates();
}

PostulateVerifierResultUI::PostulateVerifierResultUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateVerifierResultUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.04f, rightX - 0.04f, topY - 0.05f, topY - 0.25f, CheckPostulates, this, "Verify Posulates"));
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::VerifyPostulates()
{
	// Jeroen
	std::cout << "Doing stuff\n";
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	UIElement::RenderPass(r);
}
