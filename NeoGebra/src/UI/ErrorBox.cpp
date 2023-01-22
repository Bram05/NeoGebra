// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ErrorBox.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"


ErrorBox::ErrorBox(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")//, text(500, 500, "red")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
	
	m_ErrorText = std::make_shared<Text>("", m_LeftX+0.01f, m_RightX-0.01f, m_BottomY + 0.43f, 35.0f);// Init empty object

}


void ErrorBox::updateError(std::string text) {
	
	m_ErrorText->RemoveText(0, m_ErrorText->GetText().size());
	m_ErrorText->AddText(text, 0);
}

ErrorBox::~ErrorBox()
{
}

void ErrorBox::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_ErrorText);
	
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}

	UIElement::RenderPass(r);
}