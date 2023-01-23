// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "ErrorBox.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"


ErrorBox::ErrorBox(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	m_ErrorText = std::make_shared<Text>("", leftX, rightX, topY - 0.3f, 35.0f, true, std::array<float, 4>{1.0f, 0.0f, 0.0f, 1.0f});
	m_ErrorBoxText = std::make_shared<Text>("Error Box: any errors will be displayed in here.", m_LeftX + 0.01f, m_RightX - 0.01f, m_BottomY + 0.43f, 35.0f);// Init empty object
}

void ErrorBox::DisplayError(const AdvancedString& text)
{
	m_ErrorText->SetText(text);
}

ErrorBox::~ErrorBox()
{
}

void ErrorBox::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_ErrorText);
	r->AddToRenderQueue(m_ErrorBoxText);

	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}

	UIElement::RenderPass(r);
}