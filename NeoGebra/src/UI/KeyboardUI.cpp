﻿// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "KeyboardUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"

static void insertKey(void* c)
{
	Application::Get()->GetWindowUI()->InsertKey(*(int*)c);
}

// The list of all unicode numbers of the characters in the keyboard
std::vector<AdvancedString> textList{ 0x2200, 0x2203, 0x2208, 0x03B1, 0x03B2, 0x03B3, 0x03B8, 0x03C0 };

KeyboardUI::KeyboardUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "KeyboardUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	float buttonWidth = 0.1f;
	float indent = 0.0175f;

	float x = leftX + indent;
	float y = topY - 0.01f;
	for (int i = 1; i <= textList.size(); i++) {
		m_SubUIElements.push_back({ std::make_shared<ButtonUI>(x, x + buttonWidth, y, y - buttonWidth, insertKey, &textList[i-1], textList[i-1]) });
		if (i % 4 == 0) {
			x = leftX + indent;
			y -= buttonWidth;
			continue;
		}
		x += buttonWidth;
	}
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
	UIElement::RenderPass(r);
}