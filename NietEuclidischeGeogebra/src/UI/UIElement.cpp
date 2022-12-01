#include "UIElement.h"

#include "Renderer.h"

UIElement::UIElement(double leftX, double rightX, double topY, double bottomY, const std::string& name)
	: m_LeftX{ leftX },
	m_RightX{ rightX },
	m_TopY{ topY },
	m_BottomY{ bottomY },
	m_Name{ name }
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
}

UIElement::~UIElement()
{
}

std::pair<bool, std::shared_ptr<UIElement>> UIElement::Hit(float x, float y, void(UIElement::*callback)(float, float))
{
	if (x > m_LeftX && x < m_RightX && y > m_BottomY && y < m_TopY)
	{
		for (std::shared_ptr<UIElement>& element : m_SubUIElements)
		{
			std::pair<bool, std::shared_ptr<UIElement>> out = element->Hit(x, y, callback);
			if (out.second)
			{
				return out;
			}
			if (out.first)
			{
				((*element).*callback)(x, y);
				out.second = element;
				return out;
			}
		}
		return { true, nullptr };
	}
	return { false, nullptr };
}

void UIElement::RenderPass(Renderer* r)
{
	for (const std::shared_ptr<UIElement>& el : m_SubUIElements)
	{
		el->RenderPass(r);
	}
	for (const std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
}
