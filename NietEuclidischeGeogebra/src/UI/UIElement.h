#pragma once

class UIElement
{
public:
	UIElement(double leftX, double rightX, double topY, double bottomY)
		: m_LeftX{ leftX },
		m_RightX{ rightX },
		m_TopY{ topY },
		m_BottomY{ bottomY }
	{}
	virtual ~UIElement() {}

	virtual void RenderPass() = 0;
protected:
	double m_LeftX, m_RightX, m_TopY, m_BottomY;
};