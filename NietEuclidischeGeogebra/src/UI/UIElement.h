// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

// Base class for a subpart of the UI
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
	// The bounds of this element
	double m_LeftX, m_RightX, m_TopY, m_BottomY;
};