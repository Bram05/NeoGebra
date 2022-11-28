// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

class Renderer;

// Base class for a subpart of the UI
class UIElement
{
public:
	UIElement(double leftX, double rightX, double topY, double bottomY, const std::string& name)
		: m_LeftX{ leftX },
		m_RightX{ rightX },
		m_TopY{ topY },
		m_BottomY{ bottomY },
		m_Name{ name }
	{}
	virtual ~UIElement() {}

	// Getters
	double GetLeftX() const { return m_LeftX; }
	double GetTopY() const { return m_TopY; }
	double GetRightX() const { return m_RightX; }
	double GetBottomY() const { return m_BottomY; }
	const std::string& GetName() const { return m_Name; }

	// Queue all the necessary things for rendering
	virtual void RenderPass(Renderer* r) = 0;

protected:
	// The bounds of this element
	double m_LeftX, m_RightX, m_TopY, m_BottomY;
	std::string m_Name;
};