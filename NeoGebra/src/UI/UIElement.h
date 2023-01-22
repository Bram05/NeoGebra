// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "Rendering/LineRenderer.h"

class Renderer;
class WindowUI;

class UIElement;

// Simple struct for a SubUIElement
struct SubUIElement
{
	std::shared_ptr<UIElement> element;
	bool shouldRender{true};
};

// Base class for a subpart of the UI
class UIElement
{
public:
	UIElement(float leftX, float rightX, float topY, float bottomY, const std::string& name);
	virtual ~UIElement();

	// Getters
	float GetLeftX() const { return m_LeftX; }
	float GetTopY() const { return m_TopY; }
	float GetRightX() const { return m_RightX; }
	float GetBottomY() const { return m_BottomY; }
	const std::string& GetName() const { return m_Name; }

	// Queue all the necessary things for rendering
	virtual void RenderPass(Renderer* r);
	virtual void UpdateGraphUI();

protected:
	// Virtual functions for UIElement to do something on certain events
	virtual void WasClicked(float x, float y) { /*std::cout << "Hit element " << m_Name << '\n'; */ }
	virtual void DraggedUpdate(float x, float y) { /*std::cout << "Dragged update" << m_Name << '\n'; */ }
	virtual void IsHovered(float x, float y) { /*std::cout << "Hovered over element " << m_Name << '\n'; */ }
	virtual void NotHoveredAnymore() { /*std::cout << "Not hovering over element " << m_Name << " anymore\n";*/ }
	virtual void IsSelected() { /*std::cout << "Element " << m_Name << " is selected\n";*/ }
	virtual void NotSelectedAnymore() { /*std::cout << "Element " << m_Name << " is not selected anymore\n"; */ }
	virtual void TextInput(unsigned int codepoint) { /*std::cout << "Got key " << key << '\n';*/ }
	virtual void SpecialKeyInput(int key, int scancode, int action, int mods) {}
	virtual void ResizeWindow(int width, int height);
	friend WindowUI;

	// The bounds of this element
	float m_LeftX, m_RightX, m_TopY, m_BottomY;
	std::string m_Name;
	std::vector<SubUIElement> m_SubUIElements;
	bool m_MouseIsHovering{ false };
	bool m_IsSelected{ false };
	bool m_IsBeingDragged{ false };
};