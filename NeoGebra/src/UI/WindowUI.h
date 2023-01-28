// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/Renderer.h"
#include "GraphUI.h"

// Represents all the UI
// Owns all subparts and updates them
class WindowUI
{
public:
	WindowUI();
	virtual ~WindowUI() {}

	// Call the renderpass on all the contained UI elements
	virtual void RenderPass(Renderer* r);

	// To be called on certain events. WindowUI will then pass these to the correct UIElement
	std::shared_ptr<UIElement> MouseClicked(float x, float y);
	std::shared_ptr<UIElement> MouseMoved(float x, float y);
	void MouseReleased();
	void TextInput(unsigned int codepoint);
	void SpecialKeyInput(int key, int scancode, int action, int mods);
	void ResizeWindow(int width, int height);
	void InsertKey(int codepoint);
	
protected:
	bool m_MouseDown = false;
	std::vector<std::shared_ptr<UIElement>> m_UIElements;
	std::shared_ptr<UIElement> m_CurrentlyHoveredElement{ nullptr };
	std::shared_ptr<UIElement> m_SelectedElement{ nullptr };

	// Recursive function to find the element that is at this position.
	// This function will the element that is furtherst in the tree that is under this position
	// SubElements must always be completely in the bounding box of their parent for this to work
	// @param elementPair: the element that is currently searched
	// @param x,y: the position to find
	std::shared_ptr<UIElement> Hit(const std::shared_ptr<UIElement>& elementPair, float x, float y);
};
