// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Renderer.h"

// Represents all the UI
// Owns all subparts and updates them
class WindowUI
{
public:
	WindowUI();
	~WindowUI();

	// Call the render on all the contained UI elements
	void RenderPass(Renderer* r);

	// Ask if this position is in any UI element
	std::shared_ptr<UIElement> MouseClicked(float x, float y);
	std::shared_ptr<UIElement> MouseMoved(float x, float y);
	void TextInput(unsigned int codepoint);
	void SpecialKeyInput(int key, int scancode, int action, int mods);

private:
	std::vector<std::shared_ptr<UIElement>> m_UIElements;
	std::shared_ptr<UIElement> Hit(const std::shared_ptr<UIElement>& element, float x, float y);
	std::shared_ptr<UIElement> m_CurrentlyHoveredElement{nullptr};
	std::shared_ptr<UIElement> m_SelectedElement{nullptr};
};
