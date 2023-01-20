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
	~WindowUI();

	// Call the renderpass on all the contained UI elements
	void RenderPass(Renderer* r);

	// Ask if this position is in any UI element
	std::shared_ptr<UIElement> MouseClicked(float x, float y);
	std::shared_ptr<UIElement> MouseMoved(float x, float y);
	void MouseReleased();
	void TextInput(unsigned int codepoint);
	void SpecialKeyInput(int key, int scancode, int action, int mods);
	void ResizeWindow(int width, int height);
	void UpdateGraphUI();
	GraphUI* GetGraphUI();
	void InsertKey(int codepoint);

private:
	bool m_MouseDown = false;
	std::vector<std::shared_ptr<UIElement>> m_UIElements;
	std::shared_ptr<UIElement> Hit(const std::shared_ptr<UIElement>& elementPair, float x, float y);
	std::shared_ptr<UIElement> m_CurrentlyHoveredElement{ nullptr };
	std::shared_ptr<UIElement> m_SelectedElement{ nullptr };
	int m_GraphUIIndex;
};
