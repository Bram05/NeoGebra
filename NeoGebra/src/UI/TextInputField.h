// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "Rendering/Renderer.h"
#include "Window.h"

// A text input field that takes input and renders it
class TextInputField : public UIElement
{
public:
	TextInputField(float leftX, float rightX, float topY, float bottomY, void(*enterCallback)(void*) = nullptr, void* obj = nullptr, const AdvancedString& defaultText = AdvancedString(""), float lineThickness = 0.002f, Window* window = nullptr);
	virtual ~TextInputField();

	const AdvancedString& GetText() const { return m_Text->GetText(); }
	void SetText(const AdvancedString& text);
	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void IsSelected() override;
	virtual void NotSelectedAnymore() override;
	virtual void TextInput(unsigned int codepoint) override;
	virtual void SpecialKeyInput(int key, int scancode, int action, int mods) override;
	virtual void ResizeWindow(int width, int height) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::shared_ptr<Line> m_EditingLine;
	std::shared_ptr<Text> m_Text;
	Window* m_Window;
	int m_Editingindex;
	void(*m_EnterCallback)(void*);
	void* m_Obj;

	// Update the blinking line that indicates where the cursor is
	void UpdateEditingLine();
	void UpdateEditingIndex(int offset, bool isRemoved, bool wasResized = false);
};
