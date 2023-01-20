// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "Rendering/Renderer.h"

// A text input field that takes input and renders it
class TextInputField : public UIElement
{
public:
	TextInputField(double leftX, double rightX, double topY, double bottomY, void(*enterCallback)(void*) = nullptr, void* obj = nullptr);
	virtual ~TextInputField();

	// Get the text as a vector of the unicode character and the width of this character
	const AdvancedString& GetText() const { return m_Text->GetText(); }
	virtual void RenderPass(Renderer* r) override;

protected:
	virtual void IsSelected() override;
	virtual void NotSelectedAnymore() override;
	virtual void TextInput(unsigned int codepoint) override;
	virtual void SpecialKeyInput(int key, int scancode, int action, int mods) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::shared_ptr<Line> m_EditingLine;
	std::shared_ptr<Text> m_Text;
	int m_Editingindex{ 0 };
	void(*m_EnterCallback)(void*);
	void* m_Obj;

	void SetEditingLine();
	void UpdateEditingIndex(int offset, bool isRemoved);
};