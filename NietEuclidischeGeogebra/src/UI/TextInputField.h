#pragma once

#include "UIElement.h"
#include "LineRenderer.h"
#include "TextRenderer.h"
#include "Renderer.h"

class TextInputField : public UIElement
{
public:
	TextInputField(double leftX, double rightX, double topY, double bottomY);
	~TextInputField();

protected:
	virtual void IsSelected() override;
	virtual void TextInput(unsigned int codepoint) override;
	virtual void SpecialKeyInput(int key, int scancode, int action, int mods) override;
	virtual void NotSelectedAnymore() override;
	virtual void RenderPass(Renderer* r) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::shared_ptr<Line> m_EditingLine;
	std::shared_ptr<Text> m_Text;
	std::string m_Input;
	int m_Editingindex{0};

	void SetEditingLine();
	void UpdateEditingIndex(int offset, bool isRemoved);
};
