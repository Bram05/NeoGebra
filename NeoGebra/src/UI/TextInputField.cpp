// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "TextInputField.h"

#include <GLFW/glfw3.h>
#include <cctype>

#include "Application.h"

TextInputField::TextInputField(float leftX, float rightX, float topY, float bottomY, void(*enterCallback)(void*), void* obj)
	: UIElement(leftX, rightX, topY, bottomY, "TextInputField"), m_Text(), m_EnterCallback{enterCallback}, m_Obj{obj}
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, bottomY), Point(rightX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, topY), Point(leftX, topY)));
	auto [width, height] = Application::Get()->GetWindow()->GetSize();
	m_EditingLine = std::make_shared<Line>(Point(m_LeftX + 0.01f, m_BottomY + 0.045f), Point(m_LeftX + 0.01f, m_BottomY + 0.05f + (float)60 / height));
	m_Text = std::make_shared<Text>(AdvancedString(""), leftX + 0.01f, rightX - 0.01f, bottomY + 0.05f, 55.0f, false);
}

TextInputField::~TextInputField()
{
}

void TextInputField::IsSelected()
{
	for (std::shared_ptr<Line>& l : m_Lines)
	{
		l->SetColour({ 0.0f, 1.0f, 0.0f, 1.0f });
	}
}

void TextInputField::TextInput(unsigned int codepoint)
{
	m_Text->AddText(AdvancedString(codepoint), m_Editingindex);
	UpdateEditingIndex(m_Editingindex + 1, true);
	UpdateEditingLine();
}

void TextInputField::SpecialKeyInput(int key, int scancode, int action, int mods)
{
	if (action == GLFW_RELEASE)
		return;
	if (key == GLFW_KEY_ENTER)
	{
		if (m_EnterCallback)
			m_EnterCallback(m_Obj);
	}

	switch (key)
	{
	case GLFW_KEY_LEFT:
		if (mods & GLFW_MOD_CONTROL)
		{
			int index = m_Editingindex - 2;
			if (index == -2) index = -1;
			while (index >= 0 && m_Text->GetText()[index] != ' ')
				--index;
			++index;
			UpdateEditingIndex(index, false);
			UpdateEditingLine();
		}
		else
		{
			UpdateEditingIndex(std::max(m_Editingindex - 1, 0), false);
			UpdateEditingLine();
		}
		break;
	case GLFW_KEY_RIGHT:
		if (mods & GLFW_MOD_CONTROL)
		{
			int index = m_Editingindex;
			if (index == m_Text->GetText().size())
				index -= 1;
			while (index < m_Text->GetText().size() - 1 && m_Text->GetText()[index] != ' ')
				++index;
			++index;
			UpdateEditingIndex(index, false);
			UpdateEditingLine();
		}
		else
		{
			UpdateEditingIndex(std::min(m_Editingindex + 1, (int)m_Text->GetText().size()), false);
			UpdateEditingLine();
		}
		break;
	case GLFW_KEY_BACKSPACE:
		if (m_Editingindex != 0 && m_Text->GetText().size() >= m_Editingindex)
		{
			m_Text->RemoveText(m_Editingindex - 1, 1);
			UpdateEditingIndex(m_Editingindex - 1, true);
			UpdateEditingLine();
		}
		break;
	case GLFW_KEY_DELETE:
		if (m_Editingindex < m_Text->GetText().size())
		{
			m_Text->RemoveText(m_Editingindex, 1);
			UpdateEditingIndex(m_Editingindex, true);
		}
		break;
	case GLFW_KEY_V:
		if (mods & GLFW_MOD_CONTROL)
		{
			const char* content{ Application::Get()->GetWindow()->GetClipboardContent() };
			int i{0};
			while (content[i])
			{
				TextInput(content[i]);
				++i;
			}
		}
		break;
	default: return;
	}
}

void TextInputField::ResizeWindow(int widht, int height)
{
	UpdateEditingLine();
}

void TextInputField::NotSelectedAnymore()
{
	for (std::shared_ptr<Line>& l : m_Lines)
	{
		l->SetColour({ 1.0f, 0.0f, 0.0f, 1.0f });
	}
}

void TextInputField::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& l : m_Lines)
	{
		r->AddToRenderQueue(l);
	}
	if (m_IsSelected)
	{
		float intensity{ 0.5f + 0.5f * (float)std::sin(
		3 * glfwGetTime()) };
		m_EditingLine->SetColour({ 1.0f, 0.0f, 0.0f, intensity });
		r->AddToRenderQueue(m_EditingLine);
	}
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}

void TextInputField::UpdateEditingLine()
{
	auto [width, height] = Application::Get()->GetWindow()->GetSize();
	auto font{ Application::Get()->GetRenderer()->GetFont() };
	const AdvancedString& text = m_Text->GetText();

	float x = m_LeftX + 0.01f;
	for (int i{ m_Text->m_RenderBegin }; i < m_Editingindex; ++i)
	{
		x += font->GetCharacterInfo(text[i]).xAdvance * m_Text->GetScale() / width;
	}
	m_EditingLine->SetLocation(Point(x, m_BottomY + 0.045f), Point(x, m_BottomY + 0.05f + (float)55 / height));
}

void TextInputField::UpdateEditingIndex(int newIndex, bool isRemoved)
{
	auto [width, height] = Application::Get()->GetWindow()->GetSize();
	int offset = (newIndex - m_Editingindex);
	m_Editingindex = newIndex;
	auto font{ Application::Get()->GetRenderer()->GetFont() };
	if (offset >= 0) // Offset is 0 after delete is pressed
	{
		// TODO hij gaat er nog wel eens overheen
		if (m_Editingindex > m_Text->m_RenderEnd)
		{
			m_Text->m_RenderEnd = m_Editingindex; // maybe change this to += offset for a nicer effect when jumping around
			m_Text->m_RenderBegin = m_Text->m_RenderEnd - 1;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{ 0.0f };
			float lastCharacterAddition{ 0.0f };
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f)
			{
				if (m_Text->m_RenderBegin == -1)
				{
					m_Text->m_RenderBegin = -2;
					break;
				}
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderBegin]).xAdvance * m_Text->GetScale() / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderBegin]) };
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				--m_Text->m_RenderBegin;
			}
			m_Text->m_RenderBegin += 2;
		}
		else
		{
			m_Text->m_RenderEnd = m_Text->m_RenderBegin;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{ 0.0f };
			float lastCharacterAddition{ 0.0f };
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f && m_Text->m_RenderEnd < m_Text->GetText().size())
			{
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]).xAdvance * m_Text->GetScale() / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]) };
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				++m_Text->m_RenderEnd;
			}
			if (totalRenderWidth + lastCharacterAddition >= m_RightX - m_LeftX - 2 * 0.01f)
				--m_Text->m_RenderEnd;
		}
	}
	else
	{
		if (m_Editingindex < m_Text->m_RenderBegin)
		{
			m_Text->m_RenderBegin = m_Editingindex;
			if (isRemoved && m_Text->m_RenderBegin > 0)
			{
				m_Text->m_RenderBegin -= 1;// TODO: maybe change this to jump a few characters back to show what is being deleted
			}
			m_Text->m_RenderEnd = m_Text->m_RenderBegin;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{ 0.0f };
			float lastCharacterAddition{ 0.0f };
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f)
			{
				totalRenderWidth += renderWidthAddition;
				if (m_Text->m_RenderEnd == m_Text->GetText().size())
				{
					m_Text->m_RenderEnd += 1;
					break;
				}
				renderWidthAddition = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]).xAdvance * m_Text->GetScale() / width;
				const CharacterInfo& info = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]);
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				++m_Text->m_RenderEnd;
			}
			--m_Text->m_RenderEnd;
		}
		else
		{
			m_Text->m_RenderEnd = m_Text->m_RenderBegin;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{ 0.0f };
			float lastCharacterAddition{ 0.0f };
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f && m_Text->m_RenderEnd < m_Text->GetText().size())
			{
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]).xAdvance * m_Text->GetScale() / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd]) };
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				++m_Text->m_RenderEnd;
			}
			//--m_Text->m_RenderEnd;
		}
	}
}
