#include "TextInputField.h"

#include <GLFW/glfw3.h>
#include <cctype>

#include "Application.h"

TextInputField::TextInputField(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "TextInputField"), m_Text()
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, bottomY), Point(rightX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, topY), Point(leftX, topY)));
	auto[width,height] = Application::Get()->GetWindow()->GetSize();
	m_EditingLine = std::make_shared<Line>(Point(m_LeftX + 0.01f, m_BottomY + 0.045f), Point(m_LeftX + 0.01f, m_BottomY + 0.05f + (float)60/height));
	m_Text = std::make_shared<Text>(std::vector<int>{}, leftX + 0.01f, rightX - 0.01f, bottomY + 0.05f, 55);
}

TextInputField::~TextInputField()
{
}

void TextInputField::IsSelected()
{
	for (std::shared_ptr<Line>& l : m_Lines)
	{
		l->SetColour({0.0f, 1.0f, 0.0f, 1.0f});
	}
}

void TextInputField::TextInput(unsigned int codepoint)
{
	m_Text->AddText(std::vector<int>{(int)codepoint}, m_Editingindex);
	UpdateEditingIndex(m_Editingindex+1, true);
	SetEditingLine();
}

void TextInputField::SpecialKeyInput(int key, int scancode, int action, int mods)
{
	if (action == GLFW_RELEASE)
		return;

	switch (key)
	{
	case GLFW_KEY_LEFT:
		if (mods & GLFW_MOD_CONTROL)
		{
			int index = m_Editingindex - 2;
			if (index == -2) index = -1;
			while (index >= 0 && m_Text->GetText()[index].first != ' ')
				--index;
			++index;
			UpdateEditingIndex(index, false);
			SetEditingLine();
		}
		else
		{
			UpdateEditingIndex(std::max(m_Editingindex-1, 0), false);
			SetEditingLine();
		}
		break;
	case GLFW_KEY_RIGHT:
		if (mods & GLFW_MOD_CONTROL)
		{
			int index = m_Editingindex;
			if (index == m_Text->GetText().size())
				index -= 1;
			while (index < m_Text->GetText().size() - 1 && m_Text->GetText()[index].first != ' ')
				++index;
			++index;
			UpdateEditingIndex(index, false);
			SetEditingLine();
		}
		else
		{
			UpdateEditingIndex(std::min(m_Editingindex+1, (int)m_Text->GetText().size()), false);
			SetEditingLine();
		}
		break;
	case GLFW_KEY_BACKSPACE:
		if (m_Editingindex != 0 && m_Text->GetText().size() >= m_Editingindex)
		{
			m_Text->RemoveText(m_Editingindex-1, 1);
			UpdateEditingIndex(m_Editingindex-1, true);
			SetEditingLine();
		}
		break;
	case GLFW_KEY_DELETE:
		if (m_Editingindex < m_Text->GetText().size())
		{
			m_Text->RemoveText(m_Editingindex, 1);
			UpdateEditingIndex(m_Editingindex, true);
		}
		break;
	default: return;
	}
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
		float intensity{0.5f + 0.5f * (float)std::sin(
		3 * glfwGetTime())};
		m_EditingLine->SetColour({1.0f, 0.0f, 0.0f, intensity});
		r->AddToRenderQueue(m_EditingLine);
	}
	r->AddToRenderQueue(m_Text);
	UIElement::RenderPass(r);
}

void TextInputField::SetEditingLine()
{
	auto[width, height] = Application::Get()->GetWindow()->GetSize();
	const std::vector<std::pair<int,float>>& text = m_Text->GetText();

	float x = m_LeftX + 0.01f;
	for (int i{m_Text->m_RenderBegin}; i < m_Editingindex; ++i)
	{
		x += text[i].second / width;
	}
	m_EditingLine->SetLocation(Point(x, m_BottomY + 0.045f), Point(x, m_BottomY + 0.05f + (float)55 / height));
}

void TextInputField::UpdateEditingIndex(int newIndex, bool isRemoved)
{
	auto[width, height] = Application::Get()->GetWindow()->GetSize();
	int offset = (newIndex - m_Editingindex);
	m_Editingindex = newIndex;
	auto font{Application::Get()->GetRenderer()->GetFont()};
	if (offset >= 0) // Offset is 0 after delete is pressed
	{
		// TODO hij gaat er nog wel eens overheen
		if (m_Editingindex > m_Text->m_RenderEnd)
		{
			m_Text->m_RenderEnd = m_Editingindex; // maybe change this to += offset for a nicer effect when jumping around
			m_Text->m_RenderBegin = m_Text->m_RenderEnd-1;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{ 0.0f };
			float lastCharacterAddition{0.0f};
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f)
			{
				if (m_Text->m_RenderBegin == -1)
				{
					m_Text->m_RenderBegin = -2;
					break;
				}
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = m_Text->GetText()[m_Text->m_RenderBegin].second / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderBegin].first) };
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
			float lastCharacterAddition{0.0f};
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f && m_Text->m_RenderEnd < m_Text->GetText().size())
			{
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = m_Text->GetText()[m_Text->m_RenderEnd].second / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd].first) };
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
			float renderWidthAddition{0.0f};
			float lastCharacterAddition{0.0f};
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f)
			{
				totalRenderWidth += renderWidthAddition;
				if (m_Text->m_RenderEnd == m_Text->GetText().size())
				{
					m_Text->m_RenderEnd += 1;
					break;
				}
				renderWidthAddition = m_Text->GetText()[m_Text->m_RenderEnd].second / width;
				const CharacterInfo& info = font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd].first);
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				++m_Text->m_RenderEnd;
			}
			--m_Text->m_RenderEnd;
		}
		else
		{
			m_Text->m_RenderEnd = m_Text->m_RenderBegin;
			float totalRenderWidth{ 0.0f };
			float renderWidthAddition{0.0f};
			float lastCharacterAddition{0.0f};
			while (totalRenderWidth + lastCharacterAddition < m_RightX - m_LeftX - 2 * 0.01f && m_Text->m_RenderEnd < m_Text->GetText().size())
			{
				totalRenderWidth += renderWidthAddition;
				renderWidthAddition = m_Text->GetText()[m_Text->m_RenderEnd].second / width;
				const CharacterInfo& info{ font->GetCharacterInfo(m_Text->GetText()[m_Text->m_RenderEnd].first) };
				lastCharacterAddition = ((float)info.width) / width * m_Text->GetScale();
				++m_Text->m_RenderEnd;
			}
			//--m_Text->m_RenderEnd;
		}
	}
}
