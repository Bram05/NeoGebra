#include "TextInputField.h"

#include <GLFW/glfw3.h>
#include <cctype>
#include <streambuf>

TextInputField::TextInputField(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "TextInputField")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, bottomY), Point(rightX, bottomY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY)));
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, topY), Point(leftX, topY)));
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
	m_Input.insert(m_Editingindex, 1, (char)codepoint);
	++m_Editingindex;
	std::cout << "Input is now: " << m_Input << '\n';
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
			int index = m_Editingindex - 2;// hallo hallo
			if (index == -2) index = -1;
			while (index >= 0 && m_Input[index] != ' ')
				--index;
			++index;
			m_Editingindex = index;
		}
		else
		{
			m_Editingindex = std::max(m_Editingindex-1, 0);
		}
		break;
	case GLFW_KEY_RIGHT:
		if (mods & GLFW_MOD_CONTROL)
		{
			int index = m_Editingindex;
			if (index == m_Input.size())
				index -= 1;
			while (index < m_Input.size() - 1 && m_Input[index] != ' ')
				++index;
			++index;
			m_Editingindex = index;
		}
		else
			m_Editingindex = std::min(m_Editingindex+1, (int)m_Input.size());
		break;
	case GLFW_KEY_BACKSPACE:
		if (m_Editingindex != 0 && m_Input.size() >= m_Editingindex)
		{
			m_Input.erase(m_Editingindex-1, 1);
			--m_Editingindex;
		}
		break;
	case GLFW_KEY_DELETE:
		if (m_Editingindex < m_Input.size())
		{
			m_Input.erase(m_Editingindex, 1);
		}
		break;
	default: return;
	}
	std::cout << "Input is now: " << m_Input << '\n';
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
}
