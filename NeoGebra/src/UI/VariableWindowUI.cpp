#include "VariableWindowUI.h"

#include "TextInputField.h"
#include "ButtonUI.h"
#include "Window.h"

constexpr unsigned int c_NumVariables{ 5 };

void UpdateVariables(void* obj)
{
	VariableWindowUI* ui = (VariableWindowUI*)obj;
	VarMap* map = ui->m_VarMap;

	map->second.clear();
	//map->second.resize(c_NumVariables);
	for (int i = 0; i < c_NumVariables; i++)
	{
		TextInputField* name = (TextInputField*)(ui->m_UIElements[i * 2].get());
		TextInputField* decl = (TextInputField*)(ui->m_UIElements[i * 2 + 1].get());
		if (name->GetText().empty() || decl->GetText().empty())
			continue;
		map->second.emplace_back(name->GetText(), std::make_shared<Equation>(ui->m_Identifiers, decl->GetText()));
	}
}

VariableWindowUI::VariableWindowUI(VarMap* variables, Window* window, const std::vector<AdvancedString>& identifiers)
	: m_VarMap{ variables }, m_Identifiers{ identifiers }
{
	float currentHeight{ 1.0f - 0.05f };

	for (int i{ 0 }; i < c_NumVariables; ++i)
	{
		AdvancedString s1, s2;
		if (i < variables->second.size())
		{
			s1 = variables->second[i].first;
			s2 = variables->second[i].second->m_EquationString;
		}
		m_UIElements.emplace_back(std::make_shared<TextInputField>(-1.0f + 0.01f, -1.0f + 0.10f, currentHeight, currentHeight - 0.15f, UpdateVariables, this, s1, 0.005f, window));
		m_Texts.emplace_back(std::make_shared<Text>("=", -1.0f + 0.14f, -1.0f + 0.17f, currentHeight - 0.13f, 40.0f));
		m_UIElements.emplace_back(std::make_shared<TextInputField>(-1.0f + 0.19f, 1.0f - 0.01f, currentHeight, currentHeight - 0.15f, UpdateVariables, this, s2, 0.005f, window));
		currentHeight -= 0.18f;
	}
	m_UIElements.emplace_back(std::make_shared<ButtonUI>(-1.0f + 0.06f, 1.0f - 0.06f, currentHeight - 0.01f, currentHeight - 0.11f, UpdateVariables, this, "Update Variables"));
}

void VariableWindowUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Text>& t : m_Texts)
		r->AddToRenderQueue(t);
	WindowUI::RenderPass(r);
}
