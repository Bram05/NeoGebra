#include "VariableWindowUI.h"

#include "TextInputField.h"
#include "ButtonUI.h"

static void UpdateVariables(void* obj)
{
	std::cout << "Clicked\n";
}

VariableWindowUI::VariableWindowUI(VarMap* variables)
	: m_VarMap{variables}
{
	float currentHeight{ 1.0f - 0.05f };

	for (int i{ 0 }; i < variables->second.size(); ++i)
	{
		m_UIElements.emplace_back(std::make_shared<TextInputField>(-1.0f + 0.01f, -1.0f + 0.15f, currentHeight, currentHeight - 0.15f, UpdateVariables, this, variables->second[i].first));
		m_Texts.emplace_back(std::make_shared<Text>(".", -1.0f+0.16f, -1.0f+0.19f, currentHeight - 0.13f, 40.0f));
		m_UIElements.emplace_back(std::make_shared<TextInputField>(-1.0f + 0.17f, 1.0f - 0.01f, currentHeight, currentHeight - 0.15f, UpdateVariables, this, variables->second[i].second->m_EquationString));
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
