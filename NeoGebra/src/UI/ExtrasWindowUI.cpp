#include "ExtrasWindowUI.h"

#include "TextInputField.h"
#include "ButtonUI.h"
#include "Window.h"

constexpr unsigned int c_NumVariables{5};

static void UpdateExtraEquations(void* obj)
{
	ExtrasWindowUI* ob = (ExtrasWindowUI*)obj;
	std::vector<Equation>* extras = ob->m_ExtraEquations;
	extras->clear();
	for (unsigned int i{ 0 }; i < c_NumVariables; ++i)
	{
		TextInputField* element = (TextInputField*)ob->m_UIElements[i].get();
		const AdvancedString& text = element->GetText();
		if (!text.empty())
		{
			extras->emplace_back(text);
		}
	}
}

ExtrasWindowUI::ExtrasWindowUI(std::vector<Equation>* extraEquations, Window* window)
	: m_ExtraEquations{extraEquations}
{
	float currentHeight{ 1.0f - 0.05f };

	for (int i{ 0 }; i < c_NumVariables; ++i)
	{
		AdvancedString text;
		if (i < extraEquations->size())
		{
			text = extraEquations->at(i).m_EquationString;
		}
		m_UIElements.emplace_back(std::make_shared<TextInputField>(-1.0f + 0.01f, 1.0f - 0.01f, currentHeight, currentHeight - 0.15f, UpdateExtraEquations, this, text, 0.005f, window));
		currentHeight -= 0.18f;
	}
	currentHeight -= 0.1f;
	m_UIElements.emplace_back(std::make_shared<ButtonUI>(-1.0f + 0.2f, 0.0f, currentHeight - 0.01f, currentHeight - 0.20f, UpdateExtraEquations, this, "Update Extra Equations"));
}
