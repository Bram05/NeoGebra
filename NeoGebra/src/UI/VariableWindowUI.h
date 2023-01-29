#pragma once

#include "WindowUI.h"

struct Window;

using VarMapPart=std::vector<std::pair<AdvancedString, std::shared_ptr<Equation>>>;

class VariableWindowUI : public WindowUI
{
public:
	VariableWindowUI(VarMapPart* variables, Window* window, const std::vector<AdvancedString>& identifier);

	virtual void RenderPass(Renderer* r) override;

	friend void UpdateVariables(void* obj);

private:
	VarMapPart* m_VarMapPart;
	std::vector<std::shared_ptr<Text>> m_Texts;
	std::vector<AdvancedString> m_Identifiers;
};