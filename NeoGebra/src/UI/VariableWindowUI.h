#pragma once

#include "WindowUI.h"

struct Window;

class VariableWindowUI : public WindowUI
{
public:
	VariableWindowUI(VarMap* variables, Window* window, const std::vector<AdvancedString>& identifier);

	virtual void RenderPass(Renderer* r) override;

	friend void UpdateVariables(void* obj);

private:
	VarMap* m_VarMap;
	std::vector<std::shared_ptr<Text>> m_Texts;
	std::vector<AdvancedString> m_Identifiers;
};