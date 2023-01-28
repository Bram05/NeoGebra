#pragma once

#include "WindowUI.h"

class VariableWindowUI : public WindowUI
{
public:
	VariableWindowUI(VarMap* variables);

	virtual void RenderPass(Renderer* r) override;

private:
	VarMap* m_VarMap;
	std::vector<std::shared_ptr<Text>> m_Texts;
};