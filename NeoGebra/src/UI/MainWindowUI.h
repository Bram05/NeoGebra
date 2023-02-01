#pragma once

#include "WindowUI.h"

class EquationUI;

class MainWindowUI : public WindowUI
{
public:
	MainWindowUI();

	void DisplayError(const AdvancedString& error);
	void DisplayError(const std::string& error) { DisplayError(AdvancedString(error)); }
	void SetFPSCounter(float fps);
	void UpdateGraphUI();
	GraphUI* GetGraphUI();
	EquationUI* GetEquationUI() { return (EquationUI*)(m_UIElements[1].get()); }

private:
	int m_GraphUIIndex, m_FPSCounterIndex;
};