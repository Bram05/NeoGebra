#pragma once

#include "WindowUI.h"
#include "Maths/Equation.h"

class Window;

class ExtrasWindowUI : public WindowUI
{
public:
	ExtrasWindowUI(std::vector<Equation>* extraEquations, Window* window);

	friend void UpdateExtraEquations(void*);

private:
	std::vector<Equation>* m_ExtraEquations;
};