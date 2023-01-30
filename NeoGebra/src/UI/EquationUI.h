// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "TextInputField.h"
#include "VariableWindowUI.h"

static void TabButtonClickedStatic(void*,int);

// Represents what will eventually be the part where equations can be written
class EquationUI : public UIElement
{
public:
	EquationUI(float leftX, float rightX, float topY, float bottomY);
	~EquationUI();

	void UpdateGraphs();
	void UpdateModel();

	VarMap m_Variables;
	std::vector<Equation> m_ExtraEquations;

protected:
	void RenderPass(Renderer* r) override;
	std::vector<std::shared_ptr<Text>> m_Texts;
	std::shared_ptr<Text> m_PointText;
	std::shared_ptr<Text> m_LineText;
	std::vector<std::shared_ptr<Text>> m_ModelTexts;
	std::vector<std::shared_ptr<NEPoint>> m_NEPoints;
	std::vector<std::shared_ptr<NELine>> m_NELines;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	int m_LinesIndexBegin, m_PointsIndexBegin, m_LineDefInputField, m_PointDefInputField;
	int m_ModelBeginIndex, m_ModelEndIndex;
	int m_UpdateGraphsButton;
	int m_ButtonValue{2};

	void TabButtonClicked(int value);
	friend void TabButtonClickedStatic(void*,int);

	std::vector<float> ParseInput(const AdvancedString& input);
};
