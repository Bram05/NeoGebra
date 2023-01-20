// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "PostulateVerifier/PostulateVerifier.h"

#include "EquationUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "KeyboardUI.h"
#include "TabUI.h"
#include "TextInputFieldWithDesc.h"

static void TabButtonClickedStatic(void* obj, int value)
{
	((EquationUI*)obj)->TabButtonClicked(value);
}

static void UpdateGraphsStatic(void* obj)
{
	((EquationUI*)obj)->UpdateGraphs();
}

static void UpdateModelStatic(void* obj)
{
	((EquationUI*)obj)->UpdateModel();
}

constexpr int NumInputFields{ 5 };

EquationUI::EquationUI(double leftX, double rightX, double topY, double bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	//m_SubUIElements.push_back({std::make_shared<ButtonUI>(leftX + 0.2f, (leftX + 0.4f), topY - 0.5f, (topY - 1.0f))});
	m_PointsIndexBegin = m_SubUIElements.size();
	for (int i{ 0 }; i < NumInputFields; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX, rightX, topY - 0.2f - i * 0.15f, topY - 0.35f - i * 0.15f, UpdateGraphsStatic, this));
	}
	m_LinesIndexBegin = m_SubUIElements.size();
	for (int i{ 0 }; i < NumInputFields; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX, rightX, topY - 0.2f - i * 0.15f, topY - 0.35f - i * 0.15f, UpdateGraphsStatic, this), false);
	}

	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.2f, topY - 0.4f, "Point definition: ", 0.2f, UpdateModelStatic, this), false);
	m_PointDefInputField = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.4f, topY - 0.6f, "Line definition: ", 0.2f, UpdateModelStatic, this), false);
	m_LineDefInputField = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<KeyboardUI>(leftX, rightX, bottomY + 0.7f, bottomY));
	m_SubUIElements.emplace_back(std::make_shared<TabUI>(leftX, rightX, topY, topY - 0.2f, 0, &TabButtonClickedStatic, this));
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.85f, bottomY + 0.72f, UpdateGraphsStatic, this, "Update graphs"));
	m_UpdateGraphsButton = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.85f, bottomY + 0.72f, UpdateModelStatic, this, "Update model"), false);
	m_UpdateModelButton = m_SubUIElements.size() - 1;

	//m_Texts.push_back(std::make_shared<Text>("ABCDEFGHIJKLMNOPQRSTUVWXYZ", -1.0f, 0.0f, 0.5f, 72));
	//m_Texts.push_back(std::make_shared<Text>("abcdefghijklmnopqrstuvwxyz123456789", -1.0f, 0.0f, -0.5f, 100));
	//m_Texts.push_back(std::make_shared<Text>(std::vector<int>{8704, 8707}, -1.0f, 0.0f, 0.0f, 72));
	//m_Lines.push_back(std::make_shared<Line>(Point(-1.0f, 0.5f), Point(0.0f, 0.5f)));
}

EquationUI::~EquationUI()
{
}

void EquationUI::TabButtonClicked(int value)
{
	for (int i{ m_PointsIndexBegin }; i < m_PointsIndexBegin + NumInputFields; i++)
	{
		m_SubUIElements[i].shouldRender = value == 0;
	}
	for (int i{ m_LinesIndexBegin }; i < m_LinesIndexBegin + NumInputFields; i++)
	{
		m_SubUIElements[i].shouldRender = value == 1;
	}
	m_SubUIElements[m_PointDefInputField].shouldRender = value == 2;
	m_SubUIElements[m_LineDefInputField].shouldRender = value == 2;
	m_SubUIElements[m_UpdateGraphsButton].shouldRender = value == 0 || value == 1;
	m_SubUIElements[m_UpdateModelButton].shouldRender = value == 2;
}


void EquationUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	for (std::shared_ptr<Text>& text : m_Texts)
	{
		r->AddToRenderQueue(text);
	}
	UIElement::RenderPass(r);
}

std::vector<float> EquationUI::ParseInput(const AdvancedString& input)
{
	std::vector<float> identifiers;
	int beginOfNumber{ 0 };
	for (int i{ 0 }; i < input.size(); ++i)
	{
		if (input[i] == ',')
		{
			std::string tmp(input.begin() + beginOfNumber, input.begin() + i);
			identifiers.push_back(std::stof(tmp));
			beginOfNumber = i + 1;
		}
	}
	std::string tmp(input.begin() + beginOfNumber, input.end());
	identifiers.push_back(std::stof(tmp));
	return identifiers;
}

void EquationUI::UpdateGraphs()
{
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();
	Application::Get()->GetModelManager()->GetModel()->getElements().clear();
	for (int i{ m_PointsIndexBegin }; i < m_PointsIndexBegin + NumInputFields; ++i)
	{
		const AdvancedString& text{ ((TextInputField*)(m_SubUIElements[i].element.get()))->GetText() };
		if (text.empty())
			continue;

		try {
			std::vector<float> identifiers{ ParseInput(text) };
			new NEPoint(identifiers, Application::Get()->GetModelManager()->GetModel(), { 255, 0, 0, 255 }, false);
		}
		catch (const std::exception&)
		{
			std::string input;
			for (int i : text)
				input.push_back(i);
			std::cerr << "Failed to create the point " << input << '\n';
		}
	}

	for (int i{ m_LinesIndexBegin }; i < m_LinesIndexBegin + NumInputFields; ++i)
	{
		const AdvancedString& text{ ((TextInputField*)(m_SubUIElements[i].element.get()))->GetText() };
		if (text.empty())
			continue;

		try {
			std::vector<float> identifiers{ ParseInput(text) };
			new NELine(identifiers, Application::Get()->GetModelManager()->GetModel(), { 255, 255, 0, 255 }, false);
		}
		catch (const std::exception&)
		{
			std::string input;
			for (int i : text)
				input.push_back(i);
			std::cerr << "Failed to create the line " << input << '\n';
		}
	}
	Application::Get()->GetWindowUI()->UpdateGraphUI();
}

void EquationUI::UpdateModel()
{
	const AdvancedString& pointDef{ ((TextInputFieldWithDesc*)(m_SubUIElements[m_PointDefInputField].element.get()))->GetText() };
	const AdvancedString& lineDef{ ((TextInputFieldWithDesc*)(m_SubUIElements[m_LineDefInputField].element.get()))->GetText() };
	Equation pointDefEq({ AdvancedString("p") }, pointDef);
	Equation lineDefEq({ {'l'}}, lineDef);
	std::shared_ptr<Model> model{ Application::Get()->GetModelManager()->GetModel() };
	Application::Get()->GetModelManager()->SetModel(model->GetNumPointIdentifiers(), pointDefEq, model->GetNumLineIdentifiers(), lineDefEq, model->GetIncidenceConstr(), model->GetBetweennessConstr());
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();
	UpdateGraphs();
}
