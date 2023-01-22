// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

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

EquationUI::EquationUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

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

	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.2f, topY - 0.4f, "Number of point identifiers: ", 0.2f, UpdateModelStatic, this), false);
	m_ModelBeginIndex = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.4f, topY - 0.6f, "Point definition: ", 0.2f, UpdateModelStatic, this), false);
	m_PointDefInputField = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.6f, topY - 0.8f, "Number of line identifiers: ", 0.2f, UpdateModelStatic, this), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX, topY - 0.8f, topY - 1.0f, "Line definition: ", 0.2f, UpdateModelStatic, this), false);
	m_LineDefInputField = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.85f, bottomY + 0.72f, UpdateModelStatic, this, "Update model"), false);
	m_ModelEndIndex = m_SubUIElements.size() - 1;
	m_SubUIElements.emplace_back(std::make_shared<KeyboardUI>(leftX, rightX, bottomY + 0.7f, bottomY));
	m_SubUIElements.emplace_back(std::make_shared<TabUI>(leftX, rightX, topY, topY - 0.2f, 0, &TabButtonClickedStatic, this));
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.85f, bottomY + 0.72f, UpdateGraphsStatic, this, "Update graphs"));
	m_UpdateGraphsButton = m_SubUIElements.size() - 1;
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
	for (int i{ m_ModelBeginIndex }; i <= m_ModelEndIndex; i++)
	{
		m_SubUIElements[i].shouldRender = value == 2;
	}
	m_SubUIElements[m_UpdateGraphsButton].shouldRender = value == 0 || value == 1;
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
	Application::Get()->GetModel()->getElements().clear();
	for (int i{ m_PointsIndexBegin }; i < m_PointsIndexBegin + NumInputFields; ++i)
	{
		const AdvancedString& text{ ((TextInputField*)(m_SubUIElements[i].element.get()))->GetText() };
		if (text.empty())
			continue;

		try {
			std::vector<float> identifiers{ ParseInput(text) };
			if (identifiers.size() != Application::Get()->GetModel()->GetNumPointIdentifiers())
			{
				std::string input;
				for (int i : text)
					input.push_back(i);
				std::cerr << "Failed to create the point: " << input << " because it has " << identifiers.size() << " identifiers while the model needs " << Application::Get()->GetModel()->GetNumPointIdentifiers() << '\n';
				continue;
			}
			new NEPoint(identifiers, Application::Get()->GetModel(), { 255, 0, 0, 255 }, false);
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
			if (identifiers.size() != Application::Get()->GetModel()->GetNumLineIdentifiers())
			{
				std::string input;
				for (int i : text)
					input.push_back(i);
				std::cerr << "Failed to create the line: " << input << " because it has " << identifiers.size() << " identifiers while the model needs " << Application::Get()->GetModel()->GetNumLineIdentifiers() << '\n';
				continue;
			}
			new NELine(identifiers, Application::Get()->GetModel(), { 255, 255, 0, 255 }, false);
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
	int numPointsIdents{ std::stoi(((TextInputFieldWithDesc*)(m_SubUIElements[m_ModelBeginIndex].element.get()))->GetText().toString()) };
	int numLineIdents{ std::stoi(((TextInputFieldWithDesc*)(m_SubUIElements[m_ModelBeginIndex+2].element.get()))->GetText().toString()) };
	Equation pointDefEq({ AdvancedString("p") }, pointDef);
	Equation lineDefEq({ {AdvancedString("l") } }, lineDef);
	std::shared_ptr<Model> model{ Application::Get()->GetModel() };
	Application::Get()->SetModel(numPointsIdents, pointDefEq, numLineIdents, lineDefEq, model->GetIncidenceConstr(), model->GetBetweennessConstr());
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();
	UpdateGraphs();
}
