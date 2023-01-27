// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "EquationUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "KeyboardUI.h"
#include "TabUI.h"
#include "TextInputFieldWithDesc.h"
#include "Window.h"

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

Window* g_PointVariableWindow{ nullptr };

static void ManagePointVariableWindow()
{
	g_PointVariableWindow = new Window({ 400,400,"Point Variables" });
	while (!g_PointVariableWindow->ShouldClose())
	{
		glClearColor(0.5f, 0.5f, 0.5f, 1.0f);
		glClear(GL_COLOR_BUFFER_BIT);

		g_PointVariableWindow->Update();
	}
	delete g_PointVariableWindow;
	g_PointVariableWindow = nullptr;
}

Window* g_LineVariableWindow{ nullptr };

static void ManageLineVariableWindow()
{
	g_LineVariableWindow = new Window({ 400,400,"Line Variables" });
	while (!g_LineVariableWindow->ShouldClose())
	{
		glClearColor(0.5f, 0.0f, 0.5f, 1.0f);
		glClear(GL_COLOR_BUFFER_BIT);

		g_LineVariableWindow->Update();
	}
	delete g_LineVariableWindow;
	g_LineVariableWindow = nullptr;
}

static void DisplayPointVariables(void* obj)
{
	if (!g_PointVariableWindow)
	{
		std::thread(ManagePointVariableWindow).detach();
	}
	else
		g_PointVariableWindow->Focus();
}

static void DisplayLineVariables(void* obj)
{
	if (!g_LineVariableWindow)
	{
		std::thread(ManageLineVariableWindow).detach();
	}
	else
		g_PointVariableWindow->Focus();
}
constexpr int NumInputFields{ 5 }, DefaultPointSize{ 10 }, DefaultLineWidth{ 3 };

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

	Application::Get()->GetRenderer()->GetGraphRenderer()->setPointSize(DefaultPointSize);
	Application::Get()->GetRenderer()->GetGraphRenderer()->setLineThickness(DefaultLineWidth);

	float currentHeight = topY - 0.2f;

	m_ModelBeginIndex = m_SubUIElements.size();
	// Point
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(rightX - 0.35f, rightX - 0.25f, currentHeight, currentHeight - 0.1f, DisplayPointVariables, this, "Variables", std::array<float, 4>{0.8f, 0.8f, 0.8f, 1.0f}, std::array<float, 4>{0.6f, 0.6f, 0.6f, 1.0f}), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.20f, rightX - 0.14f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString("p")), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.13f, rightX - 0.07f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString(std::to_string(DefaultPointSize))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.004f, currentHeight, currentHeight - 0.1f, "Point", (m_RightX - m_LeftX - 0.068f), UpdateModelStatic, this), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.11f, currentHeight - 0.21f, UpdateModelStatic, this), false);
	m_PointDefInputField = m_SubUIElements.size() - 1;

	currentHeight -= 0.26f;

	// Line
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(rightX - 0.35f, rightX - 0.25f, currentHeight, currentHeight - 0.1f, DisplayLineVariables, this, "Variables", std::array<float, 4>{0.8f, 0.8f, 0.8f, 1.0f}, std::array<float, 4>{0.6f, 0.6f, 0.6f, 1.0f}), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.20f, rightX - 0.14f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString("l")), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.13f, rightX - 0.07f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString(std::to_string(DefaultLineWidth))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.004f, currentHeight, currentHeight - 0.1f, "Line", (m_RightX - m_LeftX - 0.068f), UpdateModelStatic, this), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.11f, currentHeight - 0.21f, UpdateModelStatic, this), false);
	m_LineDefInputField = m_SubUIElements.size() - 1;

	currentHeight -= 0.26f;

	// Incidence
	m_ModelTexts.push_back(std::make_shared<Text>("Incidence", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.17f, UpdateModelStatic, this), false);

	currentHeight -= 0.22f;

	// Betweenness
	m_ModelTexts.push_back(std::make_shared<Text>("Betweenness", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.17f, UpdateModelStatic, this), false);

	currentHeight -= 0.22f;

	// Betweenness
	m_ModelTexts.push_back(std::make_shared<Text>("Congruence", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.17, "d = ", 0.05f, UpdateModelStatic, this, 40.0f), false);


	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.4f, bottomY + 0.27f, UpdateModelStatic, this, "Update model"), false);
	m_ModelEndIndex = m_SubUIElements.size() - 1;

	m_SubUIElements.emplace_back(std::make_shared<KeyboardUI>(leftX, rightX, bottomY + 0.24f, bottomY));
	m_SubUIElements.emplace_back(std::make_shared<TabUI>(leftX, rightX, topY, topY - 0.2f, 0, &TabButtonClickedStatic, this));
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.4f, bottomY + 0.27f, UpdateGraphsStatic, this, "Update graphs"));
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
	m_ButtonValue = value;
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
	if (m_ButtonValue == 2)
	{
		for (std::shared_ptr<Text>& text : m_ModelTexts)
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
	const AdvancedString& pointDef{ ((TextInputField*)(m_SubUIElements[m_PointDefInputField].element.get()))->GetText() };
	const AdvancedString& lineDef{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField].element.get()))->GetText() };
	int numPointsIdents{ std::stoi(((TextInputFieldWithDesc*)(m_SubUIElements[m_PointDefInputField - 1].element.get()))->GetText().toString()) };
	int numLineIdents{ std::stoi(((TextInputFieldWithDesc*)(m_SubUIElements[m_LineDefInputField - 1].element.get()))->GetText().toString()) };
	const AdvancedString& pointId{ ((TextInputField*)(m_SubUIElements[m_PointDefInputField - 3].element.get()))->GetText() };
	const AdvancedString& lineId{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField - 3].element.get()))->GetText() };
	Equation pointDefEq({ pointId }, pointDef);
	Equation lineDefEq({ { lineId } }, lineDef);
	std::shared_ptr<Model> model{ Application::Get()->GetModel() };
	Application::Get()->SetModel(numPointsIdents, pointDefEq, numLineIdents, lineDefEq, model->GetIncidenceConstr(), model->GetBetweennessConstr());
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();

	int pointSize = std::stoi(((TextInputField*)m_SubUIElements[m_PointDefInputField - 2].element.get())->GetText().toString());
	int lineWidth = std::stoi(((TextInputField*)m_SubUIElements[m_LineDefInputField - 2].element.get())->GetText().toString());
	Application::Get()->GetRenderer()->GetGraphRenderer()->setLineThickness(lineWidth);
	Application::Get()->GetRenderer()->GetGraphRenderer()->setPointSize(pointSize);

	UpdateGraphs();
}
