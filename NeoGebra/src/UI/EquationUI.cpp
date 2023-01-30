// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "EquationUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "KeyboardUI.h"
#include "TabUI.h"
#include "TextInputFieldWithDesc.h"
#include "Window.h"
#include "Constants.h"
#include <GLFW/glfw3.h>
#include "Util.h"
#include "ExtrasWindowUI.h"

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

struct SubWindow
{
	Window* window{ nullptr };
	Renderer* renderer{ nullptr };
	WindowUI* UI{ nullptr };
};

SubWindow g_LineWindow;
SubWindow g_PointWindow;
SubWindow g_ExtrasWindow;

void ResizeCallback(SubWindow window, int width, int height)
{
	window.UI->ResizeWindow(width, height);
	window.renderer->Resize(width, height);
	window.UI->RenderPass(window.renderer);
	window.renderer->RenderQueues();
	window.window->Update();
}
static void PointResizeCallback(int width, int height) { ResizeCallback(g_PointWindow, width, height); }
static void LineResizeCallback(int width, int height) { ResizeCallback(g_LineWindow, width, height); }
static void ExtrasResizeCallback(int width, int height) { ResizeCallback(g_ExtrasWindow, width, height); }

static void MouseClickCallback(SubWindow window, int mouseButton, int action, int mods)
{
	if (mouseButton == MouseButton::left && action == Action::pressed)
	{
		auto [x, y] = window.window->GetMouseLocation();
		auto [width, height] = window.window->GetSize();
		float newX = 2 * (float)x / width - 1.0f;
		float newY = -(2 * (float)y / height - 1.0f);
		window.UI->MouseClicked(newX, newY);
	}
	if (mouseButton == MouseButton::left && action == Action::released)
	{
		window.UI->MouseReleased();
	}
}
static void PointMouseClickCallback(int mousebutton, int action, int mods) { MouseClickCallback(g_PointWindow, mousebutton, action, mods); }
static void LineMouseClickCallback(int mousebutton, int action, int mods) { MouseClickCallback(g_LineWindow, mousebutton, action, mods); }
static void ExtrasMouseClickCallback(int mousebutton, int action, int mods) { MouseClickCallback(g_ExtrasWindow, mousebutton, action, mods); }

static void MouseMovedCallback(SubWindow window, int x, int y)
{
	//Util::Timer t("MouseMovedCallback");
	auto [width, height] = window.window->GetSize();
	float newX = 2 * (float)x / width - 1.0f;
	float newY = -(2 * (float)y / height - 1.0f);
	window.UI->MouseMoved(newX, newY);
}
static void PointMouseMovedCallback(int x, int y) { MouseMovedCallback(g_PointWindow, x, y); }
static void LineMouseMovedCallback(int x, int y) { MouseMovedCallback(g_LineWindow, x, y); }
static void ExtrasMouseMovedCallback(int x, int y) { MouseMovedCallback(g_ExtrasWindow, x, y); }

static void TextCallback(SubWindow window, unsigned int codepoint)
{
	window.UI->TextInput(codepoint);
}
static void PointTextCallback(unsigned int codepoint) { TextCallback(g_PointWindow, codepoint); }
static void LineTextCallback(unsigned int codepoint) { TextCallback(g_LineWindow, codepoint); }
static void ExtrasTextCallback(unsigned int codepoint) { TextCallback(g_ExtrasWindow, codepoint); }

static void KeyCallback(SubWindow window, int key, int scancode, int action, int mods)
{
	if (key == GLFW_KEY_ESCAPE)
	{
		PrintInfo(std::cout << "\nEscape key pressed, closing this window\n" << std::flush);
		window.window->Close();
	}
	else if (key == GLFW_KEY_F11 && action == GLFW_PRESS)
		window.window->ToggleMaximized();
	else
		window.UI->SpecialKeyInput(key, scancode, action, mods);
}
static void PointKeyCallback(int key, int scancode, int action, int mods) { KeyCallback(g_PointWindow, key, scancode, action, mods); }
static void LineKeyCallback(int key, int scancode, int action, int mods) { KeyCallback(g_LineWindow, key, scancode, action, mods); }
static void ExtrasKeyCallback(int key, int scancode, int action, int mods) { KeyCallback(g_ExtrasWindow, key, scancode, action, mods); }

static void ManagePointVariableWindow(EquationUI* base)
{
	// Technically Window creation and destruction must happen on the main thread, but this seems to work
	g_PointWindow.window = new Window(WindowCreationOptions(800, 400, "Point Variables", PointMouseClickCallback, PointTextCallback, PointMouseMovedCallback, PointKeyCallback, PointResizeCallback));

	// TODO: by doing this, we are reloading the font which is inefficient, but it needs a texture which has to be created on this thread
	g_PointWindow.renderer = new Renderer;
	g_PointWindow.UI = new VariableWindowUI(&base->m_Variables.first, g_PointWindow.window);

	while (!g_PointWindow.window->ShouldClose())
	{
		glClearColor(0.5f, 0.0f, 0.5f, 1.0f);
		glClear(GL_COLOR_BUFFER_BIT);

		g_PointWindow.UI->RenderPass(g_PointWindow.renderer);
		g_PointWindow.renderer->RenderQueues();

		g_PointWindow.window->Update();
	}
	delete g_PointWindow.renderer;
	g_PointWindow.renderer = nullptr;
	delete g_PointWindow.window;
	g_PointWindow.window = nullptr;
}

static void ManageLineVariableWindow(EquationUI* base)
{
	// Technically Window creation and destruction must happen on the main thread, but this seems to work
	g_LineWindow.window = new Window(WindowCreationOptions(800, 400, "Line Variables", LineMouseClickCallback, LineTextCallback, LineMouseMovedCallback, LineKeyCallback, LineResizeCallback));

	// TODO: by doing this, we are reloading the font which is inefficient, but it needs a texture which has to be created on this thread
	g_LineWindow.renderer = new Renderer;
	g_LineWindow.UI = new VariableWindowUI(&base->m_Variables.second, g_LineWindow.window);

	while (!g_LineWindow.window->ShouldClose())
	{
		glClearColor(0.5f, 0.0f, 0.5f, 1.0f);
		glClear(GL_COLOR_BUFFER_BIT);

		g_LineWindow.UI->RenderPass(g_LineWindow.renderer);
		g_LineWindow.renderer->RenderQueues();

		g_LineWindow.window->Update();
	}
	delete g_LineWindow.renderer;
	g_LineWindow.renderer = nullptr;
	delete g_LineWindow.window;
	g_LineWindow.window = nullptr;
}

static void ManageExtrasWindow(EquationUI* base)
{
	// Technically Window creation and destruction must happen on the main thread, but this seems to work
	g_ExtrasWindow.window = new Window(WindowCreationOptions(800, 400, "Extra Equations", ExtrasMouseClickCallback, ExtrasTextCallback, ExtrasMouseMovedCallback, ExtrasKeyCallback, ExtrasResizeCallback));

	// TODO: by doing this, we are reloading the font which is inefficient, but it needs a texture which has to be created on this thread
	g_ExtrasWindow.renderer = new Renderer;
	g_ExtrasWindow.UI = new ExtrasWindowUI(&base->m_ExtraEquations, g_ExtrasWindow.window);

	while (!g_ExtrasWindow.window->ShouldClose())
	{
		glClearColor(0.5f, 0.0f, 0.5f, 1.0f);
		glClear(GL_COLOR_BUFFER_BIT);

		g_ExtrasWindow.UI->RenderPass(g_ExtrasWindow.renderer);
		g_ExtrasWindow.renderer->RenderQueues();

		g_ExtrasWindow.window->Update();
	}
	delete g_ExtrasWindow.renderer;
	g_ExtrasWindow.renderer = nullptr;
	delete g_ExtrasWindow.window;
	g_ExtrasWindow.window = nullptr;
}

static void DisplayPointVariables(void* obj)
{
	if (!g_PointWindow.window)
	{
		std::thread(ManagePointVariableWindow, (EquationUI*)obj).detach();
	}
	else
		g_PointWindow.window->Focus();
}

static void DisplayLineVariables(void* obj)
{
	if (!g_LineWindow.window)
	{
		std::thread(ManageLineVariableWindow, (EquationUI*)obj).detach();
	}
	else
		g_LineWindow.window->Focus();
}

static void DisplayExtrasVariables(void* obj)
{
	if (!g_ExtrasWindow.window)
	{
		std::thread(ManageExtrasWindow, (EquationUI*)obj).detach();
	}
	else
		g_ExtrasWindow.window->Focus();
}
constexpr int NumInputFields{ 8 }, DefaultPointSize{ 10 }, DefaultLineWidth{ 3 };

EquationUI::EquationUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "EquationUI")
{
	AdvancedString lineDef, pointDef, incidenceDef, congruenceDef, betweennessDef, lineFromPoints, pointFromLines;
	unsigned int numLineIds, numPointIds;
	std::shared_ptr<Model> model = Application::Get()->GetModel();
	if (model)
	{
		lineDef = model->GetLineDef().m_EquationString;
		pointDef = model->GetPointDef().m_EquationString;
		incidenceDef = model->GetIncidenceConstr().m_EquationString;
		congruenceDef = model->GetDistanceDef().m_EquationString;
		betweennessDef = model->GetBetweennessConstr().m_EquationString;
		numLineIds = model->GetNumLineIdentifiers();
		numPointIds = model->GetNumPointIdentifiers();

		bool first = true;
		for (const Equation& e : model->GetLineFromPoints())
		{
			if (!first)
				lineFromPoints += AdvancedString("; ");
			lineFromPoints += e.m_EquationString;
			first = false;
		}

		first = true;
		for (const Equation& e : model->GetPointFromLines())
		{
			if (!first)
				pointFromLines += AdvancedString("; ");
			pointFromLines += e.m_EquationString;
			first = false;
		}

		m_Variables = model->GetVarMap();
	}

	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	m_PointsIndexBegin = m_SubUIElements.size();
	float currentHeight = topY - 0.2f;
	for (int i{ 0 }; i < NumInputFields; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX - 0.01f, currentHeight, currentHeight - 0.07f, AdvancedString(std::to_string(i) + ":"), 0.04f, UpdateGraphsStatic, this));
		currentHeight -= 0.1f;
	}

	m_PointText = std::make_shared<Text>("Lines from points (if defined):", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, 40.0f);
	currentHeight -= 0.10f;

	for (int i{ 0 }; i < 4; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight, currentHeight - 0.07f, UpdateModelStatic, this));
		currentHeight -= 0.1f;
	}

	m_LinesIndexBegin = m_SubUIElements.size();
	currentHeight = topY - 0.2f;
	for (int i{ 0 }; i < NumInputFields; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX, rightX - 0.01f, currentHeight, currentHeight - 0.07f, AdvancedString(std::to_string(i) + ":"), 0.04f, UpdateGraphsStatic, this));
		currentHeight -= 0.1f;
	}

	m_LineText = std::make_shared<Text>("Intersection of two lines (if defined):", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, 40.0f);
	currentHeight -= 0.10f;

	for (int i{ 0 }; i < 4; ++i)
	{
		m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight, currentHeight - 0.07f, UpdateModelStatic, this));
		currentHeight -= 0.1f;
	}

	Application::Get()->GetRenderer()->GetGraphRenderer()->setPointSize(DefaultPointSize);
	Application::Get()->GetRenderer()->GetGraphRenderer()->setLineThickness(DefaultLineWidth);

	currentHeight = topY - 0.2f;

	m_ModelBeginIndex = m_SubUIElements.size();
	// Point
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(rightX - 0.35f, rightX - 0.25f, currentHeight, currentHeight - 0.1f, DisplayPointVariables, this, "Variables", std::array<float, 4>{0.8f, 0.8f, 0.8f, 1.0f}, std::array<float, 4>{0.6f, 0.6f, 0.6f, 1.0f}), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.20f, rightX - 0.14f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString("p")), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.13f, rightX - 0.07f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString(std::to_string(DefaultPointSize))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.004f, currentHeight, currentHeight - 0.1f, AdvancedString("Point"), (m_RightX - m_LeftX - 0.068f), UpdateModelStatic, this, 43.0f, AdvancedString(std::to_string(numPointIds))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.11f, currentHeight - 0.18f, UpdateModelStatic, this, pointDef), false);
	m_PointDefInputField = m_SubUIElements.size() - 1;

	currentHeight -= 0.22f;

	// Line
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(rightX - 0.35f, rightX - 0.25f, currentHeight, currentHeight - 0.1f, DisplayLineVariables, this, "Variables", std::array<float, 4>{0.8f, 0.8f, 0.8f, 1.0f}, std::array<float, 4>{0.6f, 0.6f, 0.6f, 1.0f}), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.20f, rightX - 0.14f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString("l")), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(rightX - 0.13f, rightX - 0.07f, currentHeight, currentHeight - 0.1f, UpdateModelStatic, this, AdvancedString(std::to_string(DefaultLineWidth))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.004f, currentHeight, currentHeight - 0.1f, AdvancedString("Line"), (m_RightX - m_LeftX - 0.068f), UpdateModelStatic, this, 43.0f, AdvancedString(std::to_string(numLineIds))), false);
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.11f, currentHeight - 0.18f, UpdateModelStatic, this, lineDef), false);
	m_LineDefInputField = m_SubUIElements.size() - 1;

	currentHeight -= 0.22f;

	// Incidence
	m_ModelTexts.push_back(std::make_shared<Text>("Incidence", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.14f, UpdateModelStatic, this, incidenceDef), false);

	currentHeight -= 0.18f;

	// Betweenness
	m_ModelTexts.push_back(std::make_shared<Text>("Betweenness", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.14f, UpdateModelStatic, this, betweennessDef), false);

	currentHeight -= 0.18f;

	// Congruence
	m_ModelTexts.push_back(std::make_shared<Text>("Congruence", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputFieldWithDesc>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.14f, AdvancedString("d = "), 0.05f, UpdateModelStatic, this, 40.0f, congruenceDef), false);

	currentHeight -= 0.18f;

	// New Line
	m_ModelTexts.push_back(std::make_shared<Text>("Line From Two Points (may not be required)", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.14f, UpdateModelStatic, this, lineFromPoints), false);

	currentHeight -= 0.18f;

	// Points from line
	m_ModelTexts.push_back(std::make_shared<Text>("Intersection Of Two Lines (may not be required)", leftX + 0.01f, rightX - 0.01f, currentHeight - 0.05f, 40.0f));
	m_SubUIElements.emplace_back(std::make_shared<TextInputField>(leftX + 0.01f, rightX - 0.01f, currentHeight - 0.07f, currentHeight - 0.14f, UpdateModelStatic, this, pointFromLines), false);

	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.01f, leftX + 0.16f, bottomY + 0.36f, bottomY + 0.27f, DisplayExtrasVariables, this, "Extra Equations", std::array<float, 4>{0.8f, 0.8f, 0.8f, 1.0f}, std::array<float, 4>{0.6f, 0.6f, 0.6f, 1.0f}), false);
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.20f, rightX - 0.05f, bottomY + 0.36f, bottomY + 0.27f, UpdateModelStatic, this, "Update model"), false);
	m_ModelEndIndex = m_SubUIElements.size() - 1;

	m_SubUIElements.emplace_back(std::make_shared<KeyboardUI>(leftX, rightX, bottomY + 0.24f, bottomY));
	m_SubUIElements.emplace_back(std::make_shared<TabUI>(leftX, rightX, topY, topY - 0.2f, m_ButtonValue, &TabButtonClickedStatic, this));
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.02f, rightX - 0.02f, bottomY + 0.4f, bottomY + 0.27f, UpdateGraphsStatic, this, "Update graphs"));
	m_UpdateGraphsButton = m_SubUIElements.size() - 1;

	TabButtonClicked(m_ButtonValue);
}

EquationUI::~EquationUI()
{
	// TODO: look into why the extra windows aren't properly destructed after glfwTerminate()
	using namespace std::chrono_literals;
	if (g_LineWindow.window)
	{
		g_LineWindow.window->Close();
		while (g_LineWindow.window)
			std::this_thread::sleep_for(3ms);
	}

	if (g_PointWindow.window)
	{
		g_PointWindow.window->Close();
		while (g_PointWindow.window)
			std::this_thread::sleep_for(3ms);
	}

	if (g_ExtrasWindow.window)
	{
		g_ExtrasWindow.window->Close();
		while (g_ExtrasWindow.window)
			std::this_thread::sleep_for(3ms);
	}
}

void EquationUI::TabButtonClicked(int value)
{
	for (int i{ m_PointsIndexBegin }; i < m_PointsIndexBegin + NumInputFields + 4; i++)
	{
		m_SubUIElements[i].shouldRender = value == 0;
	}
	for (int i{ m_LinesIndexBegin }; i < m_LinesIndexBegin + NumInputFields + 4; i++)
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
	else if (m_ButtonValue == 1)
	{
		r->AddToRenderQueue(m_LineText);
	}
	else
	{
		r->AddToRenderQueue(m_PointText);
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
	m_NEPoints.clear();
	m_NELines.clear();
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();
	Application::Get()->GetModel()->getElements().clear();
	for (int i{ m_PointsIndexBegin }; i < m_PointsIndexBegin + NumInputFields; ++i)
	{
		const AdvancedString& text{ ((TextInputFieldWithDesc*)(m_SubUIElements[i].element.get()))->GetText() };
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
			m_NEPoints.push_back(std::make_shared<NEPoint>(identifiers, Application::Get()->GetModel(), RGBColour{ 255, 0, 0, 255 }, false));
		}
			UserInput(new NEPoint(identifiers, Application::Get()->GetModel(), { 255, 0, 0, 255 }, false));
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
		const AdvancedString& text{ ((TextInputFieldWithDesc*)(m_SubUIElements[i].element.get()))->GetText() };
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
			m_NELines.push_back(std::make_shared<NELine>(identifiers, Application::Get()->GetModel(), RGBColour{ 255, 255, 0, 255 }, false));
			UserInput(new NELine(identifiers, Application::Get()->GetModel(), { 255, 255, 0, 255 }, false));
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
	const AdvancedString& incidenceDef{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField + 1].element.get()))->GetText() };
	const AdvancedString& betweennessDef{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField + 2].element.get()))->GetText() };
	const AdvancedString& congruenceDef{ ((TextInputFieldWithDesc*)(m_SubUIElements[m_LineDefInputField + 3].element.get()))->GetText() };
	const AdvancedString& lineFromPoints{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField + 4].element.get()))->GetText() };
	const AdvancedString& pointFromLines{ ((TextInputField*)(m_SubUIElements[m_LineDefInputField + 5].element.get()))->GetText() };

	EquationVector lineFromPointsVec;
	unsigned int begin{ 0 };
	for (int i{ 0 }; i < lineFromPoints.size(); ++i)
	{
		if (lineFromPoints[i] == ';')
		{
			lineFromPointsVec.emplace_back(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, lineFromPoints.substr(begin, i - begin));
			begin = i+1;
		}
	}
	lineFromPointsVec.emplace_back(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, lineFromPoints.substr(begin, lineFromPoints.size() - begin));

	EquationVector pointFromLinesVec;
	begin = 0;
	for (int i{ 0 }; i < pointFromLines.size(); ++i)
	{
		if (pointFromLines[i] == ';')
		{
			pointFromLinesVec.emplace_back(std::vector<AdvancedString>{AdvancedString("l"), AdvancedString("k")}, pointFromLines.substr(begin, i - begin));
			begin = i + 1;
		}
	}
	pointFromLinesVec.emplace_back(std::vector<AdvancedString>{AdvancedString("l"), AdvancedString("l")}, pointFromLines.substr(begin, pointFromLines.size() - begin));

	Equation pointDefEq({ pointId }, pointDef);
	Equation lineDefEq({ { lineId } }, lineDef);
	Equation incidenceDefEq{ {pointId, lineId}, incidenceDef };

	VarMap correctMap;
	for (unsigned int i{ 0 }; i < m_Variables.first.size(); ++i)
	{
		correctMap.first.emplace_back(m_Variables.first[i].first, std::make_shared<Equation>(std::vector<AdvancedString>{pointId}, m_Variables.first[i].second->m_EquationString));
	}
	for (unsigned int i{ 0 }; i < m_Variables.second.size(); ++i)
	{
		correctMap.second.emplace_back(m_Variables.second[i].first, std::make_shared<Equation>(std::vector<AdvancedString>{lineId}, m_Variables.second[i].second->m_EquationString));
	}

	Application::Get()->SetModel(correctMap, numPointsIdents, pointDefEq, numLineIdents, lineDefEq, incidenceDefEq, congruenceDef, betweennessDef, lineFromPointsVec, pointFromLinesVec);
	for (auto& eq : m_ExtraEquations)
	{
		Application::Get()->GetModel()->addExtraEquation(eq);
	}
	Application::Get()->GetWindowUI()->GetGraphUI()->DeleteGraphs();

	int pointSize = std::stoi(((TextInputField*)m_SubUIElements[m_PointDefInputField - 2].element.get())->GetText().toString());
	int lineWidth = std::stoi(((TextInputField*)m_SubUIElements[m_LineDefInputField - 2].element.get())->GetText().toString());
	Application::Get()->GetRenderer()->GetGraphRenderer()->setLineThickness(lineWidth);
	Application::Get()->GetRenderer()->GetGraphRenderer()->setPointSize(pointSize);

	UpdateGraphs();

	for (int i{ m_PointsIndexBegin + NumInputFields }; i < m_PointsIndexBegin + NumInputFields + 4; ++i)
	{
		TextInputField* field = (TextInputField*)m_SubUIElements[i].element.get();
		const AdvancedString& text = field->GetText();
		if (text.empty())
			continue;
		auto it = text.toString().find(',');
		if (it == std::string::npos)
		{
			Application::Get()->GetWindowUI()->DisplayError("Line from points: " + text.toString() + " does not contain a comma. You need to specify two points separated by a comma.");
		}
		else
		{
			const std::shared_ptr<NEPoint>& p1 = m_NEPoints[std::stoi(text.substr(0, it).toString())];
			const std::shared_ptr<NEPoint>& p2 = m_NEPoints[std::stoi(text.substr(it + 1, text.size() - it - 1).toString())];
			Application::Get()->GetModel()->lineFromPoints(*p1, *p2);
		}
	}

	for (int i{ m_LinesIndexBegin + NumInputFields }; i < m_LinesIndexBegin + NumInputFields + 4; ++i)
	{
		TextInputField* field = (TextInputField*)m_SubUIElements[i].element.get();
		const AdvancedString& text = field->GetText();
		if (text.empty())
			continue;
		auto it = text.toString().find(',');
		if (it == std::string::npos)
		{
			Application::Get()->GetWindowUI()->DisplayError("Point from lines: " + text.toString() + " does not contain a comma. You need to specify two points separated by a comma.");
		}
		else
		{
			const std::shared_ptr<NELine>& l1 = m_NELines[std::stoi(text.substr(0, it).toString())];
			const std::shared_ptr<NELine>& l2 = m_NELines[std::stoi(text.substr(it + 1, text.size() - it - 1).toString())];
			Application::Get()->GetModel()->pointFromLines(*l1, *l2);
		}
	}
	Application::Get()->GetWindowUI()->UpdateGraphUI();

}
