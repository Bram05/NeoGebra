// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"
#include "Util.h"
#include "Maths/PostulateVerifier.h" // Temporary

#include <GLFW/glfw3.h> // I don't like this

Application* Application::s_Instance = nullptr;

static void MouseClickCallback(int mouseButton, int action, int mods)
{
	if (mouseButton == MouseButton::left && action == Action::pressed)
	{
		auto [x, y] = Application::Get()->GetWindow()->GetMouseLocation();
		float newX = Util::ConvertToOpenGLCoordinate(x, true);
		float newY = -Util::ConvertToOpenGLCoordinate(y, false);
		Application::Get()->GetWindowUI()->MouseClicked(newX, newY);
	}
	if (mouseButton == MouseButton::left && action == Action::released)
	{
		Application::Get()->GetWindowUI()->MouseReleased();
	}
}

static void MouseMovedCallback(int x, int y)
{
	//Util::Timer t("MouseMovedCallback");
	float newX = Util::ConvertToOpenGLCoordinate(x, true);
	float newY = -Util::ConvertToOpenGLCoordinate(y, false);
	Application::Get()->GetWindowUI()->MouseMoved(newX, newY);
}

static void TextCallback(unsigned int codepoint)
{
	Application::Get()->GetWindowUI()->TextInput(codepoint);
}

static void KeyCallback(int key, int scancode, int action, int mods)
{
	if (key == GLFW_KEY_ESCAPE)
	{
		PrintInfo(std::cout << "\nEscape key pressed, closing application\n" << std::flush);
		Application::Get()->GetWindow()->Close();
	}
	else if (key == GLFW_KEY_F11 && action == GLFW_PRESS)
		Application::Get()->GetWindow()->ToggleMaximized();
	else
		Application::Get()->GetWindowUI()->SpecialKeyInput(key, scancode, action, mods);
}

static void ResizeCallback(int width, int height)
{
	Application::Get()->GetWindowUI()->ResizeWindow(width, height);
	Application::Get()->GetRenderer()->Resize(width, height);
	Application::Get()->GetWindowUI()->RenderPass(Application::Get()->GetRenderer());
	Application::Get()->GetRenderer()->RenderQueues();
	Application::Get()->GetWindow()->Update();
}

Application::Application()
{
	Util::Timer::Initialize("times.txt");
	std::atexit(Util::Timer::Terminate);
	Util::Timer t("Creating Application");
	
	VarMap v;
	m_Model = std::make_shared<Model>(v, 0, Equation(AdvancedString("")), 0, Equation(AdvancedString("")), Equation(AdvancedString("")), EquationVector(), EquationVector());

	Application::s_Instance = this;
	m_Window = new Window(WindowCreationOptions(1080, 720, "NeoGeobra", MouseClickCallback, TextCallback, MouseMovedCallback, KeyCallback, ResizeCallback));
	m_Renderer = new Renderer;
	m_WindowUI = new MainWindowUI;
	m_Window->ToggleMaximized();
	PrintInfo(std::cout << "Created application\n\n");
}

Application::~Application()
{
	Util::Timer t("Destroying application");
	delete m_WindowUI;
	delete m_Renderer;
	delete m_Window;
	PrintInfo(std::cout << "Destroyed application\n");
}

void Application::Run()
{
#ifdef TIMING
	double m_LastFrameTime{ glfwGetTime() };
#endif
	while (!m_Window->ShouldClose())
	{
		m_WindowUI->RenderPass(m_Renderer);
		m_Renderer->RenderQueues();
		m_Window->Update();

#ifdef TIMING
		UpdateFrameTimes();
#endif
	}
}

void Application::UpdateFrameTimes()
{
	double endTime{ glfwGetTime() };
	double diff = endTime - m_LastFrameTime;
	double fps = 1 / diff;
	m_TimeSinceLastFpsUpdate += diff;
	m_LastFpss.push(fps);

	if (m_TimeSinceLastFpsUpdate > g_NumSecondsForFpsAverage)
	{
		double sum{ 0.0 };
		int size = m_LastFpss.size();
		while (m_LastFpss.size() != 0)
		{
			sum += m_LastFpss.top();
			m_LastFpss.pop();
		}
		m_WindowUI->SetFPSCounter(sum / size);
		m_TimeSinceLastFpsUpdate = 0.0;
	}
	m_LastFrameTime = endTime;
}

Application* Application::Get()
{
	return s_Instance;
}
