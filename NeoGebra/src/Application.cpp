// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"
#include "Util.h"

#include <GLFW/glfw3.h> // I don't like this

Application* Application::s_Instance = nullptr;
constexpr int numFpsAverage = 60;

static void MouseClickCallback(int mouseButton, int action, int mods)
{
	//std::cout << (mouseButton == MouseButton::left ? "Left" : mouseButton == MouseButton::right ? "Right" : "Middle")
		//<< "mouse button was " << (action == Action::pressed ? "pressed" : "released") << '\n';
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
		std::cout << "\nEscape key pressed, closing application\n" << std::flush;
		Application::Get()->GetWindow()->Close();
	}
	Application::Get()->GetWindowUI()->SpecialKeyInput(key, scancode, action, mods);
}

Application::Application()
{
	Equation P2pointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & p0^2 + p1^2 < 1") };
	Equation P2lineDef{ {AdvancedString("l")}, AdvancedString("(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1") };
	Equation P2incidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2") };
	//Equation P2incidence{ {"p", "l"}, "lieoncircle(p0, p1, circle(l0, l1, ...))" };
	Equation P2betweenness{ {AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)") };

	m_Model = std::make_shared<Model>(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness);

	std::shared_ptr<NELine> l1(new NELine({ 1.25, 0 }, m_Model));
	std::shared_ptr<NEPoint> p1(new NEPoint({ 0.625,  0.4145780988 }, m_Model, { 255, 0, 0, 255 }));


	Application::s_Instance = this;
	m_Window = new Window(WindowCreationOptions(1080, 720, "NeoGeobra", MouseClickCallback, TextCallback, MouseMovedCallback, KeyCallback));
	m_Renderer = new Renderer;
	m_WindowUI = new WindowUI;
}

Application::~Application()
{
	delete m_WindowUI;
	delete m_Renderer;
	delete m_Window;
}

void Application::Run()
{
	double m_LastFrameTime{ glfwGetTime() };
	while (!m_Window->ShouldClose())
	{
		m_WindowUI->RenderPass(m_Renderer);
		m_Renderer->RenderQueues();
		m_Window->Update();

		UpdateFrameTimes();
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
		std::cout << "\rAverage FPS (over " << g_NumSecondsForFpsAverage << " seconds): " << sum / size << std::flush;
		m_TimeSinceLastFpsUpdate = 0.0;
	}
	m_LastFrameTime = endTime;
}

Application* Application::Get()
{
	return s_Instance;
}
