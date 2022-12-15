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
		float newY = Util::ConvertToOpenGLCoordinate(y, false);
		Application::Get()->GetWindowUI()->MouseClicked(newX, newY);
	}
}

static void MouseMovedCallback(int x, int y)
{
	float newX = Util::ConvertToOpenGLCoordinate(x, true);
	float newY = Util::ConvertToOpenGLCoordinate(y, false);
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
	Application::s_Instance = this;
	AssetsFolder = "../../../../NietEuclidischeGeogebra/assets";
	m_Window = new Window(WindowCreationOptions(1080, 720, "Jeroen moet niet zo vervelend doen", MouseClickCallback, TextCallback, MouseMovedCallback, KeyCallback));
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
		std::cout << "\rAverage FPS (over " << g_NumSecondsForFpsAverage << " seconds): " << sum / size;
		m_TimeSinceLastFpsUpdate = 0.0;
	}
	m_LastFrameTime = endTime;
}

Application* Application::Get()
{
	return s_Instance;
}
