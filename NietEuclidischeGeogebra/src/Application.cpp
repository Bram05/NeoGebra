// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"

#include <GLFW/glfw3.h> // I don't like this

Application* Application::s_Instance = nullptr;
constexpr int numFpsAverage = 60;

static void MouseClickCallback(int mouseButton, int action, int mods)
{
	std::cout << (mouseButton == MouseButton::left ? "Left" : mouseButton == MouseButton::right ? "Right" : "Middle") << "mouse button was " << (action == Action::pressed ? "pressed" : "released") << '\n';
}

static void KeyCallback(int key, int scancode, int action, int mods)
{
	if (key == GLFW_KEY_ESCAPE)
	{
		Application::Get()->GetWindow()->SetShouldClose(true);
	}
}

Application::Application()
{
	AssetsFolder = "NietEuclidischeGeogebra/assets";
	m_Window = new Window(WindowCreationOptions(1080, 720, "Hello World", MouseClickCallback, KeyCallback));
	m_Renderer = new Renderer; // this takes significantly more time but I think it is fine here
}

Application::~Application()
{
	delete m_Renderer;
	delete m_Window;
}

void Application::Run()
{
	double m_LastFrameTime{ glfwGetTime() };
	std::shared_ptr<Line> line{ std::make_shared<Line>(Point(0.2f, 0.2f), Point( - 0.5f, -0.5f))};
	while (!m_Window->ShouldClose())
	{
		m_Renderer->GetLineRenderer()->AddToRenderQueue(line);
		m_Renderer->BeginRenderPass(0.5f, 0.3f, 0.2f, 1.0f);
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
