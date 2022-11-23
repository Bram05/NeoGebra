// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"

#include <GLFW/glfw3.h> // I don't like this

Application* Application::s_Instance = nullptr;

static void MouseClickCallback(int mouseButton, int action, int mods)
{
	std::cout << (mouseButton == MouseButton::left ? "Left" : mouseButton == MouseButton::right ? "Right" : "Middle") << "mouse button was " << (action == Action::pressed ? "pressed" : "released") << '\n';
}

static void KeyCallback(int key, int scancode, int action, int mods)
{
	if (key == GLFW_KEY_ESCAPE)
	{
		Application::GetApplication()->GetWindow()->SetShouldClose(true);
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
	while (!m_Window->ShouldClose())
	{
		m_Renderer->Render(0.5f, 0.3f, 0.2f, 1.0f);
		m_Window->Update();
	}
}

Application* Application::GetApplication()
{
	return s_Instance;
}
