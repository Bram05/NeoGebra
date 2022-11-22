// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"

Application* Application::s_Instance = nullptr;

Application::Application()
{
	m_Window = std::make_shared<Window>(WindowCreationOptions(1080, 720, "Hello World"));
	m_Renderer = std::shared_ptr<Renderer>(new Renderer); // this takes significantly more time but I think it is fine here
}

Application::~Application()
{
}

void Application::Run()
{
	while (!m_Window->ShouldClose())
	{
		m_Renderer->Update(0.5f, 0.3f, 0.2f, 1.0f);
		m_Window->Update();
	}
}

Application* Application::GetApplication()
{
	return s_Instance;
}
