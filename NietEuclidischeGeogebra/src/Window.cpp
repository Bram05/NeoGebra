// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Window.h"
#include "Window.h"
#include "Window.h"

#include <glad/glad.h>
#include <glfw/glfw3.h>

bool Window::s_Initialized{false};

Window::Window(const WindowCreationOptions& options)
{
	if (s_Initialized)
	{
		throw std::runtime_error("A window was already created");
	}

	if (!glfwInit())
	{
		throw std::runtime_error("GLFW failed to initialize");
	}
	s_Initialized = true;

	m_Window = glfwCreateWindow(options.width, options.height, options.title.c_str(), nullptr, nullptr);
	std::cout << "Created window with width " << options.width << ", height " << options.height << " and title " << options.title << '\n';
	glfwMakeContextCurrent(m_Window);
}

Window::~Window()
{
	glfwDestroyWindow(m_Window);
	glfwTerminate();
}

bool Window::ShouldClose() const
{
	return glfwWindowShouldClose(m_Window);
}

void Window::Update()
{
	glfwPollEvents();
	glfwSwapBuffers(m_Window);
}

std::pair<int, int> Window::GetSize() const
{
	int width, height;
	glfwGetWindowSize(m_Window, &width, &height);
	return {width, height};
}
