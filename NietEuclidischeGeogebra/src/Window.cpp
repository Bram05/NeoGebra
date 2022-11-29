// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Window.h"

#include <glad/glad.h>
#include <glfw/glfw3.h>

#include "Constants.h"
#include "Application.h"

bool Window::s_Initialized{false};

Window::Window(const WindowCreationOptions& options)
	: m_MouseButtonCallback{ options.mouseButtonCallback }, m_KeyCallback{ options.keyCallback }
{
	if (s_Initialized)
	{
		throw std::runtime_error("A window was already created");
	}

	if (!glfwInit())
	{
		throw std::runtime_error("GLFW failed to initialize");
	}
	MouseButton::left = GLFW_MOUSE_BUTTON_LEFT;
	MouseButton::right = GLFW_MOUSE_BUTTON_RIGHT;
	MouseButton::middle = GLFW_MOUSE_BUTTON_MIDDLE;
	Action::pressed = GLFW_PRESS;
	Action::released = GLFW_RELEASE;
	s_Initialized = true;

	glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
	glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
	#ifdef DEBUG
	glfwWindowHint(GLFW_OPENGL_DEBUG_CONTEXT, true);
	#endif

	//glfwWindowHint(GLFW_RESIZABLE, GLFW_FALSE);

	m_Window = glfwCreateWindow(options.width, options.height, options.title.c_str(), nullptr, nullptr);
	std::cout << "Created window with width " << options.width << ", height " << options.height << " and title " << options.title << '\n';
	glfwMakeContextCurrent(m_Window);

	glfwSetWindowUserPointer(m_Window, this);

	glfwSetMouseButtonCallback(m_Window, [](GLFWwindow* window, int button, int action, int mods) {
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
		if (handledWindow->m_MouseButtonCallback)
			handledWindow->m_MouseButtonCallback(button, action, mods);
	});

	glfwSetKeyCallback(m_Window, [](GLFWwindow* window, int key, int scancode, int action, int mods) {
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
		if (handledWindow->m_KeyCallback)
			handledWindow->m_KeyCallback(key, scancode, action, mods);
	});

	glfwSetWindowSizeCallback(m_Window, [](GLFWwindow* window, int width, int height) {
		Application::Get()->GetRenderer()->Resize(width, height);
	});
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

void Window::SetShouldClose(bool val)
{
	glfwSetWindowShouldClose(m_Window, val);
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

std::pair<int, int> Window::GetMouseLocation() const
{
	double x, y;
	glfwGetCursorPos(m_Window, &x, &y);
	return {x, y};
}
