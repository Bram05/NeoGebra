// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Window.h"

#include <GLFW/glfw3.h>

#include "Constants.h"
#include "Application.h"

int Window::s_NumWindowsCreated{ 0 };

Window::Window(const WindowCreationOptions& options)
	: m_MouseButtonCallback{ options.mouseButtonCallback }, m_TextCallback{ options.textCallback }, m_MouseMovedCallback{ options.mouseMovedCallback }, m_SpecialKeyCallback{ options.specialKeyCallback }
{
	if (!s_NumWindowsCreated)
	{
		if (!glfwInit())
		{
			throw std::runtime_error("GLFW failed to initialize");
		}
		MouseButton::left = GLFW_MOUSE_BUTTON_LEFT;
		MouseButton::right = GLFW_MOUSE_BUTTON_RIGHT;
		MouseButton::middle = GLFW_MOUSE_BUTTON_MIDDLE;
		Action::pressed = GLFW_PRESS;
		Action::released = GLFW_RELEASE;
		glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
		glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 5);
#ifdef DEBUG
		glfwWindowHint(GLFW_OPENGL_DEBUG_CONTEXT, true);
#endif
	}
	++s_NumWindowsCreated;

	m_Window = glfwCreateWindow(options.width, options.height, options.title.c_str(), nullptr, nullptr);
	glfwMakeContextCurrent(m_Window);

	glfwSetWindowUserPointer(m_Window, this);

	glfwSetMouseButtonCallback(m_Window, [](GLFWwindow* window, int button, int action, int mods) {
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
	if (handledWindow->m_MouseButtonCallback)
		handledWindow->m_MouseButtonCallback(button, action, mods);
		});

	glfwSetCharCallback(m_Window, [](GLFWwindow* window, unsigned int codepoint) {
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
	if (handledWindow->m_TextCallback)
		handledWindow->m_TextCallback(codepoint);
		});

	glfwSetWindowSizeCallback(m_Window, [](GLFWwindow* window, int width, int height) {
		Application::Get()->GetWindowUI()->ResizeWindow(width, height);
	Application::Get()->GetRenderer()->Resize(width, height);
		});

	glfwSetCursorPosCallback(m_Window, [](GLFWwindow* window, double x, double y) {
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
	if (handledWindow->m_MouseMovedCallback)
		handledWindow->m_MouseMovedCallback((int)x, (int)y);
		});

	glfwSetKeyCallback(m_Window, [](GLFWwindow* window, int key, int scancode, int action, int mods) {
		// Only call this callback if it's a special key. Others are handled through the char callback
		if ((mods & GLFW_MOD_CONTROL) == 0 && (mods & GLFW_MOD_ALT) == 0 && key < 255 && std::isprint(key))
		return;
	Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
	if (handledWindow->m_SpecialKeyCallback)
		handledWindow->m_SpecialKeyCallback(key, scancode, action, mods);
		});
}

Window::~Window()
{
	--s_NumWindowsCreated;
	if (!s_NumWindowsCreated)
	{
		glfwDestroyWindow(m_Window);
		glfwTerminate();
	}
}

bool Window::ShouldClose() const
{
	return glfwWindowShouldClose(m_Window);
}

void Window::Close()
{
	glfwSetWindowShouldClose(m_Window, true);
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
	return { width, height };
}

std::pair<int, int> Window::GetMouseLocation() const
{
	double x, y;
	glfwGetCursorPos(m_Window, &x, &y);
	return { x, y };
}

const char* Window::GetClipboardContent() const
{
	return glfwGetClipboardString(NULL);
}
