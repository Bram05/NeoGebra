// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Window.h"

#include <GLFW/glfw3.h>

#include "Constants.h"
#include "Application.h"
#include "Util.h"

int Window::s_NumWindowsCreated{ 0 };

Window::Window(const WindowCreationOptions& options)
	: m_Title{ options.title }, m_MouseButtonCallback{ options.mouseButtonCallback }, m_TextCallback{ options.textCallback }, m_MouseMovedCallback{ options.mouseMovedCallback }, m_SpecialKeyCallback{ options.specialKeyCallback }, m_ResizeCallback{ options.resizeCallback }
{
	if (!s_NumWindowsCreated)
	{
		if (!glfwInit())
		{
			std::cerr << "GLFW failed to initialize\n";
			Util::ExitDueToFailure();
		}
		PrintInfo(std::cout << "GLFW initialized\n");
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

	Util::Timer t("Creating window");
	m_Window = glfwCreateWindow(options.width, options.height, options.title.c_str(), nullptr, nullptr);
	if (!m_Window)
	{
		std::cerr << "GLFW failed to create the window. Please make sure your graphics drivers support at least OpenGL 4.5\n";
		Util::ExitDueToFailure();
	}
	glfwMakeContextCurrent(m_Window);
	glfwSwapInterval(1); // Enable VSync

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
		Window* handledWindow = (Window*)glfwGetWindowUserPointer(window);
	if (handledWindow->m_ResizeCallback)
		handledWindow->m_ResizeCallback(width, height);
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

	PrintInfo(std::cout << "Created window " + options.title << '\n');
}

Window::~Window()
{
	--s_NumWindowsCreated;
	glfwDestroyWindow(m_Window);
	PrintInfo(std::cout << "Destroyed window " + m_Title << '\n');
	if (!s_NumWindowsCreated)
	{
		glfwTerminate();
		PrintInfo(std::cout << "GLFW terminated\n");
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

	Util::Timer t("Finishing all OpenGL calls");
	glFinish();
	t.Stop();

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
	return { (int)x, (int)y };
}

const char* Window::GetClipboardContent() const
{
	return glfwGetClipboardString(NULL);
}

void Window::ToggleMaximized()
{
	if (glfwGetWindowAttrib(m_Window, GLFW_MAXIMIZED))
		glfwRestoreWindow(m_Window);
	else
		glfwMaximizeWindow(m_Window);
}

void Window::Focus()
{
	glfwFocusWindow(m_Window);
}
