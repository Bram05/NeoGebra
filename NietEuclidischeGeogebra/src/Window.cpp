#include "Window.h"

#include <glad/glad.h>
#include <glfw/glfw3.h>

bool Window::s_Initialized{false};

Window::Window(const WindowCreationOptions& options)
{
	if (s_Initialized)
	{
		std::cerr << "Error! A window was already created.\n";
		throw std::run
	}

	if (!glfwInit())
	{
		std::cerr << "Error! GLFW failed to initialize\n";
		std::exit(-1);
	}

	m_Window = glfwCreateWindow(1080, 720, getValue().c_str(), nullptr, nullptr);
	glfwMakeContextCurrent(m_Window);

	int status = gladLoadGLLoader((GLADloadproc)glfwGetProcAddress);
	if (status == 0)
	{
		std::cerr << "Error! Glad failed to initialize. Make sure your drivers support OpenGL 4.0.\n";
		
	}
	std::cout << "Loaded GL version " << glGetString(GL_VERSION) << '\n';
}

Window::~Window()
{
}

std::pair<int, int> Window::GetSize() const
{
	int x, y;
	glfwGetWindowAttrib()
}

const char* Window::GetWindowName() const
{
	return nullptr;
}
