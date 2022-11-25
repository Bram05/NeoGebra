// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Renderer.h"

#include <glad/glad.h>
#include <GLFW/glfw3.h>

Renderer::Renderer()
{
	int status = gladLoadGLLoader((GLADloadproc)glfwGetProcAddress);
	if (status == 0)
	{
		throw std::runtime_error("Glad failed to initialize.Make sure your drivers support OpenGL 4.0.");
	}
	std::cout << "Loaded GL version " << glGetString(GL_VERSION) << '\n';
	m_LineRenderer = new LineRenderer;
}

Renderer::~Renderer()
{
	delete m_LineRenderer;
	// I couldn't find cleanup calls for glad
}

void Renderer::AddLine(const Line& line)
{
	
}

void Renderer::BeginRenderPass(float r, float g, float b, float a)
{
	glClearColor(r, g, b, a);
	glClear(GL_COLOR_BUFFER_BIT);

	m_LineRenderer->RenderQueue();
}

void Renderer::Resize(int width, int height)
{
	glViewport(0, 0, width, height);
}

void Renderer::Render(std::shared_ptr<Line> line)
{
	m_LineRenderer->AddToRenderQueue(line);
}
