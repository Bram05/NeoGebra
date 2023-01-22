// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Renderer.h"

#include <glad/glad.h>
#include <GLFW/glfw3.h>

#include "Application.h"
#include "Constants.h"
#include "Util.h"

static bool s_PrintedMessageThisFrame = false;

static void APIENTRY debugMessageCallback(GLenum source, GLenum type, GLuint id, GLenum severity, GLsizei length, const GLchar* message, const void*)
{
	if (id == 131169 || id == 131185 || id == 131218 || id == 131204) return;

	s_PrintedMessageThisFrame = true;
	std::cerr << "-------------Debug message from OpenGL-------------\n";
	std::cerr << "ID: " << id << ", message: " << message << '\n';

	switch (source)
	{
	case GL_DEBUG_SOURCE_API: std::cerr << "Source: call to OpenGL API\n"; break;
	case GL_DEBUG_SOURCE_WINDOW_SYSTEM: std::cerr << "Source: call to window system API\n"; break;
	case GL_DEBUG_SOURCE_SHADER_COMPILER: std::cerr << "Source: shader compiler\n"; break;
	case GL_DEBUG_SOURCE_THIRD_PARTY: std::cerr << "Source: an application associated with OpenGL\n"; break;
	case GL_DEBUG_SOURCE_APPLICATION: std::cerr << "Source: our application\n"; break;
	case GL_DEBUG_SOURCE_OTHER: std::cerr << "Source: something not in the OpenGL list\n"; break;
	default: std::cerr << "Source is not in our list\n";
	}

	switch (type)
	{
	case GL_DEBUG_TYPE_ERROR: std::cerr << "Type: an error\n"; break;
	case GL_DEBUG_TYPE_DEPRECATED_BEHAVIOR: std::cerr << "Type: deprecated behaviour\n"; break;
	case GL_DEBUG_TYPE_UNDEFINED_BEHAVIOR: std::cerr << "Type: undefined behaviour\n"; break;
	case GL_DEBUG_TYPE_PORTABILITY: std::cerr << "Type: usage that is not portable\n"; break;
	case GL_DEBUG_TYPE_PERFORMANCE: std::cerr << "Type: perfomence issue\n"; break;
	case GL_DEBUG_TYPE_MARKER: std::cerr << "Type: command stream annotation\n"; break;
	case GL_DEBUG_TYPE_PUSH_GROUP: std::cerr << "Type: group push\n"; break;
	case GL_DEBUG_TYPE_POP_GROUP: std::cerr << "Type: group pop\n"; break;
	case GL_DEBUG_TYPE_OTHER: std::cerr << "Type: something not in the OpenGL list\n"; break;
	default: std::cerr << "Type is not in our list\n";
	}

	switch (severity)
	{
	case GL_DEBUG_SEVERITY_HIGH: std::cerr << "Severity: High (errors or highly-dangerous undefined behaviour)\n"; break;
	case GL_DEBUG_SEVERITY_MEDIUM: std::cerr << "Severity: Medium ((big performance) warnings or deprecated functionality)\n"; break;
	case GL_DEBUG_SEVERITY_LOW: std::cerr << "Severity: Low (redundant state change performance warning or unimported undefined behaviour)\n"; break;
	case GL_DEBUG_SEVERITY_NOTIFICATION: std::cerr << "Severity: Notification (anything other than error or performace issue)\n"; break;
	}
	std::cerr << "-------------End of debug message------------------\n";

#ifdef WIN32
#ifdef DEBUG
	__debugbreak();
#endif
#endif
}

Renderer::Renderer()
{
	int status = gladLoadGLLoader((GLADloadproc)glfwGetProcAddress);
	if (status == 0)
	{
		throw std::runtime_error("Glad failed to initialize. Please make sure your graphics drivers support at least OpenGL 4.5");
	}
	PrintInfo(std::cout << "Loaded GL version " << glGetString(GL_VERSION) << '\n');

#ifdef DEBUG
	int flags;
	glGetIntegerv(GL_CONTEXT_FLAGS, &flags);
	if (!(flags & GL_CONTEXT_FLAG_DEBUG_BIT))
	{
		std::cerr << "Failed to create OpenGL debug context. No error messages will be created from OpenGL!\n";
	}
	else
	{
		glEnable(GL_DEBUG_OUTPUT);
		glEnable(GL_DEBUG_OUTPUT_SYNCHRONOUS);
		glDebugMessageCallback(debugMessageCallback, nullptr);
		glDebugMessageControl(GL_DONT_CARE, GL_DONT_CARE, GL_DONT_CARE, 0, nullptr, true);
	}
#endif

	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

	m_LineRenderer = new LineRenderer;
	m_SquareRenderer = new SquareRenderer;
	m_GraphRenderer = new GraphRenderer;
	m_TextRenderer = new TextRenderer("defaultFont");
}

Renderer::~Renderer()
{
	delete m_LineRenderer;
	delete m_SquareRenderer;
	delete m_GraphRenderer;
	delete m_TextRenderer;
	// I couldn't find cleanup calls for glad
	PrintInfo(std::cout << "Destroyed all renderers\n");
}

void Renderer::RenderQueues()
{
#ifdef DEBUG
	if (glIsEnabled(GL_BLEND) == GL_FALSE)
		throw std::runtime_error("Waarschijnlijk heeft Jeroen blending weer uitgezet ofzo");
#endif
	glClearColor(1.0f, 1.0f, 1.0f, 1.0f);
	glClear(GL_COLOR_BUFFER_BIT);

	m_SquareRenderer->RenderQueue();
	m_LineRenderer->RenderQueue();
	m_GraphRenderer->RenderQueue();
	m_TextRenderer->RenderQueue();
#ifdef DEBUG
	// Prevent spamming messages each frame by turning the messages off after a frame in which one was printed
	if (s_PrintedMessageThisFrame)
	{
		glDisable(GL_DEBUG_OUTPUT);
	}
#endif
}

void Renderer::Resize(int width, int height)
{
	glViewport(0, 0, width, height);
	Application::Get()->GetWindowUI()->RenderPass(this);
	RenderQueues();
	Application::Get()->GetWindow()->Update();
}

void Renderer::AddToRenderQueue(const std::shared_ptr<Line>& line)
{
	m_LineRenderer->AddToRenderQueue(line);
}

void Renderer::AddToRenderQueue(const std::shared_ptr<Square>& square)
{
	m_SquareRenderer->AddToRenderQueue(square);
}

void Renderer::AddToRenderQueue(const std::shared_ptr<Text>& m_Text)
{
	m_TextRenderer->AddToRenderQueue(m_Text);
}

void Renderer::AddToRenderQueue(const std::shared_ptr<Graph>& graph)
{
	m_GraphRenderer->AddToRenderQueue(graph);
}
