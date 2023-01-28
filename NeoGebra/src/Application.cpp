// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"
#include "Util.h"

#include <GLFW/glfw3.h> // I don't like this

Application* Application::s_Instance = nullptr;

static void MouseClickCallback(int mouseButton, int action, int mods)
{
	if (mouseButton == MouseButton::left && action == Action::pressed)
	{
		auto [x, y] = Application::Get()->GetWindow()->GetMouseLocation();
		float newX = Util::ConvertToOpenGLCoordinate(x, true);
		float newY = -Util::ConvertToOpenGLCoordinate(y, false);
		Application::Get()->GetWindowUI()->MouseClicked(newX, newY);
	}
	if (mouseButton == MouseButton::left && action == Action::released)
	{
		Application::Get()->GetWindowUI()->MouseReleased();
	}
}

static void MouseMovedCallback(int x, int y)
{
	//Util::Timer t("MouseMovedCallback");
	float newX = Util::ConvertToOpenGLCoordinate(x, true);
	float newY = -Util::ConvertToOpenGLCoordinate(y, false);
	Application::Get()->GetWindowUI()->MouseMoved(newX, newY);
}

static void TextCallback(unsigned int codepoint)
{
	Application::Get()->GetWindowUI()->TextInput(codepoint);
}

static void KeyCallback(int key, int scancode, int action, int mods)
{
	if (key == GLFW_KEY_ESCAPE)
	{
		PrintInfo(std::cout << "\nEscape key pressed, closing application\n" << std::flush);
		Application::Get()->GetWindow()->Close();
	}
	else if (key == GLFW_KEY_F11 && action == GLFW_PRESS)
		Application::Get()->GetWindow()->ToggleMaximized();
	else
		Application::Get()->GetWindowUI()->SpecialKeyInput(key, scancode, action, mods);
}

static void ResizeCallback(int width, int height)
{
	Application::Get()->GetWindowUI()->ResizeWindow(width, height);
	Application::Get()->GetRenderer()->Resize(width, height);
	Application::Get()->GetWindowUI()->RenderPass(Application::Get()->GetRenderer());
	Application::Get()->GetRenderer()->RenderQueues();
	Application::Get()->GetWindow()->Update();
}

Application::Application()
{
	Util::Timer::Initialize("times.txt");
	std::atexit(Util::Timer::Terminate);
	Util::Timer t("Creating Application");

	VarMap P2variables;
	P2variables.second.push_back({ AdvancedString("d2"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l0^2+l1^2")) });
	P2variables.second.push_back({ AdvancedString("sub"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("~(l.d2) + ~(l.d2-1)")) });
	P2variables.second.push_back({ AdvancedString("r"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("1 / (-2*l.sub) + 0.5 * l.sub")) });

	Equation P2pointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & p0^2 + p1^2 < 1") };
	Equation P2lineDef{ {AdvancedString("l")}, AdvancedString("(x-l0)^2 + (y-l1)^2 = l.r^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1") };
	Equation P2incidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("(p0-l0)^2 + (p1-l1)^2 = l.r^2") };
	//Equation P2incidence{ {"p", "l"}, "lieoncircle(p0, p1, circle(l0, l1, ...))" };
	Equation P2distanceDef{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("acosh(1+(2*((p0-q0)^2 + (p1-q1)^2))/((1-(p0^2+p1^2))(1-(q0^2+q1^2))))") };
	//Equation P2betweenness{ {AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)") };

	//Equation P2customScrollPointX{ {AdvancedString("dx"), AdvancedString("dy")}, AdvancedString("tanh(0.5dx)") };
	//Equation P2customScrollPointY{ {AdvancedString("dx"), AdvancedString("dy")}, AdvancedString("tanh(0.5dy)")};

	m_Model = std::make_shared<Model>(P2variables, 2, P2pointDef, 2, P2lineDef, P2incidence, P2distanceDef);

	Equation circle(AdvancedString("x^2+y^2=1"));
	m_Model->addExtraEquation(circle);
	std::shared_ptr<NELine> l1(new NELine({ 1.25f, 0.0f }, m_Model));
	std::shared_ptr<NEPoint> p1(new NEPoint({ 0.625f,  0.4145780988f }, m_Model, { 255, 0, 0, 255 }));
	std::shared_ptr<NEPoint> p2(new NEPoint({ 0.625f,  -0.4145780988f }, m_Model, { 255, 0, 0, 255 }));
	std::shared_ptr<NEPoint> p3(new NEPoint({ 0.5f,  0.0f }, m_Model, { 255, 0, 0, 255 }));
	std::shared_ptr<NEPoint> p4(new NEPoint({ 0.8434959408f,  0.4145780988f }, m_Model, { 255, 0, 0, 255 }));
	//std::shared_ptr<NEPoint> o(new NEPoint({ 0.0f,  0.0f }, m_Model, { 255, 0, 0, 255 }));
	//std::cout << distance(*p1, *p4);

	Application::s_Instance = this;
	m_Window = new Window(WindowCreationOptions(1080, 720, "NeoGeobra", MouseClickCallback, TextCallback, MouseMovedCallback, KeyCallback, ResizeCallback));
	m_Renderer = new Renderer;
	m_WindowUI = new MainWindowUI;
	PrintInfo(std::cout << "Created application\n\n");
}

Application::~Application()
{
	Util::Timer t("Destroying application");
	delete m_WindowUI;
	delete m_Renderer;
	delete m_Window;
	PrintInfo(std::cout << "Destroyed application\n");
}

void Application::Run()
{
	#ifdef TIMING
	double m_LastFrameTime{ glfwGetTime() };
	#endif
	while (!m_Window->ShouldClose())
	{
		m_WindowUI->RenderPass(m_Renderer);
		m_Renderer->RenderQueues();
		m_Window->Update();

		#ifdef TIMING
		UpdateFrameTimes();
		#endif
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
		m_WindowUI->SetFPSCounter(sum / size);
		m_TimeSinceLastFpsUpdate = 0.0;
	}
	m_LastFrameTime = endTime;
}

Application* Application::Get()
{
	return s_Instance;
}
