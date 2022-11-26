#pragma once

#include "Window.h"
#include "Renderer.h"

#include "UI/WindowUI.h"

constexpr double g_NumSecondsForFpsAverage = 0.5;

class Application
{
private:
	Application();
	~Application();

public:
	static Application* Get();
	void Run();

	Window* GetWindow() { return m_Window; }
	Renderer* GetRenderer() { return m_Renderer; }
	WindowUI* GetWindowUI() { return m_WindowUI; }

	friend int main();

private:
	static Application* s_Instance;
	Window* m_Window;
	Renderer* m_Renderer;
	WindowUI* m_WindowUI;

	double m_LastFrameTime{0.0};
	std::stack<double> m_LastFpss;
	double m_TimeSinceLastFpsUpdate{ 0.0 };

	void UpdateFrameTimes();
};