// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "Window.h"
#include "Renderer.h"

#include "UI/WindowUI.h"

// Number of seconds before the average fps is calculated and the counters are reset
constexpr double g_NumSecondsForFpsAverage = 0.5;

// Main application class
// Owns the window and renderers and updates them every frame
// This class can only be constructed by main, but every part of the code can access it
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

	double m_LastFrameTime{ 0.0 };
	std::stack<double> m_LastFpss;
	double m_TimeSinceLastFpsUpdate{ 0.0 };

	// Updates the fps counters
	void UpdateFrameTimes();
};