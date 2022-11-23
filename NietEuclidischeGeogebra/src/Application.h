#pragma once

#include "Window.h"
#include "Renderer.h"

class Application
{
private:
	Application();
	~Application();

public:
	static Application* GetApplication();
	void Run();

	Window* GetWindow() { return m_Window; }
	Renderer* GetRenderer() { return m_Renderer; }

	friend int main();

private:
	static Application* s_Instance;
	Window* m_Window;
	Renderer* m_Renderer;
};