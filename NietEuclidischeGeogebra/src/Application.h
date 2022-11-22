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

	std::weak_ptr<Window> GetWindow() { return m_Window; }
	std::weak_ptr<Renderer> GetRenderer() { return m_Renderer; }

	friend int main();

private:
	static Application* s_Instance;
	std::shared_ptr<Window> m_Window;
	std::shared_ptr<Renderer> m_Renderer;
};