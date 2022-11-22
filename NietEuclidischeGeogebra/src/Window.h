#pragma once

struct WindowCreationOptions
{
	std::string name;
	int width, height;
};

struct GLFWwindow;

class Window
{
public:
	Window(const WindowCreationOptions& options);
	~Window();

	std::pair<int, int> GetSize() const;
	const char* GetWindowName() const;

private:
	GLFWwindow* m_Window;
	static bool s_Initialized;
};