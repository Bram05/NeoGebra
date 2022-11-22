#pragma once

struct WindowCreationOptions
{
	int width, height;
	std::string title;
};

struct GLFWwindow;

class Window
{
public:
	Window(const WindowCreationOptions& options);
	~Window();

	bool ShouldClose() const;
	void Update();

	std::pair<int, int> GetSize() const;

private:
	GLFWwindow* m_Window;
	static bool s_Initialized;
};