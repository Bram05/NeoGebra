#pragma once

class Window;

typedef void(*MouseButtonCallbackType)(int, int, int);
typedef void(*KeyCallbackType)(int, int, int, int);
typedef void(*ResizeCallbackType)(int, int, int, int);

struct WindowCreationOptions
{
	int width = 1080, height = 720;
	std::string title = "Default title";

	MouseButtonCallbackType mouseButtonCallback = nullptr;
	KeyCallbackType keyCallback = nullptr;
};

struct GLFWwindow;

class Window
{
public:
	Window(const WindowCreationOptions& options = {});
	~Window();

	bool ShouldClose() const;
	void SetShouldClose(bool val);
	void Update();

	std::pair<int, int> GetSize() const;

private:
	GLFWwindow* m_Window;
	static bool s_Initialized;

	MouseButtonCallbackType m_MouseButtonCallback;
	KeyCallbackType m_KeyCallback;
};