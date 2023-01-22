// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

class Window;

typedef void(*MouseButtonCallbackType)(int, int, int);
typedef void(*TextCallbackType)(unsigned int);
typedef void(*ResizeCallbackType)(int, int, int, int);
typedef void(*MouseMovedCallbackType)(int, int);
typedef void(*SpecialKeyCallback)(int, int, int, int);

// The options for creating a window
struct WindowCreationOptions
{
	int width = 1080, height = 720;
	std::string title = "NeoGebra";

	MouseButtonCallbackType mouseButtonCallback = nullptr;
	TextCallbackType textCallback = nullptr;
	MouseMovedCallbackType mouseMovedCallback = nullptr;
	SpecialKeyCallback specialKeyCallback = nullptr;
};

struct GLFWwindow;

// A class that represents a GLFW window
class Window
{
public:
	Window(const WindowCreationOptions& options = {});
	~Window();

	// Some getters and setters
	bool ShouldClose() const;
	void Close();
	std::pair<int, int> GetSize() const;
	std::pair<int, int> GetMouseLocation() const;
	const char* GetClipboardContent() const;

	// Update the window (swap buffers and poll GLFW events)
	void Update();

private:
	GLFWwindow* m_Window;
	std::string m_Title;
	static int s_NumWindowsCreated;

	MouseButtonCallbackType m_MouseButtonCallback;
	TextCallbackType m_TextCallback;
	MouseMovedCallbackType m_MouseMovedCallback;
	SpecialKeyCallback m_SpecialKeyCallback;
};