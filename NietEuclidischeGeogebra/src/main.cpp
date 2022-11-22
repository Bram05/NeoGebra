// Standard library files are automatically includede from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include <GLFW/glfw3.h>
#include "PostulateVerifier/PostulateVerifier.h"

int main()
{
	if (!glfwInit())
	{
		std::cerr << "Error! GLFW failed to initialize\n";
		return -1;
	}

	GLFWwindow* window{glfwCreateWindow(1080, 720, getValue().c_str(), nullptr, nullptr)};
	glfwMakeContextCurrent(window);

	while (!glfwWindowShouldClose(window))
	{
		glfwPollEvents();
	}
	return 0;
}