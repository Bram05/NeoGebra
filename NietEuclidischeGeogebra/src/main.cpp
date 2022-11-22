// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"

int main()
{
	try
	{
		Application::s_Instance = new Application;
		Application::s_Instance->Run();
		delete Application::s_Instance;
	}
	catch (const std::exception& e)
	{
		std::cout << "Error! description = " << e.what() << '\n';
	}
	return 0;
}