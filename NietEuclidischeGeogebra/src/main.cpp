// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"

// Entry point
int main()
{

	new Application;
	Application::s_Instance->Run();
	delete Application::s_Instance;
	
	return 0;
}