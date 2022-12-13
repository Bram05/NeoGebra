// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"

// Entry point
int main()
{
	try
	{
		Application* app{ new Application };
		app->Run();
		delete app;
	}
	catch (const std::exception& e)
	{
		std::cout << "Error! description = " << e.what() << '\n';
	}
	return 0;
}