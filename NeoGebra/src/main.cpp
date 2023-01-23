// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

#include "Application.h"
#include "Constants.h"

// Entry point
int main()
{
	Application* app{ new Application };
	app->Run();
	delete app;
	
	#ifdef PRINTINFO
	std::cin.get();
	#endif
	return 0;
}