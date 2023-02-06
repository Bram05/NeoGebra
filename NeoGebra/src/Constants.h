// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html

// This file contains the constants used
#pragma once

// Some constants
namespace MouseButton
{
	inline int left, right, middle;
}

namespace Action
{
	inline int pressed, released;
}

// The absolute path to the assets folder
// This will be set by cmake when the file is copied
#define AssetsFolder std::filesystem::path("assets")

#ifdef DEBUG
// This defines that debug some info is printed
#define PRINTINFO
#endif
// This defines if all the timers should be activated
//#define TIMING