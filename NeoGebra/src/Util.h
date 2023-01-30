// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "Constants.h"

class ErrorBoxException : public std::exception {};
#define UserInput(...) try { __VA_ARGS__; } catch(ErrorBoxException) {}

namespace Util
{
	// Convert between pixel coordinates and OpenGL coordinates.
	// The difference between the coordinate and value functions are that the coordinates take an actual coordinate,
	// while the value functions take a certain width/height
	// @param num: one part of the coordinates to be converted
	// @param isX: is this part in the x direction
	// @return the converted coordinate
	// OpenGL coordinates are on the interval [-1,1] with the middle of the screen being 0,0
	// This is how coordinates are stored in this program
	// Pixel coordinates are used by GLFW and is the number of pixels from the bottom left of the screen in the x and y direction
	float ConvertToOpenGLCoordinate(int num, bool isX);
	int ConvertToPixelCoordinate(float num, bool isX);
	int ConvertToPixelValue(float num, bool isX);

	void ExitDueToFailure();

#ifdef PRINTINFO
#define PrintInfo(x) x
#else
#define PrintInfo(X)
#endif

	// A class to time how long certain things take
	// This class will be completely empty if timing is disabled
	// The destructor will automatically stop the timer and print the information it is still running
	class Timer
	{
#ifdef TIMING
	public:
		Timer(const std::string& name);
		~Timer();

		static void Initialize(const std::filesystem::path& pathToOutputFile);
		static void Terminate();

		// Stop the timer, print the information to the file and return the time in seconds
		double Stop();

		// Restart the timer with a new name
		// This will only work if the timer is stopped
		void Restart(const std::string& name);

	private:
		std::chrono::time_point<std::chrono::steady_clock> m_Begin;
		std::string m_Name;
		bool m_Running;
		static std::ofstream s_OutputStream;
		static constexpr int s_MaxNameLength{51};
#else
	public:
		Timer(const std::string&) {}

		static void Initialize(const std::filesystem::path& pathToOutputFile) {}
		static void Terminate() {}

		double Stop() { return -1.0f; }
		void Restart(const std::string& name) {}
#endif
	};
}