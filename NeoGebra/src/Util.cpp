// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "Util.h"

#include "Application.h"
#include "Constants.h"

namespace Util
{

	float ConvertToOpenGLCoordinate(int num, bool isX)
	{
		auto [width, height] = Application::Get()->GetWindow()->GetSize();
		if (isX)
		{
			return 2 * (((float)num / width) - 0.5);
		}
		else
		{
			return 2 * (((float)num / height) - 0.5);
		}
	}

	int ConvertToPixelCoordinate(float coor, bool isX)
	{
		auto [width, height] = Application::Get()->GetWindow()->GetSize();
		if (isX)
		{
			return ((coor / 2) + 0.5f) * width;
		}
		else
		{
			return ((coor / 2) + 0.5f) * height;
		}
	}

#ifdef TIMING
	std::ofstream Timer::s_OutputStream;

	Timer::Timer(const std::string& name)
		: m_Name{ name }, m_Begin{ std::chrono::steady_clock::now() }, m_Running{ true }
	{
		if (name.size() > s_MaxNameLength)
			throw std::runtime_error("Timer name " + name + " exceeds the maximum length of " + std::to_string(s_MaxNameLength) + " characters");
	}

	Timer::~Timer()
	{
		if (!m_Running)
			return;
		Stop();
	}

	void Timer::Initialize(const std::filesystem::path& pathToOutputFile)
	{
		s_OutputStream.open(pathToOutputFile);
		if (!s_OutputStream)
			throw std::runtime_error("Unable to initialize timer: unable to open file " + pathToOutputFile.string());
	}

	double Timer::Stop()
	{
		std::chrono::time_point<std::chrono::steady_clock> end{ std::chrono::steady_clock::now() };
		std::chrono::duration<double> dur = end - m_Begin;
		s_OutputStream << m_Name << std::setw(s_MaxNameLength-m_Name.size()) << " took: " << dur.count() << "s or " << dur.count() * 1000 << "ms\n";
		m_Running = false;
		return dur.count();
	}

	void Timer::Restart(const std::string& name)
	{
		if (m_Running)
			throw std::runtime_error("Attempting to restart an already running timer");
		m_Name = name;
		m_Running = true;
		m_Begin = std::chrono::steady_clock::now();
	}
#endif
}

