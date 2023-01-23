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

	int ConvertToPixelValue(float num, bool isX)
	{
		auto[width, height] = Application::Get()->GetWindow()->GetSize();
		if (isX)
			return (num / 2) * width;
		else
			return (num / 2) * height;
	}

	void ExitDueToFailure()
	{
		#ifdef DEBUG
		__debugbreak();
		#endif
		std::cerr << "Press enter to exit\n";
		std::cin.get();
		std::exit(EXIT_FAILURE);
	}

#ifdef TIMING
	std::ofstream Timer::s_OutputStream;

	Timer::Timer(const std::string& name)
		: m_Name{ name }, m_Begin{ std::chrono::steady_clock::now() }, m_Running{ true }
	{
		if (name.size() > s_MaxNameLength)
		{
			std::cerr << "Timer name " << name << " exceeds the maximum length of " << std::to_string(s_MaxNameLength) << " characters\n";
			Util::ExitDueToFailure();
		}
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
		{
			std::cerr << "Unable to initialize timer: unable to open file " << pathToOutputFile.string() << '\n';
			Util::ExitDueToFailure();
		}

		s_OutputStream << std::setprecision(6);
		PrintInfo(std::cout << "Timer initialized\n");
	}

	void Timer::Terminate()
	{
		s_OutputStream.close();
		PrintInfo(std::cout << "Timer terminated\n");
	}

	double Timer::Stop()
	{
		std::chrono::time_point<std::chrono::steady_clock> end{ std::chrono::steady_clock::now() };
		std::chrono::duration<double> dur = end - m_Begin;
		s_OutputStream << m_Name << std::setw(s_MaxNameLength - m_Name.size()) << " took: " << dur.count() << "s\t or " << dur.count() * 1000 << "ms\n";
		m_Running = false;
		return dur.count();
	}

	void Timer::Restart(const std::string& name)
	{
		if (m_Running)
		{
			std::cerr << "Attempting to restart an already running timer\n";
			Util::ExitDueToFailure();
		}

		m_Name = name;
		m_Running = true;
		m_Begin = std::chrono::steady_clock::now();
	}
#endif
}

