// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "Util.h"

#include "Application.h"

float Util::ConvertToOpenGLCoordinate(int num, bool isX)
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

int Util::ConvertToPixelCoordinate(float coor, bool isX)
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
