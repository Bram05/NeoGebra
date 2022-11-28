#include "Util.h"

#include "Application.h"

float Util::ConvertToOpenGLCoordinate(int num, bool isX)
{
	auto[width, height] = Application::Get()->GetWindow()->GetSize(); // maybe invert the y
	if (isX)
	{
		return 2 * (((float)num / width) - 0.5);
	}
	else
	{
		return -2 * (((float)num / height) - 0.5);
	}
}
