#pragma once

namespace Util
{
	float ConvertToOpenGLCoordinate(int num, bool isX);
	int ConvertToPixelCoordinate(float coor, bool isX);
}