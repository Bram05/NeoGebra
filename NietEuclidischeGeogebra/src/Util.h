// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

namespace Util
{
	float ConvertToOpenGLCoordinate(int num, bool isX);
	int ConvertToPixelCoordinate(float coor, bool isX);
}