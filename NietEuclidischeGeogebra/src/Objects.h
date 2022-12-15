// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

struct Point
{
	float x, y;
};

static Point operator+(const Point& p1, const Point& p2)
{
	return {p1.x + p2.x, p1.y + p2.y};
}
static Point operator-(const Point& p1, const Point& p2)
{
	return { p1.x - p2.x, p1.y - p2.y };
}
static Point operator/(const Point& p1, float value)
{
	return { p1.x / value, p1.y / value };
}
static Point operator*(const Point& p1, float value)
{
	return { p1.x * value, p1.y * value };
}