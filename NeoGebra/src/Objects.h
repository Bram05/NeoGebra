// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

// A point struct that can be used as a vector
struct Point
{
	double x, y;
};

static Point operator+(const Point& p1, const Point& p2)
{
	return {p1.x + p2.x, p1.y + p2.y};
}
static Point operator-(const Point& p1, const Point& p2)
{
	return { p1.x - p2.x, p1.y - p2.y };
}
static Point operator/(const Point& p1, double value)
{
	return { p1.x / value, p1.y / value };
}
static Point operator*(const Point& p1, double value)
{
	return { p1.x * value, p1.y * value };
}