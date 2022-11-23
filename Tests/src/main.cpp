#include "PostulateVerifier/PostulateVerifier.h"

int main()
{
	std::vector<std::string> tmp{ "(assert (and (>= p1 1) (<= p1 3))" };

	// Poincar� model
	// 
	// punt:
	// 
	// x^2 + y^2 < 1
	// 
	// 
	// lijn:
	// 
	// E: x1 x2 y1 y2
	// 
	// (x1-a)^2 + (y1-b)^2 = r^2
	// x1c^2 + y1c^2 = 1
	// 
	// (x2-a)^2 + (y2-b)^2 = r^2
	// x2c^2 + y2c^2 = 1
	// 
	// -x1/y1 * -(x1-a)/(x1-b) = -1
	// -x2/y2 * -(x2-a)/(x2-b) = -1
	// 
	// !(x1 = x2 && y1 = y2)
	// 
	//
	// out: a en b (2 parameters)
	// 
	// incidence: 
	// (x-a)^2 + (y-b)^2 = r^2
	// x^2 + y^2 < 1
	// 
	// 
	//

	Model g(1, &tmp, nullptr, 2, nullptr, nullptr, nullptr);
	line l1 = g.newLine(std::vector<int>{1,2});
	line l2 = g.newLine(std::vector<int>{2,1});
	point p = g.newPoint(std::vector<int>{3});
	
	
	std::cout << (p >> l1) << '\n';
}