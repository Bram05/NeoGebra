#include "PostulateVerifier/PostulateVerifier.h"
#include "z3++.h"


int main()
{
	//Simpel 3 punts model
	equation SpointDef{ {"p"}, "(p0 = 1 & x = -0.5 & y = -0.5) | (p0 = 1 & x = 0.5 & y = -0.5) | (p0 = 3 & x = 0 & y = 0.5)"};
	equation SlineDef{ {"l"}, "((((l0 = 1 & l1 = 3) | (l1 = 1 & l0 = 3)) & y = 2*x + 0.5) | (((l0 = 2 & l1 = 3) | (l1 = 2 & l0 = 3)) & y = -2*x + 0.5) | (((l0 = 1 & l1 = 2) | (l1 = 1 & l0 = 2)) & y = -0.5))&(x >= -0.5 & x <= 0.5)&(y>=-0.5 & y <= 0.5)"};
	equation Sincidence{ {"p", "l"}, "p0 = l0 | p0 = l1" };
	
	//Poincaré model V2
	equation P2pointDef{ {"p"}, "x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	equation P2lineDef{ {"l"}, "(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1"};
	equation P2incidence{ {"p", "l"}, "(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	equation P2betweenness{ {"p", "q", "r"}, "((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)"};
	

	Model Sm(1, SpointDef, 2, SlineDef, Sincidence);
	Model P2m(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness);
	NEPoint p1({ 0.625,  0.4145780988 }, &P2m);
	NEPoint p2({0.5, 0}, &P2m);
	NEPoint p3({ 0.625, -0.4145780988 }, &P2m);
	NEPoint p333({0.62565, -0.4145780988}, &P2m);

	NELine l1({1.25, 0}, &P2m);

	//line l2({1.25, 0}, &P2m);
	//std::cout << isBetween(p1, p2, p3) << '\n';

	NELine l({2, 3}, &Sm);

	std::cout << (p1 == l1) << std::endl;
}	

/*
bool feq(float f1, float f2) {
	float epsilon = 0.1;
	if (abs(f1 - f2) <= epsilon)
		return true;
	return abs(f1 - f2) <= epsilon * max(abs(f1), abs(f2));
}
*/