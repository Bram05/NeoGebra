#include "PostulateVerifier/PostulateVerifier.h"
#include "z3++.h"


int main()
{
	//Simpel 3 punts model
	equation SpointDef{ {"p"}, "(p0 = 1 & x = -0.5 & y = -0.5) | (p0 = 1 & x = 0.5 & y = -0.5) | (p0 = 3 & x = 0 & y = 0.5)"};
	equation SlineDef{ {"l"}, "(((l0 = 1 & l1 = 3) | (l1 = 1 & l0 = 3)) & y = 2*x + 0.5) | (((l0 = 2 & l1 = 3) | (l1 = 2 & l0 = 3)) & y = -2*x + 0.5) | (((l0 = 1 & l1 = 2) | (l1 = 1 & l0 = 2)) & y = -0.5)"};
	equation Sincidence{ {"p", "l"}, "p0 = l0 | p0 = l1" };
	
	//Poincaré model V2
	equation P2pointDef{ {"p"}, "x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	equation P2lineDef{ {"l"}, "(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1"};
	equation P2incidence{ {"p", "l"}, "(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	equation P2betweenness{ {"p", "q", "r"}, "((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)"};
	
	Model Sm(1, SpointDef, 2, SlineDef, Sincidence);
	Model P2m(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness);
	point p1 = P2m.newPoint({ 0.625,  0.4145780988 });
	point p2 = P2m.newPoint({ 0.5, 0 });
	point p3 = P2m.newPoint({ 0.625, -0.4145780988 });
	line l1 = P2m.newLine({ 1.25, 0 });
	line l2 = P2m.newLine({ 1.25, 0 });
	std::cout << isBetween(p1, p2, p3) << '\n';
}	