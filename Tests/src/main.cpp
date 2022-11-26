#include "PostulateVerifier/PostulateVerifier.h"
#include "z3++.h"


int main()
{
	//nog ff kijken naar syntax van "p$"
	//Simpel 3 punts model
	std::string SpointConstr{ "p$ p0 = 1 | p0 = 2 | p0 = 3" };
	std::string SpointEq{ "p$q$ p0 = q0" };
	std::string SlineConstr{ "p$ (p0 = 1 | p0 = 2 | p0 = 3) & (p1 = 1 | p1 = 2 | p1 = 3) & p0 != p1" };
	std::string SlineEq{ "l$m$ (l0 = m0 & l1 = m1) | (l0 = m1 & l1 = m0)" };
	std::string Sincidence{ "p$l$ p0 = l0 | p0 = l1" };
	
	//Poincaré model
	std::string PpointConstr{ "p$ p0^2 + p1^2 < 1" };
	std::string PpointEq{ "p$q$ p0 = q0 & p1 = q1" };
	std::string PlineConstr{ "l$ l0^2 + l1^2 > 1" };
	std::string PlineEq{ "l$m$ l0 = m0 & l1 = m1" };
	std::string Pincidence{ "p$l$ (p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	
	//Poincaré model V2
	std::string P2pointDef{ "p$ x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	std::string P2lineDef{ "l$ (x-l0)^2 + (y-l1)^2 = l2^2 & l0^2 + l1^2 > 1" };
	std::string P2incidence{ "p$l$ (p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	
	//std::string tmp{ "x=p0&y=p1&2~p0=4" };
	//std::cout << Z3Tools::toLisp(tmp, { {"p0", 5}, {"p1", 6} }) << std::endl;

	Model g(2, P2pointDef, 2, P2lineDef, P2incidence);
	point p = g.newPoint(std::vector<float>{0.5, 0});
	line l = g.newLine(std::vector<float>{1.25, 0});
	std::cout << (p >> l) << '\n';
}	