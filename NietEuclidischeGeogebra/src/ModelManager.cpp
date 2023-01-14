#include "ModelManager.h"

ModelManager::ModelManager()
{
	Equation P2pointDef{ {"p"}, "x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	Equation P2lineDef{ {"l"}, "(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1" };
	Equation P2incidence{ {"p", "l"}, "(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	//Equation P2incidence{ {"p", "l"}, "lieoncircle(p0, p1, circle(l0, l1, ...))" };
	Equation P2betweenness{ {"p", "q", "r"}, "((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)" };

	SetModel(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness);
	
	std::shared_ptr<NELine> l1(new NELine({ 1.25, 0 }, m_Model));

	/*std::shared_ptr<NEPoint> p1(new NEPoint({0.625,  0.4145780988}, m_Model, {255, 0, 0, 255}));
	std::shared_ptr<NEPoint> p2(new NEPoint({ 0.5, 0 }, m_Model, { 255, 0, 0, 255 }));
	std::shared_ptr<NEPoint> p3(new NEPoint({ 0.625, -0.4145780988 }, m_Model, { 255, 0, 0, 255 }));*/
}

ModelManager::~ModelManager()
{
}