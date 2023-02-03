// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "MenuUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"
#include "ErrorBox.h"
#include "EquationUI.h"
#include "Maths/PostulateVerifier.h"

static void PoincareModel(void*)
{
	VarMap variables;
	variables.second.push_back({ AdvancedString("d"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("~(l0^2+l1^2)")) });
	variables.second.push_back({ AdvancedString("r"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("(1/l.d-l.d)/2")) });
	variables.second.push_back({ AdvancedString("a"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("atan(l1/l0)")) });
	variables.second.push_back({ AdvancedString("mx"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l0+l.r*cos(l.a)*(-1+2(l0 >= 0))")) });
	variables.second.push_back({ AdvancedString("my"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l1+l.r*sin(l.a)*(-1+2(l0 >= 0))")) });

	Equation pointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & p0^2 + p1^2 < 1") };
	Equation lineDef{ {AdvancedString("l")}, AdvancedString("(x-l.mx)^2 + (y-l.my)^2 = l.r^2 & l0^2 + l1^2 < 1 & x^2 + y^2 < 1") };
	Equation incidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("(p0-l.mx)^2 + (p1-l.my)^2 = l.r^2") };
	Equation distanceDef{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("acosh(1+(2*((p0-q0)^2 + (p1-q1)^2))/((1-(p0^2+p1^2))(1-(q0^2+q1^2))))") };
	Equation betweenness{ {AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)") };

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(-sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2)+sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2+1))/(sqrt(((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))^2+((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))^2))*((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(-sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2)+sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2+1))/(sqrt(((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))^2+((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))^2))*(-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0)") } 
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k")}, AdvancedString("(2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2) >= 1)*(0.5 * (l.mx+k.mx) + (l.r^2-k.r^2)/(2*((l.mx-k.mx)^2+(l.my-k.my)^2))*(k.mx-l.mx)+0.5*sqrt(2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2)-1)*(k.my-l.my)*(-1+2*(l.a>=k.a))*(-1+2*(l0*k0>=0))*(1-2*(l0*k0=0)*(l0+k0<0)))  + (2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2) < 1)*NaN")},
		{ {AdvancedString("l"), AdvancedString("k")}, AdvancedString("(2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2) >= 1)*(0.5 * (l.my+k.my) + (l.r^2-k.r^2)/(2*((l.mx-k.mx)^2+(l.my-k.my)^2))*(k.my-l.my)+0.5*sqrt(2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2)-1)*(l.mx-k.mx)*(-1+2*(l.a>=k.a))*(-1+2*(l0*k0>=0))*(1-2*(l0*k0=0)*(l0+k0<0)))  + (2*(l.r^2+k.r^2)/((l.mx-k.mx)^2+(l.my-k.my)^2) - (l.r^2-k.r^2)^2/(((l.mx-k.mx)^2+(l.my-k.my)^2)^2) < 1)*NaN")}
	};

	Application::Get()->SetModel(variables, 2, pointDef, 2, lineDef, incidence, distanceDef, betweenness, lineFromPoints, pointFromLines);
	Equation boundary(AdvancedString("x^2+y^2=1"));
	Application::Get()->GetModel()->addExtraEquation(boundary);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
	//PostulateVerifier::PARALLEL(*Application::Get()->GetModel());

}

static void BeltramiKleinModel(void* obj) {
	VarMap variables;
	Equation BKpointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & p0^2 + p1^2 < 1 & x^2 + y^2 < 1 ") };
	Equation BKlineDef{ {AdvancedString("l")}, AdvancedString("l0 * x + l1 * y = l2 & (l0 = 1| (l0 = 0 & l1 = 1)) & x^2 + y^2 < 1") };
	Equation BKincidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("p0*l0+l1*p1=l2") };
	Equation BKdistanceDef{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("") };
	Equation BKbetweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 <= q0 & q0 <= r0) | (p0 >= q0 & q0 >= r0)) & ((p1 <= q1 & q1 <= r1) | (p1 >= q1 & q1 >= r1))"));
	
	EquationVector BKlineFromPoints{	
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("p1 != q1") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p1 = q1)+(p1!=q1)*(q0-p0)/(p1-q1)")},
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p1 = q1)*p1 + (p1!=q1)*(p1*q0-p0*q1)/(p1-q1)")}
	};
	EquationVector BKpointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0*k1 - l1*k0 != 0)*(((-l1*k2 + l2*k1)/(l0*k1 - l1*k0))^2 + (( l0*k2 - l2*k0)/(l0*k1 - l1*k0))^2 < 1)*(-l1*k2 + l2*k1)/(l0*k1 - l1*k0)+(l0*k1 - l1*k0 = 0)*NaN+(l0*k1 - l1*k0 != 0)*(((-l1*k2 + l2*k1)/(l0*k1 - l1*k0))^2 + (( l0*k2 - l2*k0)/(l0*k1 - l1*k0))^2 >= 1)*NaN")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0*k1 - l1*k0 != 0)*(((-l1*k2 + l2*k1)/(l0*k1 - l1*k0))^2 + (( l0*k2 - l2*k0)/(l0*k1 - l1*k0))^2 < 1)*( l0*k2 - l2*k0)/(l0*k1 - l1*k0)+(l0*k1 - l1*k0 = 0)*NaN+(l0*k1 - l1*k0 != 0)*(((-l1*k2 + l2*k1)/(l0*k1 - l1*k0))^2 + (( l0*k2 - l2*k0)/(l0*k1 - l1*k0))^2 >= 1)*NaN") },
	};

	Application::Get()->SetModel(variables, 2, BKpointDef, 3, BKlineDef, BKincidence, BKdistanceDef, BKbetweennessDef, BKlineFromPoints, BKpointFromLines);
	Equation boundary(AdvancedString("x^2+y^2=1"));
	Application::Get()->GetModel()->addExtraEquation(boundary);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
	//PostulateVerifier::PARALLEL(*Application::Get()->GetModel());
}

static void HalfPlaneModel(void* obj)
{
	VarMap variables;
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("x=p0 & y=p1 & y>0"));
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("y > 0 & ((x - l0)^2 + y^2 = l1 | (x = l0 & (l1 = 0))) & !(l1 < 0)"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("l")}, AdvancedString("p1 > 0 & ((p0 - l0)^2 + p1^2 = l1 | (p0 = l0 & (l1 = 0))) & !(l0 < 0)"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString("2 * atanh(sqrt(((q0-p0)^2+(q1-p1)^2)/((q0-p0)^2 + (q1+p1)^2)))"));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 < q0 & q0 < r0) | (p0 > q0 & q0 > r0)) | ((p0 = q0 & q0 = r0) & ((p1 < q1 & q1 < r1) | (p1 > q1 & q1 > r1)))"));

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(!(p0 = q0) * (q0^2+q1^2-p0^2-p1^2)/(-2*p0+2*q0)) + ((p0 = q0) * q0)") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("!(p0 = q0) * ((p0 - (q0^2+q1^2-p0^2-p1^2)/(-2*p0+2*q0))^2 + p1^2)")}
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 = 0) * l0 + (k1 = 0) * k0 + !(l1 = 0) * !(k1 = 0) * (k1 - l1 + l0 ^ 2 - k0 ^ 2) / (-2 * k0 + 2 * l0)")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 = 0) * sqrt(k1 - (l0 - k0)^2) + (k1 = 0) * (sqrt(l1 - (k0 - l0) ^ 2)) + !(l1 = 0) * !(k1 = 0) * sqrt(l1 - (((k1 - l1 + l0 ^ 2 - k0 ^ 2) / (-2 * k0 + 2 * l0) - l0) ^ 2))") }
	};

	Application::Get()->SetModel(variables, 2, pointDef, 2, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Equation boundary(AdvancedString("y = 0"));
	Application::Get()->GetModel()->addExtraEquation(boundary, {255,0,0,255});
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

static void EuclideanModel(void* obj)
{
	VarMap variables;
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("x=p0 & y=p1"));
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l0 * x + l1 * y = l2 & (l0 = 1| (l0 = 0 & l1 = 1))"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("l")}, AdvancedString("l0 * p0 + l1 * p1 = l2"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString("sqrt((p0 - q0)^2 + (p1 - q1)^2)"));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 <= q0 & q0 <= r0) | (p0 >= q0 & q0 >= r0)) & ((p1 <= q1 & q1 <= r1) | (p1 >= q1 & q1 >= r1))"));

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("p1 != q1") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p1 = q1)+(p1!=q1)*(q0-p0)/(p1-q1)")},
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p1 = q1)*p1 + (p1!=q1)*(p1*q0-p0*q1)/(p1-q1)")}
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0*k1 - l1*k0 != 0)*(-l1*k2 + l2*k1)/(l0*k1 - l1*k0)+(l0*k1 - l1*k0 = 0)*NaN")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0*k1 - l1*k0 != 0)*( l0*k2 - l2*k0)/(l0*k1 - l1*k0)+(l0*k1 - l1*k0 = 0)*NaN") },
	};

	Application::Get()->SetModel(variables, 2, pointDef, 3, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
	//PostulateVerifier::PARALLEL(*Application::Get()->GetModel());
}

static void ProjectiveModel(void* obj)
{
	VarMap variables;
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("(x=p0 & y=p1 & p2 = 0)|((p0 = 1| (p0 = 0 & p1 = 1)) & p2 = 1)"));
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("(l0 * x + l1 * y = l2 & (l0 = 1| (l0 = 0 & l1 = 1)))|(l0=0&l1=0&l2=0)"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("l")}, AdvancedString("(!(l0 = 0 & l1 = 0) & p2 = 0 & l0 * p0 + l1 * p1 = l2)|(!(l0 = 0 & l1 = 0) & p2 = 1 & p0 = l0 & p1 = l1)|(p2 = 1 & l0 = 0 & l1 = 0)"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2=0&q2=0)*sqrt((p0 - q0)^2 + (p1 - q1)^2)+(p2=1|q2=1)*(1/0)"));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("p2=0&q2=0&((p0 <= q0 & q0 <= r0) | (p0 >= q0 & q0 >= r0)) & ((p1 <= q1 & q1 <= r1) | (p1 >= q1 & q1 >= r1))"));

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*(p1 != q1) + (p2 = 1)*(q2 = 0)*p0 + (p2 = 0)*(q2 = 1)*q0") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*((p1 = q1)+(p1!=q1)*(q0-p0)/(p1-q1)) + (p2 = 1)*(q2 = 0)*p1 + (p2 = 0)*(q2 = 1)*q1")},
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*((p1 = q1)*p1 + (p1!=q1)*(p1*q0-p0*q1)/(p1-q1)) + ((p2 = 1)*(q2 = 0)+(p2 = 0)*(q2 = 1))*(p0*q0+p1*q1)")}
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0)*(-l1*k2 + l2*k1)/(l0*k1 - l1*k0) + (l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 = 0)*l0 + (l1 = 0)*k0 + (k1 = 0)*l0")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0)*( l0*k2 - l2*k0)/(l0*k1 - l1*k0) + (l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 = 0)*l1 + (l1 = 0)*k1 + (k1 = 0)*l1") },
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0) = 0") }
	};

	Application::Get()->SetModel(variables, 3, pointDef, 3, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

static void ReverseProjectiveModel(void* obj)
{
	VarMap variables;
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("(x=p0 & y=p1 & p2 = 0)|((p0 = 1| (p0 = 0 & p1 = 1)) & p2 = 1)"));
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("(l0 * x + l1 * y = l2 & (l0 = 1| (l0 = 0 & l1 = 1)))|(l0=0&l1=0&l2=0)"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("l"), AdvancedString("p")}, AdvancedString("(!(l0 = 0 & l1 = 0) & p2 = 0 & l0 * p0 + l1 * p1 = l2)|(!(l0 = 0 & l1 = 0) & p2 = 1 & p0 = l0 & p1 = l1)|(p2 = 1 & l0 = 0 & l1 = 0)"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString(""));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString(""));

	EquationVector pointFromLines{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*(p1 != q1) + (p2 = 1)*(q2 = 0)*p0 + (p2 = 0)*(q2 = 1)*q0") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*((p1 = q1)+(p1!=q1)*(q0-p0)/(p1-q1)) + (p2 = 1)*(q2 = 0)*p1 + (p2 = 0)*(q2 = 1)*q1")},
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p2 = 0)*(q2 = 0)*((p1 = q1)*p1 + (p1!=q1)*(p1*q0-p0*q1)/(p1-q1)) + ((p2 = 1)*(q2 = 0)+(p2 = 0)*(q2 = 1))*(p0*q0+p1*q1)")}
	};

	EquationVector lineFromPoints{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0)*(-l1*k2 + l2*k1)/(l0*k1 - l1*k0) + (l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 = 0)*l0 + (l1 = 0)*k0 + (k1 = 0)*l0")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0)*( l0*k2 - l2*k0)/(l0*k1 - l1*k0) + (l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 = 0)*l1 + (l1 = 0)*k1 + (k1 = 0)*l1") },
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 != 0)*(k1 != 0)*(l0*k1 - l1*k0 != 0) = 0") }
	};

	Application::Get()->SetModel(variables, 3, pointDef, 3, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

static void ThreePointModel(void* obj)
{
	VarMap variables;
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("(p0=0&x=-1&y=-1/2*~3)|(p0=1&x=1&y=-1/2*~3)|(p0=2&x=0&y=1/2*~3)"));
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("(l0=0|l0=1)&(l1=1|l1=2)&l0<l1 &x>=-1&x<=1&y>=-0.9&y<=1/2*~3&((((l0=0&l1=1)|(l0=1&l1=0))&y=-1/2*~3)|(((l0=0&l1=2)|(l0=2&l1=0))&y=~3*x+1/2*~3)|(((l0=1&l1=2)|(l0=2&l1=1))&y=-~3*x+1/2*~3))"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("l")}, AdvancedString("p0=l0|p0=l1"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString("1"));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString(""));

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p0 < q0)*p0 + (p0 > q0)*q0") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(p0 > q0)*p0 + (p0 < q0)*q0")}
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0=k0)*l0+(l1=k0)*l1+(l0=k1)*l0+(l1=k1)*l1")}
	};

	Application::Get()->SetModel(variables, 1, pointDef, 2, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
	//UserInput(PostulateVerifier::PARALLEL(*Application::Get()->GetModel()));
}


static void EmptyModel(void* obj)
{
	VarMap v;
	Application::Get()->SetModel(v, 0, Equation(AdvancedString("")), 0, Equation(AdvancedString("")), Equation(AdvancedString("")), Equation(AdvancedString("")), Equation(AdvancedString("")), EquationVector(), EquationVector());
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

MenuUI::MenuUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "MenuUI")//, text(500, 500, "red")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom

	float buttonWidth = 0.24f;
	float indent = 0.025f;

	std::vector<void(*)(void*)> functions = { &EmptyModel, &EuclideanModel, &ProjectiveModel, &ReverseProjectiveModel, &PoincareModel, &BeltramiKleinModel, &HalfPlaneModel, &ThreePointModel};
	std::vector<AdvancedString> textList = { AdvancedString(L"New Model"), AdvancedString(L"Euclidean Model"), AdvancedString(L"Projective Model"), AdvancedString(L"Reverse Projective Model"), AdvancedString(L"Poincaré Model"), AdvancedString(L"Beltrami Klein Model"), AdvancedString(L"Half-Plane Model"), AdvancedString(L"Three-point Model") };
	for (int i = 0; i < functions.size(); i++) {
		m_SubUIElements.push_back({ std::make_shared<ButtonUI>(leftX + indent + i * buttonWidth, (leftX + i * buttonWidth + buttonWidth), topY - 0.01f, (topY - 0.09f), functions[i], this, textList[i]) });
	}
}

MenuUI::~MenuUI()
{
}

void MenuUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}

	UIElement::RenderPass(r);
}