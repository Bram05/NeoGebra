// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "MenuUI.h"
#include "Application.h"
#include "ButtonUI.h"
#include "TextInputField.h"
#include "Rendering/TextRenderer.h"
#include "ErrorBox.h"
#include "EquationUI.h"

static void PoincareModel(void*)
{
	VarMap variables;
	variables.second.push_back({ AdvancedString("d"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("~(l0^2+l1^2)")) });
	variables.second.push_back({ AdvancedString("r"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("(1/l.d-l.d)/2")) });
	variables.second.push_back({ AdvancedString("a"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("atan(l1/l0)")) });
	variables.second.push_back({ AdvancedString("mx"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l0+l.r*cos(l.a)*l0/[l0]")) });
	variables.second.push_back({ AdvancedString("my"), std::make_shared<Equation>(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("l1+l.r*sin(l.a)*l0/[l0]")) });

	Equation pointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & p0^2 + p1^2 < 1") };
	Equation lineDef{ {AdvancedString("l")}, AdvancedString("(x-l.mx)^2 + (y-l.my)^2 = l.r^2 & l0^2 + l1^2 < 1 & x^2 + y^2 < 1") };
	Equation incidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("(p0-l.mx)^2 + (p1-l.my)^2 = l.r^2") };
	Equation distanceDef{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("acosh(1+(2*((p0-q0)^2 + (p1-q1)^2))/((1-(p0^2+p1^2))(1-(q0^2+q1^2))))") };
	Equation betweenness{ {AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)") };

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(-sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2)+sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2+1))/(sqrt(((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))^2+((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))^2))*((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(-sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2)+sqrt((((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))-p0)^2+(((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))-p1)^2+1))/(sqrt(((-2*p0^2*q1 - 2*p1^2*q1 + 2*p1*q0^2 + 2*p1*q1^2 + 2*p1 - 2*q1)/(-4*p0*q1 + 4*p1*q0))^2+((-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0))^2))*(-2*p0^2*q0 + 2*p0*q0^2 + 2*p0*q1^2 - 2*p1^2*q0 + 2*p0 - 2*q0)/(4*p0*q1 - 4*p1*q0)") } };

	Application::Get()->SetModel(variables, 2, pointDef, 2, lineDef, incidence, distanceDef, betweenness, lineFromPoints);
	Equation boundary(AdvancedString("x^2+y^2=1"));
	Application::Get()->GetModel()->addExtraEquation(boundary);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

static void BeltramiKleinModel(void* obj) {
	VarMap variables;
	Equation BKpointDef{ {AdvancedString("p")}, AdvancedString("x = p0 & y = p1 & x^2 + y^2 < 1 ") };
	Equation BKlineDef{ {AdvancedString("l")}, AdvancedString("l0*x+l1*y=l2 & x^2 + y^2 < 1") };
	Equation BKincidence{ {AdvancedString("p"), AdvancedString("l")}, AdvancedString("p0*l0+l1*p1=1") };
	Equation BKdistanceDef{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("") };
	Equation BKbetweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 < q0 & q0 < r0) | p0 > q0 & q0 > r0) | ((p0 = q0 & q0 = r0) & p1 < q1 & q1 < r1)"));
	
	EquationVector BKlineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("q1-p1") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(-q0+p0)")},
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(q1-p1)*q0+(-q0+p0)*q1")}
	};
	EquationVector BKpointFromLines{ 
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1*k2-l2*k1)/(-l0*k1+l1*k0)")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l0*k2-l2*k1)/(l0*k1-l1*k0)") }  
	};
	Application::Get()->SetModel(variables, 2, BKpointDef, 3, BKlineDef, BKincidence, BKdistanceDef, BKbetweennessDef, BKlineFromPoints, BKpointFromLines);
	Equation boundary(AdvancedString("x^2+y^2=1"));
	Application::Get()->GetModel()->addExtraEquation(boundary);
	Application::Get()->GetWindowUI()->GetEquationUI()->LoadFromActiveModel();
	Application::Get()->GetWindowUI()->GetEquationUI()->UpdateModel();
}

static void HalfPlaneModel(void* obj)
{
	VarMap variables;
	Equation pointDef(std::vector<AdvancedString>{AdvancedString("p")}, AdvancedString("x=p0 & y=p1 & y>0"));
	Equation lineDef(std::vector<AdvancedString>{AdvancedString("l")}, AdvancedString("y > 0 & ((x - l0)^2 + y^2 = l1 | (x = l0 & (l1 = 0))) & !(l1 < 0)"));
	Equation incidenceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("l")}, AdvancedString("p1 > 0 & ((p0 - l0)^2 + p1^2 = l1 | (p0 = l0 & (l1 = 0))) & !(l0 < 0)"));
	Equation distanceDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q")}, AdvancedString("2 * atanh(sqrt(((q0-p0)^2+(q1-p1)^2)/((q0-p0)^2 + (q1+p1)^2)))"));
	Equation betweennessDef(std::vector<AdvancedString>{AdvancedString("p"), AdvancedString("q"), AdvancedString("r")}, AdvancedString("((p0 < q0 & q0 < r0) | p0 > q0 & q0 > r0) | ((p0 = q0 & q0 = r0) & p1 < q1 & q1 < r1)"));

	EquationVector lineFromPoints{
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("(!(p0 = q0) * (q0^2+q1^2-p0^2-p1^2)/(-2*p0+2*q0)) + ((p0 = q0) * q0)") },
		{ {AdvancedString("p"), AdvancedString("q")}, AdvancedString("!(p0 = q0) * ((p0 - (q0^2+q1^2-p0^2-p1^2)/(-2*p0+2*q0))^2 + p1^2)")}
	};

	EquationVector pointFromLines{
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 = 0) * l0 + (k1 = 0) * k0 + !(l1 = 0) * !(k1 = 0) * (k1 - l1 + l0 ^ 2 - k0 ^ 2) / (-2 * k0 + 2 * l0)")},
		{ {AdvancedString("l"), AdvancedString("k") }, AdvancedString("(l1 = 0) * sqrt(k1 - (l0 - k0)^2) + (k1 = 0) * (sqrt(l1 - (k0 - l0) ^ 2)) + !(l1 = 0) * !(k1 = 0) * sqrt(l1 - (((k1 - l1 + l0 ^ 2 - k0 ^ 2) / (-2 * k0 + 2 * l0) - l0) ^ 2))") }, //  
	};

	Application::Get()->SetModel(variables, 2, pointDef, 2, lineDef, incidenceDef, distanceDef, betweennessDef, lineFromPoints, pointFromLines);
	Equation boundary(AdvancedString("y = 0"));
	Application::Get()->GetModel()->addExtraEquation(boundary, {255,0,0,255});
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

	std::vector<void(*)(void*)> functions = { &PoincareModel, &BeltramiKleinModel, &HalfPlaneModel };
	std::vector<AdvancedString> textList = { AdvancedString(L"Poincaré Model"), AdvancedString(L"Beltrami Klein Model"), AdvancedString(L"Half-Plane Model") };
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