#include "Model.h"
#include "Application.h"

RGBColour::RGBColour() : RGBColour(0, 0, 0, 0) {}

RGBColour::RGBColour(uint8_t r, uint8_t g, uint8_t b, uint8_t a)
	: r{ r }, g{ g }, b{ b }, a{ a },
	norm_r{ r / float(255) }, norm_g{ g / float(255) }, norm_b{ b / float(255) }, norm_a{ a / float(255) } {}
RGBColour::RGBColour(int r, int g, int b, int a)
	: RGBColour(static_cast<uint8_t>(r), static_cast<uint8_t>(g), static_cast<uint8_t>(b), static_cast<uint8_t>(a)) {}
RGBColour::RGBColour(const RGBColour& c) : RGBColour(c.r, c.g, c.b, c.a) { }

NEElement::NEElement(const std::vector<float>& identifiers, const Equation& def, const int identNum, NEType type, std::shared_ptr<Model> model, const RGBColour& colour, bool checkValidity)
	: m_Identifiers{ identifiers }, m_Def{ def }, m_Type{ type }, m_Model{ model }, m_Colour{ colour }
{
	if (checkValidity) {
		if (!def.SolutionExists(identifiers, m_ID, type, model.get())) {
			std::string identifierString;
			identifierString += "( ";
			for (float id : identifiers) {
				identifierString += std::format("{:.2f}", id) + " ";
			}
			identifierString += ")";
			Application::Get()->GetWindowUI()->DisplayError("Invalid element " + identifierString + ": Check the definition");
			throw ErrorBoxException();
		}
	}

	if (identifiers.size() != identNum) {
		std::string identifierString;
		identifierString += "( ";
		for (float id : identifiers) {
			identifierString += std::format("{:.2f}", id) + " ";
		}
		identifierString += ")";
		Application::Get()->GetWindowUI()->DisplayError("Invalid identifiers: " + identifierString + ". There should be " + std::to_string(identNum) + " identifiers");
		throw ErrorBoxException();
	}

	if (m_Type != notype) {
		if (m_Model->m_Elements.size() > 0) {
			m_ID = m_Model->m_Elements.back().getID() + 1;
		}
		else { m_ID = 0; }
		m_Model->m_Elements.push_back(std::move(*this));
		m_Model->solveVariables(this);
	}
	else
	{
		m_ID = -1;
	}
}

std::string NEElement::getShader() {
	return m_Def.toShader({ m_Identifiers }, { m_ID });
}

NEPoint::NEPoint(const std::vector<float>& identifiers, std::shared_ptr<Model> m, const RGBColour& colour, bool checkValidity)
	: NEElement(identifiers, m->m_PointDef, m->m_PointIdentifiers, point, m, colour, checkValidity) {}

NELine::NELine(const std::vector<float>& identifiers, std::shared_ptr<Model> m, const RGBColour& colour, bool checkValidity)
	: NEElement(identifiers, m->m_LineDef, m->m_LineIdentifiers, line, m, colour, checkValidity) {}

Model::Model(VarMap& variables,
	unsigned int pointIdentifiers,
	const Equation& pointDef,
	unsigned int lineIdentifiers,
	const Equation& lineDef,
	const Equation& incidenceConstr,
	const EquationVector& lineFromPoints,
	const EquationVector& pointFromLines,
	const Equation& distanceDef,
	const Equation& betweennessConstr)
	:
	m_Variables{ variables },
	m_PointIdentifiers{ pointIdentifiers },
	m_PointDef{ pointDef },
	m_LineIdentifiers{ lineIdentifiers },
	m_LineDef{ lineDef },
	m_IncidenceConstr{ incidenceConstr },
	m_DistanceDef{ distanceDef },
	m_BetweennessConstr{ betweennessConstr },
	m_LineFromPoints{ lineFromPoints },
	m_PointFromLines{ pointFromLines }
{
	m_PointDef.linkVars(&m_SolvedVariables, { point });
	m_LineDef.linkVars(&m_SolvedVariables, { line });
	m_IncidenceConstr.linkVars(&m_SolvedVariables, { point, line });
	m_DistanceDef.linkVars(&m_SolvedVariables, { point, point });
	m_BetweennessConstr.linkVars(&m_SolvedVariables, { point, point, point });
	for (Equation& e : m_LineFromPoints) {
		e.linkVars(&m_SolvedVariables, { point, point });
	}
	for (Equation& e : m_PointFromLines) {
		e.linkVars(&m_SolvedVariables, { line, line });
	}

	for (std::pair < AdvancedString, std::shared_ptr<Equation>> p : m_Variables.first) {
		p.second->linkVars(&m_SolvedVariables, { point });
	}
	for (std::pair < AdvancedString, std::shared_ptr<Equation>> p : m_Variables.second) {
		p.second->linkVars(&m_SolvedVariables, { line });
	}
}

Model::Model(const Model& m) :
	m_Variables{ m.m_Variables },
	m_PointIdentifiers{ m.m_PointIdentifiers },
	m_PointDef{ m.m_PointDef },
	m_LineIdentifiers{ m.m_LineIdentifiers },
	m_LineDef{ m.m_LineDef },
	m_IncidenceConstr{ m.m_IncidenceConstr },
	m_DistanceDef{ m.m_DistanceDef },
	m_BetweennessConstr{ m.m_BetweennessConstr },
	m_LineFromPoints{ m.m_LineFromPoints },
	m_PointFromLines{ m.m_PointFromLines }
{
	m_PointDef.linkVars(&m_SolvedVariables, { point });
	m_LineDef.linkVars(&m_SolvedVariables, { line });
	m_IncidenceConstr.linkVars(&m_SolvedVariables, { point, line });
	m_DistanceDef.linkVars(&m_SolvedVariables, { point, point });
	m_BetweennessConstr.linkVars(&m_SolvedVariables, { point, point, point });
	for (Equation& e : m_LineFromPoints) {
		e.linkVars(&m_SolvedVariables, { point, point });
	}
	for (Equation& e : m_PointFromLines) {
		e.linkVars(&m_SolvedVariables, { line, line });
	}
}

void Model::solveVariables(const NEElement* e) {
	if (e->getType() == point || e->getType() == line) {
		std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >>& m = e->getType() == point ? m_Variables.first : m_Variables.second;
		for (std::pair < AdvancedString, std::shared_ptr<Equation>>& p : m) {
			m_SolvedVariables[{e->getType(), p.first}][e->getID()] = p.second->getResult({ e->getIdentifiers() }, { e->getID() });
		}
	}
}

void Model::addExtraEquation(Equation& eq, const RGBColour& colour) {
	m_ExtraEquations.push_back(NEElement(std::vector<float>{}, eq, 0, notype, shared_from_this(), colour, false));
}

NELine Model::lineFromPoints(const NEPoint& p1, const NEPoint& p2) {
	std::vector<float> identifiers;
	for (int i = 0; i < m_LineIdentifiers; ++i) {
		identifiers.push_back(m_LineFromPoints[i].getResult({ p1.getIdentifiers(), p2.getIdentifiers() }, { p1.getID(), p1.getID() }));
	}
	return NELine(identifiers, shared_from_this(), { 0,0,200,255 });
}

NEPoint Model::pointFromLines(const NELine& l1, const NELine& l2) {
	std::vector<float> identifiers;
	for (int i = 0; i < m_PointIdentifiers; ++i) {
		float identifier = m_PointFromLines[i].getResult({ l1.getIdentifiers(), l2.getIdentifiers() }, { l1.getID(), l2.getID() });
		if (isnan(identifier)) {
			Application::Get()->GetWindowUI()->DisplayError("Lines don't intersect");
			throw ErrorBoxException();
		}
		identifiers.push_back(identifier);
	}
	return NEPoint(identifiers, shared_from_this(), { 20,20,20,255 });
}

bool operator==(const NEElement& lhs, const NEElement& rhs) {
	if (lhs.getModel() != rhs.getModel()) {
		return false;
	}

	if (lhs.getType() != rhs.getType()) {
		return false;
	}

	if (lhs.getIdentifiers() == rhs.getIdentifiers()) {
		return true;
	}

	return false;
}

bool operator!=(const NEElement& lhs, const NEElement& rhs) { return !(lhs == rhs); }


bool operator==(const RGBColour& c1, const RGBColour& c2) { return c1.r == c2.r && c1.g == c2.g && c1.b == c2.b && c1.a == c2.a; }
bool operator!=(const RGBColour& c1, const RGBColour& c2) { return !(c1 == c2); }

bool operator>>(const NEPoint& p, const NELine& l) {
	if (p.getModel() != l.getModel()) {
		//Later isomorphism
		return false;
	}

	//Custom condition
	Equation eq = p.getModel()->m_IncidenceConstr;
	return eq.isTrue({ p.getIdentifiers(), l.getIdentifiers() }, { p.getID(), l.getID() });
}

float distance(const NEPoint& p1, const NEPoint& p2) {
	return p1.getModel()->m_DistanceDef.getResult({ p1.getIdentifiers(), p2.getIdentifiers() }, { p1.getID(), p2.getID() });
}

bool isBetween(const NEPoint& p1, const NEPoint& p2, const NEPoint& p3) {
	if (p1.getModel() != p2.getModel() || p2.getModel() != p3.getModel()) {
		//Later isomorphism
		return false;
	}

	std::vector<float> identifiers;
	for (int i = 0; i < p1.getModel()->m_LineIdentifiers; ++i) {
		identifiers.push_back(p1.getModel()->m_LineFromPoints[i].getResult({ p1.getIdentifiers(), p2.getIdentifiers() }, { p1.getID(), p1.getID() }));
	}
	NELine l(identifiers, p1.getModel());
	Equation eq = p1.getModel()->m_IncidenceConstr;
	if (!eq.isTrue({ p3.getIdentifiers(), l.getIdentifiers() }, { p3.getID(), l.getID() })) {
		for (int i = 0; i < p1.getModel()->m_Elements.size(); ++i) {
			NEElement e = p1.getModel()->m_Elements[i];
			if (e.getID() == l.getID()) {
				p1.getModel()->m_Elements.erase(p1.getModel()->m_Elements.begin() + i);
				break;
			}
		}
		return false;
	}
	for (int i = 0; i < p1.getModel()->m_Elements.size(); ++i) {
		NEElement e = p1.getModel()->m_Elements[i];
		if (e.getID() == l.getID()) {
			p1.getModel()->m_Elements.erase(p1.getModel()->m_Elements.begin() + i);
			break;
		}
	}

	//Custom condition
	Equation betweennessEq = p1.getModel()->m_BetweennessConstr;
	return betweennessEq.isTrue({ p1.getIdentifiers(), p2.getIdentifiers(), p3.getIdentifiers() }, { p1.getID(), p2.getID(), p2.getID() });
}

