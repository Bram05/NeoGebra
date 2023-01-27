#include "Model.h"

RGBColour::RGBColour() : RGBColour(0,0,0,0) {}

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
		if (identifiers.size() != identNum or !def.getSolution({ identifiers }, { m_ID }).sat) {
			throw std::invalid_argument("Invalid element");
		}
	}

	if (m_Model->m_Elements.size() > 0) {
		m_ID = m_Model->m_Elements.back().getID() + 1;
	}
	else { m_ID = 0; }
	m_Model->m_Elements.push_back(*this);
	m_Model->solveVariables(this);
}

std::string NEElement::getShader() {
	return m_Def.toShader({ m_Identifiers }, { m_ID }, m_Model->m_UseCustomScroll, m_Model->m_CustomScrollX, m_Model->m_CustomScrollY);
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
	const Equation& distanceDef,
	const Equation& betweennessConstr)
	:
	m_Variables{variables},
	m_PointIdentifiers{ pointIdentifiers },
	m_PointDef{ pointDef },
	m_LineIdentifiers{ lineIdentifiers },
	m_LineDef{ lineDef },
	m_IncidenceConstr{ incidenceConstr },
	m_DistanceDef{ distanceDef },
	m_BetweennessConstr{ betweennessConstr } 
{
	m_PointDef.linkVars(&m_SolvedVariables, {point});
	m_LineDef.linkVars(&m_SolvedVariables, {line});
	m_IncidenceConstr.linkVars(&m_SolvedVariables, {point, line });
	m_DistanceDef.linkVars(&m_SolvedVariables, {point, point });
	m_BetweennessConstr.linkVars(&m_SolvedVariables, {point, point, point});
	for (std::pair < AdvancedString, std::shared_ptr<Equation>> p : m_Variables.first) {
		p.second->linkVars(&m_SolvedVariables, {point});
	}
	for (std::pair < AdvancedString, std::shared_ptr<Equation>> p : m_Variables.second) {
		p.second->linkVars(&m_SolvedVariables, {line});
	}
}

Model::Model(const Model& m) :
	m_Variables{m.m_Variables},
	m_PointIdentifiers{ m.m_PointIdentifiers },
	m_PointDef{ m.m_PointDef },
	m_LineIdentifiers{ m.m_LineIdentifiers },
	m_LineDef{ m.m_LineDef },
	m_IncidenceConstr{ m.m_IncidenceConstr },
	m_DistanceDef{ m.m_DistanceDef },
	m_BetweennessConstr{ m.m_BetweennessConstr } 
{
	m_PointDef.linkVars(&m_SolvedVariables, {point});
	m_LineDef.linkVars(&m_SolvedVariables, {line});
	m_IncidenceConstr.linkVars(&m_SolvedVariables, {point, line});
	m_DistanceDef.linkVars(&m_SolvedVariables, {point, point});
	m_BetweennessConstr.linkVars(&m_SolvedVariables, {point, point, point});
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
	m_Elements.push_back(NEElement(std::vector<float>{}, eq, 0, notype, shared_from_this(), colour, false));
}

NELine Model::newLine(NEPoint p1, NEPoint p2) {
	Equation halfEq = m_IncidenceConstr;
	halfEq.m_NumberedVarNames.erase(std::next(halfEq.m_NumberedVarNames.begin()));
	Equation eq = halfEq + halfEq;
	Equation tmp = { {}, AdvancedString("l1 = 0") };
	eq = eq + tmp;
	eq.m_EquationString = AdvancedString("((pa0-l0)^2+(pa1-l1)^2=(1/(-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1))+0.5*(2~(l0^2+l1^2))+0.5*2~((2~(l0^2+l1^2))^2-1))^2)&(l1=0)");
	equationResult res = eq.getSolution({ p1.getIdentifiers(), p2.getIdentifiers() }, { p1.getID(), p2.getID() });
	if (!res.sat) {
		throw std::invalid_argument("I-1 failed");
	}
	for (int i = 0; i < res.m->num_consts(); ++i) {
		z3::func_decl f = res.m->get_const_decl(i);
		std::cout << f.name() << std::endl;
	}

	return { { 1.25, 0 }, p1.getModel() };
}

bool operator==(const NEElement& lhs, const NEElement& rhs) {
	if (lhs.getModel() != rhs.getModel()) {
		//Later isomorphism
		return false;
	}

	if (lhs.getType() != rhs.getType()) {
		return false;
	}

	if (lhs.getIdentifiers() == rhs.getIdentifiers()) {
		return true;
	}

	// If (x, y) exists for one element that doesn't exist for the other, the elements are not the same
	Equation constr1 = lhs.getDef() + !lhs.getDef();
	Equation constr2 = !lhs.getDef() + lhs.getDef();
	if (constr1.getSolution({ lhs.getIdentifiers(), rhs.getIdentifiers() }, { lhs.getID(), rhs.getID() }).sat or
		constr2.getSolution({ lhs.getIdentifiers(), rhs.getIdentifiers() }, { lhs.getID(), rhs.getID() }).sat) {
		return false;
	}
	else {
		return true;
	}
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
	return eq.isTrue({p.getIdentifiers(), l.getIdentifiers()}, { p.getID(), l.getID() });
}

float distance(const NEPoint& p1, const NEPoint& p2) {
	return p1.getModel()->m_DistanceDef.getResult({p1.getIdentifiers(), p2.getIdentifiers()}, { p1.getID(), p2.getID() });
}

bool isBetween(const NEPoint& p1, const NEPoint& p2, const NEPoint& p3) {
	if (p1.getModel() != p2.getModel() || p2.getModel() != p3.getModel()) {
		//Later isomorphism
		return false;
	}

	NELine l = p1.getModel()->newLine(p1, p2);
	// ToDo: fix line from two point

	//Custom condition
	Equation eq = p1.getModel()->m_BetweennessConstr;
	return eq.isTrue({ p1.getIdentifiers(), p2.getIdentifiers(), p3.getIdentifiers() }, { p1.getID(), p2.getID(), p2.getID() });
}

