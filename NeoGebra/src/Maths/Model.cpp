#include "Model.h"
#include "Application.h"

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
		std::vector<std::string> resNames;
		for (int i = 0; i < identNum; ++i) {
			resNames.push_back(def.m_NumberedVarNames[0].toString() + std::to_string(i));
		}

		//if (!def.getSolution({ identifiers }, { m_ID }, resNames))
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
		m_Model->m_Elements.push_back(*this);
		m_Model->solveVariables(this);
	}
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
	const Equation& betweennessConstr,
	const EquationVector& lineFromPoints,
	const EquationVector& pointFromLines)
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
	m_PointDef.linkVars(&m_SolvedVariables, {point});
	m_LineDef.linkVars(&m_SolvedVariables, {line});
	m_IncidenceConstr.linkVars(&m_SolvedVariables, {point, line });
	m_DistanceDef.linkVars(&m_SolvedVariables, {point, point });
	m_BetweennessConstr.linkVars(&m_SolvedVariables, {point, point, point});
	for (Equation& e : m_LineFromPoints) {
		e.linkVars(&m_SolvedVariables, {point, point});
	}
	for (Equation& e : m_PointFromLines) {
		e.linkVars(&m_SolvedVariables, { line, line });
	}

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
	m_BetweennessConstr{ m.m_BetweennessConstr },
	m_LineFromPoints{ m.m_LineFromPoints },
	m_PointFromLines{ m.m_PointFromLines }
{
	m_PointDef.linkVars(&m_SolvedVariables, {point});
	m_LineDef.linkVars(&m_SolvedVariables, {line});
	m_IncidenceConstr.linkVars(&m_SolvedVariables, {point, line});
	m_DistanceDef.linkVars(&m_SolvedVariables, {point, point});
	m_BetweennessConstr.linkVars(&m_SolvedVariables, {point, point, point});
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
	m_Elements.push_back(NEElement(std::vector<float>{}, eq, 0, notype, shared_from_this(), colour, false));
}

NELine Model::lineFromPoints(const NEPoint& p1, const NEPoint& p2) {
	// If user defined equation is available, use it
	if (m_LineFromPoints.size() == m_LineIdentifiers) {
		std::vector<float> identifiers;
		for (int i = 0; i < m_LineIdentifiers; ++i) {
			identifiers.push_back(m_LineFromPoints[i].getResult({p1.getIdentifiers(), p2.getIdentifiers()}, { p1.getID(), p1.getID()}));
		}
		return NELine(identifiers, shared_from_this());
	}
	return NELine(generateXFromY(p1, p2), shared_from_this());
}

NEPoint Model::pointFromLines(const NELine& l1, const NELine& l2) {
	// If user defined equation is available, use it
	if (m_PointFromLines.size() == m_PointIdentifiers) {
		std::vector<float> identifiers;
		for (int i = 0; i < m_PointIdentifiers; ++i) {
			identifiers.push_back(m_PointFromLines[i].getResult({ l1.getIdentifiers(), l2.getIdentifiers() }, { l1.getID(), l1.getID() }));
		}
		return NEPoint(identifiers, shared_from_this());
	}
	return NEPoint(generateXFromY(l1, l2), shared_from_this());
}

std::vector<float> Model::generateXFromY(const NEElement& e1, const NEElement& e2)
{
	// Generate extra code for z3
	Equation eq = m_IncidenceConstr.diff(m_IncidenceConstr.m_NumberedVarNames[e1.getType() == line ? 0 : 1]);
	std::string extraSMT{};
	std::set<std::string> tmp;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::map<AdvancedString, float> tmp2;
	std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >> m = e1.getType() == line ? m_Variables.first : m_Variables.second;
	Equation& def = e1.getType() == line ? m_PointDef : m_LineDef;
	int definedSqrts = 0;
	extraSMT = "(assert " + def.recToSmtLib(def.m_EquationString, tmp2, tmp, sqrts, {}, true) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		std::string def = sqrts[i].first;
		std::string pow = sqrts[i].second;
		extraSMT = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + extraSMT;
	}
	extraSMT = "(declare-const x Real)(declare-const y Real)" + extraSMT;
	definedSqrts = sqrts.size();
	for (int i = m.size() - 1; i >= 0; --i) {
		extraSMT = "(define-fun " + m_IncidenceConstr.m_NumberedVarNames[e1.getType() == line ? 0 : 1].toString() + "." + m[i].first.toString() + " () Real " + m[i].second->recToSmtLib(m[i].second->m_EquationString, tmp2, tmp, sqrts, {}, true) + ")" + extraSMT;
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			std::string def = sqrts[i].first;
			std::string pow = sqrts[i].second;
			extraSMT = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + extraSMT;
		}
		definedSqrts = sqrts.size();
	}

	std::vector<std::string> resNames;
	for (int i = 0; i < (e1.getType() == line ? m_PointIdentifiers : m_LineIdentifiers); ++i) {
		resNames.push_back(def.m_NumberedVarNames[0].toString() + std::to_string(i));
	}

	//solve equation
	z3::context c;
	z3::solver solver(c);
	bool sat = eq.getSolution({ e1.getIdentifiers(), e2.getIdentifiers() }, { e1.getID(), e2.getID() }, resNames, &c, &solver, sqrts, extraSMT);
	if (!sat) {
		Application::Get()->GetWindowUI()->DisplayError("Solution not found");
		throw ErrorBoxException();
	}

	//Get output from z3
	z3::model model = solver.get_model();
	std::vector<float> identifiers(e1.getType() == line ? m_PointIdentifiers : m_LineIdentifiers);
	std::string varName = def.m_NumberedVarNames[0].toString();
	for (int i = 0; i < model.num_consts(); ++i) {
		z3::func_decl f = model.get_const_decl(i);
		if (varName == f.name().str().substr(0, varName.size()) && f.name().str().substr(varName.size(), f.name().str().size() - varName.size()).find_first_not_of("0123456789") == std::string::npos) {
			z3::expr fVal = model.get_const_interp(f);
			identifiers[std::stoi(f.name().str().substr(varName.size(), f.name().str().size() - varName.size()))] = fVal.as_double();
		}
	}
	//std::cout << "test" << std::endl;
	//std::cout << solver << '\n';
	//std::cout << model;
	return identifiers;
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
	std::vector<std::string> resNames;
	for (int i = 0; i < (lhs.getType() == line ? lhs.getModel()->m_PointIdentifiers : lhs.getModel()->m_LineIdentifiers); ++i) {
		resNames.push_back(constr1.m_NumberedVarNames[0].toString() + std::to_string(i));
		resNames.push_back(constr1.m_NumberedVarNames[1].toString() + std::to_string(i));
	}
	if (constr1.getSolution({ lhs.getIdentifiers(), rhs.getIdentifiers() }, { lhs.getID(), rhs.getID() }, resNames) or
		constr2.getSolution({ lhs.getIdentifiers(), rhs.getIdentifiers() }, { lhs.getID(), rhs.getID() }, resNames)) {
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

	//NELine l = p1.getModel()->newLine(p1, p2);
	// ToDo: fix line from two point

	//Custom condition
	Equation eq = p1.getModel()->m_BetweennessConstr;
	return eq.isTrue({ p1.getIdentifiers(), p2.getIdentifiers(), p3.getIdentifiers() }, { p1.getID(), p2.getID(), p2.getID() });
}

