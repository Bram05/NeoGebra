#include "Model.h"
#include "Z3Tools.h"

Model::Model(unsigned int pointIdentifiers,
	const equation& pointDef,
	unsigned int lineIdentifiers,
	const equation& lineDef,
	const equation& incidenceConstr,
	const equation& betweennessConstr)
	:
	m_PointIdentifiers{ pointIdentifiers },
	m_PointDef{ pointDef },
	m_LineIdentifiers{ lineIdentifiers },
	m_LineDef{ lineDef },
	m_IncidenceConstr{ incidenceConstr },
	m_BetweennessConstr{ betweennessConstr } {}

Model::Model(const Model& m) :
	m_PointIdentifiers{ m.m_PointIdentifiers },
	m_PointDef{ m.m_PointDef },
	m_LineIdentifiers{ m.m_LineIdentifiers },
	m_LineDef{ m.m_LineDef },
	m_IncidenceConstr{ m.m_IncidenceConstr },
	m_BetweennessConstr{ m.m_BetweennessConstr } {}

point Model::newPoint(const std::vector<float>& identifiers) {
	if (identifiers.size() != m_PointIdentifiers) {
		throw std::invalid_argument("Invalid point");
	}

	if (!Z3Tools::isSolvable(m_PointDef, { identifiers }).sat) {
		throw std::invalid_argument("Invalid point");
	}

	//Check if point already exists
	point p{ identifiers, this };
	for (point p2 : m_Points) {
		if (p == p2) {
			return p2;
		}
	}

	m_Points.push_back(p);
	return p;
}

//point newPoint(line l1, line l2) {
//	
//}

line Model::newLine(const std::vector<float>& identifiers) {
	if (identifiers.size() != m_LineIdentifiers) {
		throw std::invalid_argument("Invalid line");
	}

	if (!Z3Tools::isSolvable(m_LineDef, { identifiers }).sat) {
		throw std::invalid_argument("Invalid line");
	}

	//Check if point already exists
	line l{ identifiers, this };
	for (line l2 : m_Lines) {
		if (l == l2) {
			return l2;
		}
	}

	m_Lines.push_back(l);
	return l;
}

line Model::newLine(point p1, point p2) {
	equation halfEq = m_IncidenceConstr;
	halfEq.vars.erase(std::next(halfEq.vars.begin()));
	equation eq = halfEq + halfEq;
	equationResult res = Z3Tools::isSolvable(eq, { p1.identifiers, p2.identifiers });
	if (!res.sat) {
		throw std::invalid_argument("I-1 failed");
	}
	for (int i = 0; i < (*res.m).num_consts(); ++i) {
		z3::func_decl f = (*res.m).get_const_decl(i);
		std::cout << f.name() << std::endl;

	}

	return newLine({ 1.25, 0 });
}

bool operator==(const point lhs, const point rhs) {
	if (lhs.m != rhs.m) {
		//Later isomorphism
		return false;
	}

	equation constr1 = (*lhs.m).m_PointDef + !(*lhs.m).m_PointDef;
	equation constr2 = !(*lhs.m).m_PointDef + (*lhs.m).m_PointDef;
	if (Z3Tools::isSolvable(constr1, { lhs.identifiers, rhs.identifiers }).sat or
		Z3Tools::isSolvable(constr2, { lhs.identifiers, rhs.identifiers }).sat) {
		return false;
	}
	else {
		return true;
	}
}

bool operator==(const line lhs, const line rhs) {
	if (lhs.m != rhs.m) {
		//Later isomorphism
		return false;
	}

	equation constr1 = (*lhs.m).m_LineDef + !(*lhs.m).m_LineDef;
	equation constr2 = !(*lhs.m).m_LineDef + (*lhs.m).m_LineDef;
	if (Z3Tools::isSolvable(constr1, { lhs.identifiers, rhs.identifiers }).sat or
		Z3Tools::isSolvable(constr2, { lhs.identifiers, rhs.identifiers }).sat) {
		return false;
	}
	else {
		return true;
	}
}

bool operator!=(const point lhs, const point rhs) { return !(lhs == rhs); }
bool operator!=(const line lhs, const line rhs) { return !(lhs == rhs); }

bool operator>>(const point p, const line l) {
	if (p.m != l.m) {
		//Later isomorphism
		return false;
	}

	//Custom condition
	equation eq = (*p.m).m_IncidenceConstr;
	return Z3Tools::eval(eq.eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{p.identifiers, l.identifiers}));
}

bool isBetween(const point p1, const point p2, const point p3) {
	if (p1.m != p2.m || p2.m != p3.m) {
		//Later isomorphism
		return false;
	}

	//Check if the 3 points lie on the same line
	//std::string lineConstraints[3] = { (*p1.m).m_LineDef.eq, (*p1.m).m_LineDef.eq, (*p1.m).m_LineDef.eq };
	//equation pointEquations[3] = { (*p1.m).m_PointDef, (*p1.m).m_PointDef, (*p1.m).m_PointDef };
	//for (int i = 0; i < 3; ++i) {
	//	Z3Tools::replaceVar(lineConstraints[i], "x", std::string{ "x" } + (char)('a' + i));
	//	Z3Tools::replaceVar(lineConstraints[i], "y", std::string{ "y" } + (char)('a' + i));
	//	Z3Tools::replaceVar(pointEquations[i].eq, "x", std::string{ "x" } + (char)('a' + i));
	//	Z3Tools::replaceVar(pointEquations[i].eq, "y", std::string{ "y" } + (char)('a' + i));
	//}
	//
	//equation lineEq{ {}, lineConstraints[0] + '&' + lineConstraints[1] + '&' + lineConstraints[2] };
	//equation totalEq = pointEquations[0] + pointEquations[1] + pointEquations[2] + lineEq;
	//if (!Z3Tools::isSolvable(totalEq, { p1.identifiers, p2.identifiers, p3.identifiers }).sat) {
	//	return false;
	//}
	line l = (*p1.m).newLine(p1, p2);

	//Custom condition
	equation eq = (*p1.m).m_BetweennessConstr;
	return Z3Tools::eval(eq.eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{p1.identifiers, p2.identifiers, p3.identifiers}));
}