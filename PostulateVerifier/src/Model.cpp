#include "Model.h"
#include "Z3Tools.h"


Model::Model(unsigned int pointIdentifiers,
	const std::string& pointDef,
	unsigned int lineIdentifiers,
	const std::string& lineDef,
	const std::string& incidenceConstr)
	: 
	m_PointIdentifiers{ pointIdentifiers },
	m_PointDef{ pointDef },
	m_LineIdentifiers{ lineIdentifiers },
	m_LineDef{ lineDef },
	m_IncidenceConstr{ incidenceConstr }
{

};

Model::Model(const Model& g) {
	m_PointIdentifiers = g.m_PointIdentifiers;
	m_PointDef = g.m_PointDef;
	m_LineIdentifiers = g.m_LineIdentifiers;
	m_LineDef = g.m_LineDef;
	m_IncidenceConstr = g.m_IncidenceConstr;
}

point Model::newPoint(const std::vector<float>& identifiers) {
	if (identifiers.size() != m_PointIdentifiers) {
		throw std::invalid_argument("Invalid point");
	}

	if (!Z3Tools::isSolvable(m_PointDef, { identifiers })) {
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

	if (!Z3Tools::isSolvable(m_LineDef, { identifiers })) {
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

//line newLine(point p1, point p2) {
//
//}

bool operator==(const point lhs, const point rhs) {
	if (lhs.m != rhs.m) {
		//Later isomorphism
		return false;
	}

	//ToDo If not (x, y) exists such that lhs.m_PointDef == true & yhs.m_PointDef != true and the opposite
	return false;
}

bool operator==(const line lhs, const line rhs) {
	if (lhs.m != rhs.m) {
		//Later isomorphism
		return false;
	}

	//ToDo If not (x, y) exists such that lhs.m_PointDef == true & yhs.m_PointDef != true and the opposite
	return false;
}

bool operator!=(const point lhs, const point rhs) { return !(lhs == rhs); }
bool operator!=(const line lhs, const line rhs) { return !(lhs == rhs); }

bool operator>>(const point p, const line l) {
	if (p.m != l.m) {
		//Later isomorphism
		return false;
	}

	//Custom condition
	std::string eq = (*p.m).m_IncidenceConstr;
	return Z3Tools::eval(eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{p.identifiers, l.identifiers}));
}