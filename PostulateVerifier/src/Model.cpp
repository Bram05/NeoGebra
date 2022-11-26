#include "Model.h"
#include "Z3Tools.h"


Model::Model(unsigned int pointIdentifiers,
	std::string pointConstraints,
	std::string pointEqualConstraints,
	unsigned int lineIdentifiers,
	std::string lineConstraints,
	std::string lineEqualConstraints,
	std::string incidenceConstraints) 
	: 
	m_PointIdentifiers{ pointIdentifiers },
	m_PointConstraints{ pointConstraints },
	m_PointEqualConstraints{ pointEqualConstraints },
	m_LineIdentifiers{ lineIdentifiers },
	m_LineConstraints{ lineConstraints },
	m_LineEqualConstraints{ lineEqualConstraints },
	m_IncidenceConstraints{ incidenceConstraints }
{

};

Model::Model(Model& g) {
	m_PointIdentifiers = g.m_PointIdentifiers;
	m_PointConstraints = g.m_PointConstraints;
	m_PointEqualConstraints = g.m_PointEqualConstraints;
	m_LineIdentifiers = g.m_LineIdentifiers;
	m_LineConstraints = g.m_LineConstraints;
	m_LineEqualConstraints = g.m_LineEqualConstraints;
	m_IncidenceConstraints = g.m_IncidenceConstraints;
}

point Model::newPoint(std::vector<float> identifiers) {
	//Creates a new point and returns the identifier
	if (identifiers.size() != m_PointIdentifiers) {
		throw std::invalid_argument("Invalid point");
	}

	//Check additional constraints
	std::string eq = m_PointConstraints;
	if (!Z3Tools::eval(eq, Z3Tools::Z3Tools::extractVars(eq, std::vector<std::vector<float>>{identifiers}))) {
		std::cout << "Invalid point:\n" << eq << std::endl;
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

line Model::newLine(std::vector<float> identifiers) {
	//Creates a new line and returns the identifier
	if (identifiers.size() != m_LineIdentifiers) {
		throw std::invalid_argument("Invalid line");
	}

	//Check additional constraints
	std::string eq = m_LineConstraints;
	if (!Z3Tools::eval(eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{identifiers}))) {
		std::cout << "Invalid point:\n" << eq << std::endl;
		throw std::invalid_argument("Invalid point");
	}

	//Check if line already exists
	line l{ identifiers, this };
	for (line l2 : m_Lines) {
		if (l == l2) {
			return l2;
		}
	}
	m_Lines.push_back(l);
	return l;
}

bool operator==(const point lhs, const point rhs) {
	if (lhs.g != rhs.g) {
		//Later isomorphism
		return false;
	}

	//Custom condition, maybe later problems with float comparison
	std::string eq = (*lhs.g).m_PointEqualConstraints;
	return Z3Tools::eval(eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{lhs.identifiers, rhs.identifiers}));
}

bool operator==(const line lhs, const line rhs) {
	if (lhs.g != rhs.g) {
		//Later isomorphism
		return false;
	}

	//Custom condition, maybe later problems with float comparison
	std::string eq = (*lhs.g).m_LineEqualConstraints;
	return Z3Tools::eval(eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{lhs.identifiers, rhs.identifiers}));
}

bool operator!=(const point lhs, const point rhs) { return !(lhs == rhs); }
bool operator!=(const line lhs, const line rhs) { return !(lhs == rhs); }

bool operator>>(const point p, const line l) {
	if (p.g != l.g) {
		//Later isomorphism
		return false;
	}
	//Custom condition, maybe later problems with float comparison
	std::string eq = (*p.g).m_IncidenceConstraints;
	return Z3Tools::eval(eq, Z3Tools::extractVars(eq, std::vector<std::vector<float>>{p.identifiers, l.identifiers}));
}