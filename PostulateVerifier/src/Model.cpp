#include "Model.h"
#include "Z3Tools.h"


Model::Model(unsigned int pointIdentifiers,
	std::vector<std::string>* pointConstraints,
	std::vector<std::string>* pointEqualConstraints,
	unsigned int lineIdentifiers,
	std::vector<std::string>* lineConstraints,
	std::vector<std::string>* lineEqualConstraints,
	std::vector<std::string>* incidenceConstraints) 
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

point Model::newPoint(std::vector<int> identifiers) {
	//Creates a new point and returns the identifier
	if (identifiers.size() != m_PointIdentifiers) {
		throw std::invalid_argument("Invalid point");
	}

	//Check additional constraints
	for (int i{}; i < m_PointConstraints->size(); ++i) {
		std::string constraint = m_PointConstraints->at(i);
		for (unsigned int p{ 1 }; p <= m_PointIdentifiers; ++p) {


			std::size_t loc = constraint.find('p' + std::to_string(p));
			while (loc != std::string::npos) {
				constraint.replace(loc, 2, std::to_string(identifiers[p - 1]));
				loc = constraint.find('p' + std::to_string(p));
			}
		}
		if (!verifyString(constraint)) {
			std::cout << "Invalid point:\n" << constraint << std::endl;
			throw std::invalid_argument("Invalid point");
		}
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

line Model::newLine(std::vector<int> identifiers) {
	//Creates a new line and returns the identifier
	if (identifiers.size() != m_LineIdentifiers) {
		throw std::invalid_argument("Invalid line");
	}

	//Check additional constraints
	for (int i{}; i < m_LineConstraints->size(); ++i) {
		std::string constraint = m_LineConstraints->at(i);
		for (unsigned int p{ 1 }; p <= m_LineIdentifiers; ++p) {


			std::size_t loc = constraint.find('p' + std::to_string(p));
			while (loc != std::string::npos) {
				constraint.replace(loc, 2, std::to_string(identifiers[p - 1]));
				loc = constraint.find('p' + std::to_string(p));
			}
		}
		if (!verifyString(constraint)) {
			std::cout << "Invalid line:\n" << constraint << std::endl;
			throw std::invalid_argument("Invalid line");
		}
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
	//Custom condition
	if (lhs.indentifiers[0] == rhs.indentifiers[0]) {
		return true;
	}
	else {
		return false;
	}
}

bool operator==(const line lhs, const line rhs) { 
	if (lhs.g != rhs.g) {
		//Later isomorphism
		return false;
	}
	//Custom condition
	if ((lhs.indentifiers[0] == rhs.indentifiers[0] && lhs.indentifiers[1] == rhs.indentifiers[1]) or 
		(lhs.indentifiers[0] == rhs.indentifiers[1] && lhs.indentifiers[1] == rhs.indentifiers[0])) {
		return true;
	}
	else {
		return false;
	}
}

bool operator!=(const point lhs, const point rhs) { return !(lhs == rhs); }
bool operator!=(const line lhs, const line rhs) { return !(lhs == rhs); }

bool operator>>(const point p, const line l) {
	if (p.g != l.g) {
		//Later isomorphism
		return false;
	}
	//Custom condition
	if (l.indentifiers[0] == p.indentifiers[0] or l.indentifiers[1] == p.indentifiers[0]) {
		return true;
	}
	else {
		return false;
	}
}