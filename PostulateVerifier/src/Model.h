#pragma once
#include <vector>

class Model;

struct point { std::vector<int> indentifiers; Model* g; };
struct line { std::vector<int> indentifiers; Model* g; };

class Model {
	//Class for defining geometries
	std::vector<std::string>* m_PointContstraints;
	std::vector<std::string>* m_LineContstraints;

	std::vector<std::string>* m_PointEqualContstraints;
	std::vector<std::string>* m_LineEqualContstraints;
	
	std::vector<std::string>* m_IncidenceContstraints;
	
	unsigned int m_PointIdentifiers;
	unsigned int m_LineIdentifiers;

	std::vector<point> m_Points;
	std::vector<line> m_Lines;

public:
	Model(unsigned int pointIdentifiers, 
		std::vector<std::string>* pointConstraints,
		std::vector<std::string>* pointEqualContstraints,
		unsigned int lineIdentifiers,
		std::vector<std::string>* lineConstraints,
		std::vector<std::string>* lineEqualContstraints,
		std::vector<std::string>* incidenceContstraints);

	point newPoint(std::vector<int> identifiers);
	line newLine(std::vector<int> identifiers);
};

bool operator==(const point lhs, const point rhs);
bool operator==(const line lhs, const line rhs);
bool operator!=(const point lhs, const point rhs);
bool operator!=(const line lhs, const line rhs);

bool operator>>(const point p, const line l);
