#pragma once
#include <vector>

class Model;

/// Struct used to define a point belonging to a model g. 
/// Points can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
struct point { std::vector<float> identifiers; Model* g; };

/// Struct used to define a line belonging to a model g. 
/// Lines can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
struct line { std::vector<float> identifiers; Model* g; };

/**
* Class used to create a model for a geometry. 
* 
* Use member functions newPoint and newLine to create points and lines. 
* Use operator== and operator!= to compare points and lines. 
* Use operator>> to test incidence (point >> line). 
*/
class Model {
	std::vector<point> m_Points;
	std::vector<line> m_Lines;

	std::string m_PointConstraints;
	std::string m_LineConstraints;

	std::string m_PointEqualConstraints;
	std::string m_LineEqualConstraints;

	std::string m_IncidenceConstraints;

	unsigned int m_PointIdentifiers;
	unsigned int m_LineIdentifiers;

public:
	/**
	* Create new model by providing the necessary constraints. 
	* 
	* @param pointIdentifiers The amount of identifiers a point uses. 
	* @param pointConstraints A string with the constraints for a valid point. 
	* @param pointEqualConstraints A string with the condition for two point to be called equal. 
	* @param lineIdentifiers The amount of identifiers a line uses. 
	* @param lineConstraints A string with the constraints for a valid line. 
	* @param lineEqualConstraints A string with the condition for two lines to be called equal. 
	* @param incidenceConstraints A string with the condition for a point to lie on a line, tested using operator>>. 
	*/
	Model(unsigned int pointIdentifiers, 
		std::string pointConstraints,
		std::string pointEqualConstraints,
		unsigned int lineIdentifiers,
		std::string lineConstraints,
		std::string lineEqualConstraints,
		std::string incidenceConstraints);

	/// Copy an existing Model object. 
	Model(Model& g);

	/**
	* Create a new point. 
	* 
	* @param identifiers A vector containing the floats used to identify the point, the amount of identifiers are determined when creating the model class
	* @return Returns a point struct used to identify the point
	*/
	point newPoint(std::vector<float> identifiers);

	/**
	* Create a new line.
	*
	* @param identifiers A vector containing the floats used to identify the point, the amount of identifiers are determined when creating the model class
	* @return Returns a line struct used to identify the point
	*/
	line newLine(std::vector<float> identifiers);

	friend bool operator==(const point lhs, const point rhs);
	friend bool operator==(const line lhs, const line rhs);
	friend bool operator>>(const point p, const line l);
};

bool operator==(const point lhs, const point rhs);
bool operator==(const line lhs, const line rhs);
bool operator!=(const point lhs, const point rhs);
bool operator!=(const line lhs, const line rhs);

/// Incidence check: Checks if point p lies on line l. 
bool operator>>(const point p, const line l);
