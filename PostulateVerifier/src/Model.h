//#pragma once
//#include <vector>
//#include <string>
//#include "Z3Tools.h"
//
//class Model;
//
///// Struct used to define a point belonging to a model m. 
///// Points can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
//struct point { std::vector<float> identifiers; Model* m; };
//
///// Struct used to define a line belonging to a model m. 
///// Lines can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
//struct line { std::vector<float> identifiers; Model* m; };
//
///**
//* Class used to create a model for a geometry. 
//* 
//* Use member functions newPoint and newLine to create points and lines. 
//* Use operator== and operator!= to compare points and lines. 
//* Use operator>> to test incidence (point >> line). 
//*/
//class Model {
//	std::vector<point> m_Points;
//	std::vector<line> m_Lines;
//
//	equation m_PointDef;
//	equation m_LineDef;
//	equation m_IncidenceConstr;
//	equation m_BetweennessConstr;
//
//	unsigned int m_PointIdentifiers;
//	unsigned int m_LineIdentifiers;
//
//public:
//	/**
//	* Create new model by providing the necessary constraints. 
//	* 
//	* @param pointIdentifiers The amount of identifiers a point uses. 
//	* @param pointConstr A string with the constraints for a valid point. 
//	* @param pointEqualConstr A string with the condition for two point to be called equal. 
//	* @param lineIdentifiers The amount of identifiers a line uses. 
//	* @param lineConstr A string with the constraints for a valid line. 
//	* @param lineEqualConstr A string with the condition for two lines to be called equal. 
//	* @param incidenceConstr A string with the condition for a point to lie on a line, tested using operator>>. 
//	*/
//	Model(unsigned int pointIdentifiers,
//		const equation& pointDef,
//		unsigned int lineIdentifiers,
//		const equation& lineDef,
//		const equation& incidenceConstr,
//		const equation& betweennessConstr = { {}, ""});
//
//	/// Copy an existing Model object. 
//	Model(const Model& g);
//
//	/**
//	* Create a new point. 
//	* 
//	* @param identifiers A vector containing the floats used to identify the point, the amount of identifiers are determined when creating the model class
//	* @return Returns a point struct used to identify the point
//	*/
//	point newPoint(const std::vector<float>& identifiers);
//	point newPoint(line l1, line l2);
//
//	/**
//	* Create a new line.
//	*
//	* @param identifiers A vector containing the floats used to identify the point, the amount of identifiers are determined when creating the model class
//	* @return Returns a line struct used to identify the point
//	*/
//	line newLine(const std::vector<float>& identifiers);
//	line newLine(point p1, point p2);
//
//	friend bool operator==(const point lhs, const point rhs);
//	friend bool operator==(const line lhs, const line rhs);
//	friend bool operator>>(const point p, const line l);
//	friend bool isBetween(const point p1, const point p2, const point p3);
//};
//
//bool operator==(const point lhs, const point rhs);
//bool operator==(const line lhs, const line rhs);
//bool operator!=(const point lhs, const point rhs);
//bool operator!=(const line lhs, const line rhs);
//
///// Incidence check: Checks if point p lies on line l. 
//bool operator>>(const point p, const line l);
//bool isBetween(const point p1, const point p2, const point p3);
