#pragma once
#include <vector>
#include <string>
#include "Z3Tools.h"

class Model;
class NEElement;
class NEPoint;
class NELine;

enum NEType
{
	notype, point, line
};

struct Colour
{
	uint8_t r, g, b, a;
	float norm_r, norm_g, norm_b, norm_a;
	Colour(uint8_t r, uint8_t g, uint8_t b, uint8_t a)
		: r{ r }, g{ g }, b{ b }, a{ a },
		norm_r{ r / float(255) }, norm_g{ g / float(255) }, norm_b{ b / float(255) }, norm_a{ a / float(255) } {}
	Colour(int r, int g, int b, int a) 
		: Colour(static_cast<uint8_t>(r), static_cast<uint8_t>(g), static_cast<uint8_t>(b), static_cast<uint8_t>(a)) {}
};

class NEElement {
protected:
	NEType m_Type;
	int m_ID;
	std::vector<float> m_Identifiers; 
	equation m_Def;
	Colour m_Colour;
	Model* m_Model; 
	NEElement(const std::vector<float>& identifiers, const equation& def, const int identNum, NEType type, Model* model, const Colour& colour); 
public:
	const std::vector<float>& getIdentifiers() const { return NEElement::m_Identifiers; }
	const equation& getDef() const { return NEElement::m_Def; }
	Model* getModel() const { return NEElement::m_Model; }
	std::string getShader();
	int getID() const { return m_ID; }
	NEType getType() const { return m_Type; }
	Colour getColour() const { return m_Colour; }
	void setColour(const Colour& c) { m_Colour = c; }
};

/// class used to define a point belonging to a model m. 
/// Points can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
class NEPoint : public NEElement {
public:
	NEPoint(const std::vector<float>& identifiers, Model* m, const Colour& colour = { 0,0,0,255 }); //ToDo: default = random colour based on id
};

/// class used to define a line belonging to a model m. 
/// Lines can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
class NELine : public NEElement {
public:
	NELine(const std::vector<float>& identifiers, Model* m, const Colour& colour = { 0,0,0,255 });
};

/**
* Class used to create a model for a geometry.
*
* Use member functions newPoint and newLine to create points and lines.
* Use operator== and operator!= to compare points and lines.
* Use operator>> to test incidence (point >> line).
*/
class Model {
	std::vector<NEElement> m_Elements;

	equation m_PointDef;
	equation m_LineDef;
	equation m_IncidenceConstr;
	equation m_BetweennessConstr;

	unsigned int m_PointIdentifiers;
	unsigned int m_LineIdentifiers;

public:
	/**
	* Create new model by providing the necessary constraints.
	*
	* @param pointIdentifiers The amount of identifiers a point uses.
	* @param pointConstr A string with the constraints for a valid point.
	* @param pointEqualConstr A string with the condition for two point to be called equal.
	* @param lineIdentifiers The amount of identifiers a line uses.
	* @param lineConstr A string with the constraints for a valid line.
	* @param lineEqualConstr A string with the condition for two lines to be called equal.
	* @param incidenceConstr A string with the condition for a point to lie on a line, tested using operator>>.
	*/
	Model(unsigned int pointIdentifiers,
		const equation& pointDef,
		unsigned int lineIdentifiers,
		const equation& lineDef,
		const equation& incidenceConstr,
		const equation& betweennessConstr = { {}, "" });

	/// Copy an existing Model object. 
	Model(const Model& g);

	const std::vector<NEElement>& getElements() const { return m_Elements; }

	NELine newLine(NEPoint p1, NEPoint p2);

	friend bool operator==(const NEElement lhs, const NEElement rhs);
	friend bool operator>>(const NEPoint p, const NELine l);
	friend bool isBetween(const NEPoint p1, const NEPoint p2, const NEPoint p3);
	friend NEElement;
	friend NEPoint;
	friend NELine;
};

bool operator==(const NEElement lhs, const NEElement rhs);
bool operator!=(const NEElement lhs, const NEElement rhs);

/// Incidence check: Checks if point p lies on line l. 
bool operator>>(const NEPoint p, const NELine l);
bool isBetween(const NEPoint p1, const NEPoint p2, const NEPoint p3);