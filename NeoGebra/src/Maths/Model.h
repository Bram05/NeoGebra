#pragma once
#include <vector>
#include <string>
#include "Equation.h"

class Model;
class NEElement;
class NEPoint;
class NELine;

enum NEType
{
	notype, point, line
};

struct RGBColour
{
	uint8_t r, g, b, a;
	float norm_r, norm_g, norm_b, norm_a;
	RGBColour();
	RGBColour(uint8_t r, uint8_t g, uint8_t b, uint8_t a);
	RGBColour(int r, int g, int b, int a);
	RGBColour(const RGBColour& c);
};

class NEElement {
protected:
	NEType m_Type;
	int m_ID;
	std::vector<float> m_Identifiers;
	Equation m_Def;
	RGBColour m_Colour;
	std::shared_ptr<Model> m_Model;
	NEElement(const std::vector<float>& identifiers, const Equation& def, const int identNum, NEType type, std::shared_ptr<Model> model, const RGBColour& colour, bool checkValidity);
public:
	virtual ~NEElement() {}
	const std::vector<float>& getIdentifiers() const { return NEElement::m_Identifiers; }
	const Equation& getDef() const { return NEElement::m_Def; }
	std::shared_ptr<Model> getModel() const { return NEElement::m_Model; }
	OrAnd getShader();
	int getID() const { return m_ID; }
	NEType getType() const { return m_Type; }
	RGBColour getColour() const { return m_Colour; }
	void setColour(const RGBColour& c) { m_Colour = c; }

	friend Model;
};

/// class used to define a point belonging to a model m. 
/// Points can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
class NEPoint : public NEElement {
public:
	NEPoint(const std::vector<float>& identifiers, std::shared_ptr<Model> m, const RGBColour& colour = { 0,0,0,255 }, bool checkValidity = false); //ToDo: default = random colour based on id
};

/// class used to define a line belonging to a model m. 
/// Lines can be compared using operator== and operator!= and incidence can be tested using operator>> (point >> line). 
class NELine : public NEElement {
public:
	NELine(const std::vector<float>& identifiers, std::shared_ptr<Model> m, const RGBColour& colour = { 0,0,0,255 }, bool checkValidity = false);
};

/**
* Class used to create a model for a geometry.
*
* Use member functions newPoint and newLine to create points and lines.
* Use operator== and operator!= to compare points and lines.
* Use operator>> to test incidence (point >> line).
*/
class Model : public std::enable_shared_from_this<Model> {
	std::vector<NEElement> m_Elements;

	Equation m_PointDef;
	Equation m_LineDef;
	Equation m_IncidenceConstr;
	Equation m_BetweennessConstr;

	unsigned int m_PointIdentifiers;
	unsigned int m_LineIdentifiers;

	std::vector<NEElement> m_ExtraEquations;

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
		const Equation& pointDef,
		unsigned int lineIdentifiers,
		const Equation& lineDef,
		const Equation& incidenceConstr,
		const Equation& betweennessConstr = Equation( {}, {} ));

	/// Copy an existing Model object. 
	Model(const Model& g);

	void addExtraEquation(Equation& eq, const RGBColour& colour = RGBColour(125, 125, 125, 255));
	std::vector<NEElement>& getExtraEquations() { return m_ExtraEquations; }

	std::vector<NEElement>& getElements() { return m_Elements; }
	unsigned int GetNumPointIdentifiers() const { return m_PointIdentifiers; }
	const Equation& GetPointDef() const { return m_PointDef; }
	unsigned int GetNumLineIdentifiers() const { return m_LineIdentifiers; }
	const Equation& GetLineDef() const { return m_LineDef; }
	const Equation& GetIncidenceConstr() const { return m_IncidenceConstr; }
	const Equation& GetBetweennessConstr() const { return m_BetweennessConstr; }

	NELine newLine(NEPoint p1, NEPoint p2);

	friend bool operator==(const NEElement& lhs, const NEElement& rhs);
	friend bool operator>>(const NEPoint& p, const NELine& l);
	friend bool isBetween(const NEPoint& p1, const NEPoint& p2, const NEPoint& p3);
	friend NEElement;
	friend NEPoint;
	friend NELine;
};

bool operator==(const NEElement& lhs, const NEElement& rhs);
bool operator!=(const NEElement& lhs, const NEElement& rhs);
bool operator==(const RGBColour& c1, const RGBColour& c2);
bool operator!=(const RGBColour& c1, const RGBColour& c2);

/// Incidence check: Checks if point p lies on line l. 
bool operator>>(const NEPoint& p, const NELine& l);
bool isBetween(const NEPoint& p1, const NEPoint& p2, const NEPoint& p3);