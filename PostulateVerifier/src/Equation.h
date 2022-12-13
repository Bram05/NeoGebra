#pragma once

#include "z3++.h"
#include <regex>
#include <set>

struct equationResult { bool sat; z3::model* m; };

class Equation 
{
private:
	float		  recIsTrue(const std::string& s, const std::map<std::string, float>& vars) const;
	std::string recToSmtLib(const std::string& s, const std::map<std::string, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, bool isFirstLayer = false) const;
	std::string recToShader(const std::string& s, const std::map<std::string, float>& vars) const;
	int getNextOperator(const std::string& s, bool& orEquals) const;

	/**
	* Extracts variable names stored at the beginning of the equation.
	*
	* Variable names are stored at the beginning of the equation in the following format:
	*	"name1$name2$name3$ equation"
	* (Not space sensitive).
	* The input string will be modified, the varNames and spaces will be removed.
	*
	* @param s[out] String containing equation, will be modified.
	* @param identifiers[in] Vector containing vector of floats for every variable name, if the variable names p and q are used in p0, p1 and q0, identifiers would be { {0.5, 0.1}, {0.3} }.
	* @return Returns map of variable names and their values.
	*/
	std::map<std::string, float> linkVars(const std::vector<std::vector<float>>& identifiers) const;
	void replaceVarName(std::string& s, const std::string& from, const std::string& to);

public:
	std::vector<std::string> m_VarNames;
	std::string m_EquationString;
	Equation(const Equation& e1, const Equation& e2);
	Equation(std::vector<std::string> varNames, std::string equationString);

	/**
	* Recursive function used to check if equation in string form is true. Input string must not contain spaces.
	*
	* @param s String containing the equation, may contain floats, variables mentioned in vars, t and f (true and false), <, <=, >, >=, =, !=, +, -, *, /, ^, ~ (sqrt), &, |, [] (abs).
	* @param vars Map containing varnames and their values.
	* @return Returns float with 1 or 0 (true or false).
	*/
	equationResult getSolution(const std::vector<std::vector<float>>& identifiers) const;

	bool isTrue(const std::vector<std::vector<float>>& identifiers) const;
	std::string toSmtLib(const std::vector<std::vector<float>>& identifiers) const;
	std::string toShader(const std::vector<std::vector<float>>& identifiers) const;
};

Equation operator+(const Equation e1, const Equation e2);
Equation operator!(const Equation e);