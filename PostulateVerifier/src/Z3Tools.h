#pragma once

#include "z3++.h"

/**
* Static class with tools that help with solving equations (mostly in string form). 
*/
class Z3Tools {
	/// Compares two float numbers using a variable epsilon value. 
	static bool floatCompare(float f1, float f2);

	/// Checks if a string contains a signed float. 
	static bool isNumber(const std::string& str);

	/** 
	* Replace all instances of substring in string.
	* 
	* @param str[out] String to replace substring in. 
	* @param from[in] Substring that should be replaced. 
	* @param to[in] Substring to replace 'from' with. 
	*/
	static bool replace(std::string& str, const std::string& from, const std::string& to);

	static std::string recToLisp(const std::string& s, const std::map<std::string, float>& vars, std::vector<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts);

public:
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
	static std::map<std::string, float> extractVars(std::string& s, const std::vector<std::vector<float>>& identifiers);
	
	/**
	* Recursive function used to check if equation in string form is true. Input string must not contain spaces. 
	*
	* @param s String containing the equation, may contain floats, variables mentioned in vars, t and f (true and false), <, <=, >, >=, =, !=, +, -, *, /, ^, ~ (sqrt), &, |, [] (abs).
	* @param vars Map containing varnames and their values.
	* @return Returns float with 1 or 0 (true or false).
	*/
	static float eval(const std::string& s, const std::map<std::string, float>& vars);
	static bool isSolvable(std::string s, const std::vector<std::vector<float>>& identifiers);
	static std::string toLisp(const std::string& s, const std::map<std::string, float>& vars);
};