#pragma once

#include "z3++.h"
#include <regex>
#include <set>

struct equationResult { bool sat; z3::model* m; };
// String with extra characters, such as square roots and pi
struct AdvancedString {
	std::vector<unsigned int> content;
	AdvancedString() {}
	AdvancedString(const std::string& str) { for (const char c : str) { content.push_back(c); } }
	AdvancedString(const std::vector<unsigned int>& v) : content(v) {}
	AdvancedString(unsigned int c) : content({c}) {}
	AdvancedString(const AdvancedString& s) : content(s.content) {}
	size_t size() const { return content.size(); }
	size_t length() const { return content.size(); }
	bool empty() const { return content.empty(); }
	std::vector<unsigned int>::const_iterator begin() const { return content.begin(); }
	std::vector<unsigned int>::const_iterator end() const { return content.end(); }
	std::vector<unsigned int>::const_iterator erase(std::vector<unsigned int>::const_iterator b, std::vector<unsigned int>::const_iterator e) { return content.erase(b, e); }
	std::vector<unsigned int>::const_iterator insert(std::vector<unsigned int>::const_iterator a, const unsigned int c) { return content.insert(a, c); }
	std::vector<unsigned int>::const_iterator insert(std::vector<unsigned int>::const_iterator a, const std::string& s) { return content.insert(a, s.begin(), s.end()); }
	std::vector<unsigned int>::const_iterator insert(std::vector<unsigned int>::const_iterator a, std::vector<unsigned int>::const_iterator b, std::vector<unsigned int>::const_iterator e) { return content.insert(a, b, e); }
	AdvancedString substr(size_t pos, size_t count) const { return AdvancedString(std::vector<unsigned int>(content.begin()+pos, content.begin()+pos+count)); }
	std::string toString() const { std::string res; for (int c : content) { res.push_back((char)c); } return res; }
	float toFloat() const { return std::stof(toString()); }
	unsigned int back() const { return content[content.size() - 1]; }
	void push_back(const unsigned int& val) { content.push_back(val); }
	unsigned int operator [](int i) const { return content[i]; }
	unsigned int& operator [](int i) { return content[i]; }
};

void replaceAll(AdvancedString& str, const AdvancedString& from, const AdvancedString& to);

class Equation
{
private:
	float		  recIsTrue(const AdvancedString& s, const std::map<AdvancedString, float>& vars) const;
	std::string recToSmtLib(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, bool isFirstLayer = false) const;
	std::string recToShader(const AdvancedString& s, const std::map<AdvancedString, float>& vars) const;
	int		getNextOperator(const AdvancedString& s, bool& orEquals) const;

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
	std::map<AdvancedString, float> linkVars(const std::vector<std::vector<float>>& identifiers) const;
	void replaceVarName(AdvancedString& s, const AdvancedString& from, const AdvancedString& to);

public:
	std::vector<AdvancedString> m_VarNames;
	AdvancedString m_EquationString;
	Equation(const Equation& e1, const Equation& e2);
	Equation(const std::vector<AdvancedString>& varNames, const AdvancedString& equationString);

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

Equation operator+(const Equation& e1, const Equation& e2);
Equation operator!(const Equation& e);

AdvancedString operator+(const AdvancedString& s1, const AdvancedString& s2);
AdvancedString operator+(const AdvancedString& s1, const std::string& s2);
AdvancedString operator+(const std::string& s1, const AdvancedString& s2);
bool operator==(const AdvancedString& s1, const AdvancedString& s2);
bool operator==(const AdvancedString& s1, const std::string& s2);
bool operator==(const std::string& s1, const AdvancedString& s2);

bool operator<(const AdvancedString& s1, const AdvancedString& s2);