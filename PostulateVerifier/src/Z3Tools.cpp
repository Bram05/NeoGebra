#include "Z3Tools.h"

#define OPERNUM 11
const char calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^' };

std::map<std::string, float> Z3Tools::extractVars(std::string& s, const std::vector<std::vector<float>>& identifiers) {
	replace(s, " ", "");
	std::map<std::string, float> m;
	size_t found = s.find('$');
	int i{};
	for (int j{}; found != std::string::npos; i = found + 1, found = s.find('$', i), ++j) {
		for (int k = 0; k < identifiers[j].size(); ++k) {
			m[s.substr(i, found - i) + std::to_string(k)] = identifiers[j][k];
		}
	}
	s = s.substr(i, s.length() - i);
	return m;
}

bool Z3Tools::isNumber(const std::string& str)
{
	return str.find_first_not_of("0123456789.-") == std::string::npos;
}

bool Z3Tools::replace(std::string& str, const std::string& from, const std::string& to) {
	size_t start_pos = str.find(from);
	if (start_pos == std::string::npos)
		return false;
	str.replace(start_pos, from.length(), to);
	replace(str, from, to);
	return true;
}

bool Z3Tools::floatCompare(float f1, float f2) {
	static constexpr auto epsilon = 1.0e-05f;
	if (std::abs(f1 - f2) <= epsilon)
		return true;
	return std::abs(f1 - f2) <= epsilon * std::max(std::abs(f1), std::abs(f2));
}

float Z3Tools::eval(const std::string& s, const std::map<std::string, float>& vars) {
	int depth = 0;
	int best = OPERNUM;
	int operIndex = -1;
	bool orEquals = false; // True if the > or < is a >= or <=
	for (int i{}; i < s.length(); ++i) {
		char c = s[i];
		if (c == '(' or c == '[') { depth += 1; }
		if (c == ')' or c == ']') { depth -= 1; }

		if (depth == 0) {
			const char* res = std::find(std::begin(calcOrder), std::begin(calcOrder) + best, c);
			if (res != std::begin(calcOrder) + best) {
				// If operator is '-', the program needs to check if there is another operator in front of it, such as 5*-3=-15
				// If operator is '!', the program needs to check if the operator is "!="
				if ((c != '-' or
						(i > 0 and (std::find(std::begin(calcOrder), std::end(calcOrder), s[i - 1]) == std::end(calcOrder)))) and
					(c != '!' or
						(i < s.length() - 1 and s[i + 1] == '='))) {
					if ((c == '>' or c == '<') and s[i + 1] == '=') { orEquals = true; }
					else { orEquals = false; }
					best = std::distance(calcOrder, res);
					operIndex = i;
				}
			}
		}
	}

	if (depth != 0) { throw std::invalid_argument("Invalid brackets"); }

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) {return std::stof(s);}
		if (s[0] != '-') {
			if (vars.count(s)) { return vars.at(s); }
			if (s[0] == '(' and s.back() == ')') { return eval(s.substr(1, s.length() - 2), vars); }
			if (s[0] == '[' and s.back() == ']') { return std::abs(eval(s.substr(1, s.length() - 2), vars)); }
			if (s[0] == '~') { return std::sqrt(eval(s.substr(1, s.length() - 1), vars)); }
			if (s[0] == '!') { return !eval(s.substr(1, s.length() - 1), vars); }
		} else {
			if (vars.count(s.substr(1, s.length() - 1))) { return -vars.at(s.substr(1, s.length() - 1)); }
			if (s[1] == '(' and s.back() == ')') { return -eval(s.substr(2, s.length() - 3), vars); }
			if (s[1] == '[' and s.back() == ']') { return -std::abs(eval(s.substr(2, s.length() - 3), vars)); }
			if (s[1] == '~') { return -std::sqrt(eval(s.substr(2, s.length() - 2), vars)); }
			if (s[1] == '!') { return -!eval(s.substr(2, s.length() - 2), vars); }
		}
		if (s == "t") { return true; }
		if (s == "f") { return false; }
		throw std::invalid_argument("Invalid operator");
	}

	std::string s1 = s.substr(0, operIndex);
	std::string s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return eval(s1, vars) or eval(s2, vars);
	case '&': return eval(s1, vars) and eval(s2, vars);
	case '!': return !floatCompare(eval(s1, vars), eval(s2.substr(1, s2.length() - 1), vars));
	case '>': 
		if (!orEquals) { return eval(s1, vars) > eval(s2, vars); }
		else { return eval(s1, vars) >= eval(s2.substr(1, s2.length() - 1), vars); }
	case '<': 
		if (!orEquals) { return eval(s1, vars) < eval(s2, vars); }
		else { return eval(s1, vars) <= eval(s2.substr(1, s2.length() - 1), vars); }
	case '=': return floatCompare(eval(s1, vars), eval(s2, vars));
	case '+': return eval(s1, vars) + eval(s2, vars);
	case '-': return eval(s1, vars) - eval(s2, vars);
	case '*': return eval(s1, vars) * eval(s2, vars);
	case '/': return eval(s1, vars) / eval(s2, vars);
	case '^': return std::pow(eval(s1, vars), eval(s2, vars));
	default:  throw std::invalid_argument("Invalid operator"); return -1;
	}
}