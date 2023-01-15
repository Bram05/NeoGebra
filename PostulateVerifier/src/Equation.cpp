#include "Equation.h"

#define OPERNUM 12
const char calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', '~' };

/// Checks if a string contains a signed float. 
bool isNumber(const std::string& str)
{
	return str.find_first_not_of("0123456789.-") == std::string::npos;
}

/**
	* Replace all instances of substring in string.
	*
	* @param from[in] Substring that should be replaced.
	* @param to[in] Substring to replace 'from' with.
*/
bool replaceAll(std::string& str, const std::string& from, const std::string& to) {
	size_t start_pos = str.find(from);
	if (start_pos == std::string::npos)
		return false;
	str.replace(start_pos, from.length(), to);
	replaceAll(str, from, to);
	return true;
}

/// Compares two float numbers using a variable epsilon value. 
bool floatCompare(float f1, float f2) {
	static constexpr auto epsilon = 1.0e-05f;
	if (std::abs(f1 - f2) <= epsilon)
		return true;
	return std::abs(f1 - f2) <= epsilon * std::max(std::abs(f1), std::abs(f2));
}

std::map<std::string, float> Equation::linkVars(const std::vector<std::vector<float>>& identifiers) const {
	if (m_VarNames.size() != identifiers.size()) {
		throw std::invalid_argument("Invalid identifiers");
	}
	
	std::map<std::string, float> m;
	for (int i = 0; i < m_VarNames.size(); ++i) {
		std::string varName = m_VarNames[i];
		for (int j = 0; j < identifiers[i].size(); ++j) {
			m[varName + std::to_string(j)] = identifiers[i][j];
		}
	}
	return m;
}

Equation::Equation(const std::vector<std::string>& varNames, const std::string& equationString) : m_VarNames{ varNames }, m_EquationString{ equationString }
{
	replaceAll(m_EquationString, " ", "");
}

Equation::Equation(const Equation& e1, const Equation& e2) {
	std::string s1 = e1.m_EquationString;
	std::string s2 = e2.m_EquationString;

	for (std::string var1 : e1.m_VarNames) {
		bool varNameAdded = false;
		for (std::string var2 : e2.m_VarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				m_VarNames.push_back(var1 + 'a');
				replaceVarName(s1, var1, var1 + 'a');
			}
		}
		if (!varNameAdded) {
			m_VarNames.push_back(var1);
		}
	}
	for (std::string var2 : e2.m_VarNames) {
		bool varNameAdded = false;
		for (std::string var1 : e1.m_VarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				m_VarNames.push_back(var2 + 'b');
				replaceVarName(s2, var2, var2 + 'b');
			}
		}
		if (!varNameAdded) {
			m_VarNames.push_back(var2);
		}
	}
	m_EquationString = "(" + s1 + ")&(" + s2 + ")";
}

void Equation::replaceVarName(std::string& s, const std::string& from, const std::string& to) {
	std::regex reg("(^|[\\(\\)\\[\\]|&!><=+\\-*\\^~])(" + from + ")([0-9]*)([\\(\\)\\[\\]|&!><=+\\-*\\^~]|$)");
	// Needs to be run twice in case matches overlap
	for (int i = 0; i < 2; ++i) {
		s = std::regex_replace(s, reg, "$1" + to + "$3$4");
	}
}

Equation operator+(const Equation& e1, const Equation& e2) {
	return Equation{ e1, e2 };
}

Equation operator!(const Equation& e) {
	return Equation{ e.m_VarNames, "!(" + e.m_EquationString + ")" };
}

equationResult Equation::getSolution(const std::vector<std::vector<float>>& identifiers) const {
	z3::context c;
	z3::solver solver(c);

	std::string smtLibString = toSmtLib(identifiers);
	Z3_ast_vector test2 = Z3_parse_smtlib2_string(c, smtLibString.c_str(), 0, 0, 0, 0, 0, 0);

	for (int i{}; i < Z3_ast_vector_size(c, test2); ++i) {
		z3::expr tmp(c, Z3_ast_vector_get(c, test2, i));
		solver.add(tmp);
	}

	//std::cout << solver << "\n";
	//std::cout << solver.to_smt2() << "\n\n::\n\n";
	switch (solver.check()) {
	case z3::sat: {z3::model m = solver.get_model(); return { true, &m }; }
	case z3::unsat: return { false, nullptr };
	case z3::unknown: throw std::invalid_argument("Error when resolving expression");
	default: return { false, nullptr };
	}
}

bool Equation::isTrue(const std::vector<std::vector<float>>& identifiers) const {
	std::map<std::string, float> vars = linkVars(identifiers);
	return recIsTrue(m_EquationString, vars);
}

std::string Equation::toSmtLib(const std::vector<std::vector<float>>& identifiers) const {
	std::set<std::string> toDefine;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::map<std::string, float> vars = linkVars(identifiers);
	std::string out = "(assert " + recToSmtLib(m_EquationString, vars, toDefine, sqrts, true) + ")(check-sat)";

	for (int i = sqrts.size() - 1; i >= 0; --i) {
		std::string def = sqrts[i].first;
		std::string pow = sqrts[i].second;
		out = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + out;
	}
	for (std::string var : toDefine) {
		out = "(declare-const " + var + " Real)" + out;
	}

	return "(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))" + out;
}

std::string Equation::toShader(const std::vector<std::vector<float>>& identifiers) const {
	std::map<std::string, float> vars = linkVars(identifiers);
	return recToShader(m_EquationString, vars);
}

float Equation::recIsTrue(const std::string& s, const std::map<std::string, float>& vars) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::stof(s); }
		if (s[0] != '-') {
			if (vars.count(s)) { return vars.at(s); }
			if (s[0] == '(' and s.back() == ')') { return recIsTrue(s.substr(1, s.length() - 2), vars); }
			if (s[0] == '[' and s.back() == ']') { return std::abs(recIsTrue(s.substr(1, s.length() - 2), vars)); }
			if (s[0] == '!') { return !recIsTrue(s.substr(1, s.length() - 1), vars); }
		}
		else {
			if (vars.count(s.substr(1, s.length() - 1))) { return -vars.at(s.substr(1, s.length() - 1)); }
			if (s[1] == '(' and s.back() == ')') { return -recIsTrue(s.substr(2, s.length() - 3), vars); }
			if (s[1] == '[' and s.back() == ']') { return -std::abs(recIsTrue(s.substr(2, s.length() - 3), vars)); }
		}
		if (s == "t") { return true; }
		if (s == "f") { return false; }
		throw std::invalid_argument("Invalid operator");
	}

	std::string s1 = s.substr(0, operIndex);
	std::string s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return recIsTrue(s1, vars) or recIsTrue(s2, vars);
	case '&': return recIsTrue(s1, vars) and recIsTrue(s2, vars);
	case '!': return !floatCompare(recIsTrue(s1, vars), recIsTrue(s2.substr(1, s2.length() - 1), vars));
	case '>':
		if (!orEquals) { return recIsTrue(s1, vars) > recIsTrue(s2, vars); }
		else { return recIsTrue(s1, vars) >= recIsTrue(s2.substr(1, s2.length() - 1), vars); }
	case '<':
		if (!orEquals) { return recIsTrue(s1, vars) < recIsTrue(s2, vars); }
		else { return recIsTrue(s1, vars) <= recIsTrue(s2.substr(1, s2.length() - 1), vars); }
	case '=': return floatCompare(recIsTrue(s1, vars), recIsTrue(s2, vars));
	case '+': return recIsTrue(s1, vars) + recIsTrue(s2, vars);
	case '-': return recIsTrue(s1, vars) - recIsTrue(s2, vars);
	case '*': return recIsTrue(s1, vars) * recIsTrue(s2, vars);
	case '/': return recIsTrue(s1, vars) / recIsTrue(s2, vars);
	case '^': return std::pow(recIsTrue(s1, vars), recIsTrue(s2, vars));
	case '~': return std::pow(recIsTrue(s2, vars), 1 / recIsTrue(s1, vars));
	default:  throw std::invalid_argument("Invalid operator");
	}
}

std::string Equation::recToSmtLib(const std::string& s, const std::map<std::string, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, bool isFirstLayer) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s; }
		if (s[0] != '-') {
			if (vars.count(s)) { return std::to_string(vars.at(s)); }
			if (s[0] == '(' and s.back() == ')') { return recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts); }
			if (s[0] == '[' and s.back() == ']') { return ("(abs " + recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts) + ')'); }
			if (s[0] == '!') { return ("(not " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts) + ')'); }
		}
		else {
			if (vars.count(s.substr(1, s.length() - 1))) { return std::to_string(-vars.at(s.substr(1, s.length() - 1))); }
			if (s[1] == '(' and s.back() == ')') { return ("(- " + recToSmtLib(s.substr(2, s.length() - 3), vars, toDefine, sqrts) + ")"); }
			if (s[1] == '[' and s.back() == ']') { return ("(- (abs " + recToSmtLib(s.substr(2, s.length() - 3), vars, toDefine, sqrts) + "))"); }
		}
		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		toDefine.insert(s);
		return s;
	}

	std::string s1 = s.substr(0, operIndex);
	std::string s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "(or " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '&': {
		if (isFirstLayer) {
			return recToSmtLib(s1, vars, toDefine, sqrts) + ")(assert " + recToSmtLib(s2, vars, toDefine, sqrts, true);
		}
		return "(and " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	}
	case '!': return "(not (feq " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + "))";
	case '>':
		if (!orEquals) { return "(> " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")"; }
		else { return "(>= " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts) + ")"; }
	case '<':
		if (!orEquals) { return "(< " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")"; }
		else { return "(<= " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts) + ")"; }
	case '=': return "(feq " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '+': return "(+ " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '-': return "(- " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '*': return "(* " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '/': return "(/ " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")";
	case '^': return "(^ " + recToSmtLib(s1, vars, toDefine, sqrts) + " " + recToSmtLib(s2, vars, toDefine, sqrts) + ")"; //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
	case '~': {
		std::pair<std::string, std::string> sqrt = { recToSmtLib(s2, vars, toDefine, sqrts) , recToSmtLib(s1, vars, toDefine, sqrts) };
		auto it = std::find(sqrts.begin(), sqrts.end(), sqrt);
		if (it != sqrts.end()) {
			return "sqrt" + std::to_string(it - sqrts.begin());
		}
		else {
			sqrts.push_back(sqrt);
			return "sqrt" + std::to_string(sqrts.size() - 1); //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
		}
	}
	default:  throw std::invalid_argument("Invalid operator");
	}
}

std::string Equation::recToShader(const std::string& s, const std::map<std::string, float>& vars) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::to_string(std::stof(s)); }
		if (s[0] != '-') {
			if (vars.count(s)) { return std::to_string(vars.at(s)); }
			if (s[0] == '(' and s.back() == ')') { return "(" + recToShader(s.substr(1, s.length() - 2), vars) + ")"; }
			if (s[0] == '[' and s.back() == ']') { return ("abs(" + recToShader(s.substr(1, s.length() - 2), vars) + ')'); }
			if (s[0] == '!') { return ("((" + recToShader(s.substr(1, s.length() - 1), vars) + " == 0.0) ? 1/0.0 : 0.0)"); } //Have to look into potential problems
		}
		else {
			if (vars.count(s.substr(1, s.length() - 1))) { return std::to_string(-vars.at(s.substr(1, s.length() - 1))); }
			if (s[1] == '(' and s.back() == ')') { return ("-(" + recToShader(s.substr(2, s.length() - 3), vars) + ")"); } 
			if (s[1] == '[' and s.back() == ']') { return ("-abs( " + recToShader(s.substr(2, s.length() - 3), vars) + ")"); }
		}
		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		if (s == "x" or s == "y") { return "coords." + s; }
		throw std::invalid_argument("Invalid statement");
	}	

 	std::string s1 = s.substr(0, operIndex);
	std::string s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "min(" + recToShader(s1, vars) + ", " + recToShader(s2, vars) + ")";
	case '&': return "abs(" + recToShader(s1, vars) + ") + abs(" + recToShader(s2, vars) + ")";
	case '!': return "((" + recToShader(s1, vars) + " - " + recToShader(s2, vars) + " == 0.0) ? 1/0.0 : 0.0)"; //Have to look into potential problems
	case '>':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " > " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars) + " >= " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
	case '<':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " < " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars) + " <= " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
	case '=': return recToShader(s1, vars) + " - " + recToShader(s2, vars);
	case '+': return recToShader(s1, vars) + " + " + recToShader(s2, vars);
	case '-': return recToShader(s1, vars) + " - " + recToShader(s2, vars);
	case '*': return recToShader(s1, vars) + " * " + recToShader(s2, vars);
	case '/': return recToShader(s1, vars) + " / " + recToShader(s2, vars);
	case '^': return "customPow( " + recToShader(s1, vars) + ", " + recToShader(s2, vars) + ")"; 
	case '~': return "customPow( " + recToShader(s2, vars) + ", (1.0 / " + recToShader(s1, vars) + "))";
	default:  throw std::invalid_argument("Invalid operator");
	}
}

int Equation::getNextOperator(const std::string& s, bool& orEquals) const {
	int depth = 0;
	int best = OPERNUM;
	int operIndex = -1;
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

	return operIndex;
}