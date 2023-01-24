#include "Equation.h"

#define OPERNUM 12
const unsigned int calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', '~' };
const unsigned int specialCharacters[] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', '~', '(', ')', 0x221A};

/// Checks if a string contains a signed float. 
bool isNumber(const AdvancedString& str)
{
	for (unsigned int c : str.content) {
		if (!((c >= '0' && c <= '9') || c == '.' || c == '-')) {
			return false;
		}
	}
	return true;
}

/**
	* Replace all instances of substring in string.
	*
	* @param from[in] Substring that should be replaced.
	* @param to[in] Substring to replace 'from' with.
*/
void replaceAll(AdvancedString& str, const AdvancedString& from, const AdvancedString& to) {
	for (int i = 0; i < str.size(); i++) {
		bool match = true;
		for (int j = 0; j < from.size(); j++) {
			if (str[i + j] != from[j]) {
				match = false;
				break;
			}
		}
		if (match) {
			str.erase(str.begin()+i, str.begin()+i+from.size());
			str.insert(str.begin() + i, to.begin(), to.end());
		}
	}
}

/// Compares two float numbers using a variable epsilon value. 
bool floatCompare(float f1, float f2) {
	static constexpr auto epsilon = 1.0e-05f;
	if (std::abs(f1 - f2) <= epsilon)
		return true;
	return std::abs(f1 - f2) <= epsilon * std::max(std::abs(f1), std::abs(f2));
}

std::map<AdvancedString, float> Equation::linkVars(const std::vector<std::vector<float>>& identifiers) const {
	if (m_VarNames.size() != identifiers.size()) {
		throw std::invalid_argument("Invalid identifiers");
	}
	
	std::map<AdvancedString, float> m;
	for (int i = 0; i < m_VarNames.size(); ++i) {
		AdvancedString varName(m_VarNames[i]);
		for (int j = 0; j < identifiers[i].size(); ++j) {
			m[varName + std::to_string(j)] = identifiers[i][j];
		}
	}
	return m;
}

Equation::Equation(const std::vector<AdvancedString>& varNames, const AdvancedString& equationString) : m_VarNames{ varNames }, m_EquationString{ equationString }
{
	replaceAll(m_EquationString, AdvancedString(" "), AdvancedString(""));
}

Equation::Equation(const Equation& e1, const Equation& e2) {
	AdvancedString s1 = e1.m_EquationString;
	AdvancedString s2 = e2.m_EquationString;

	for (AdvancedString var1 : e1.m_VarNames) {
		bool varNameAdded = false;
		for (AdvancedString var2 : e2.m_VarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				AdvancedString newVarName = var1;
				newVarName.push_back('a');
				m_VarNames.push_back(newVarName);
				replaceVarName(s1, var1, newVarName);
			}
		}
		if (!varNameAdded) {
			m_VarNames.push_back(var1);
		}
	}
	for (AdvancedString var2 : e2.m_VarNames) {
		bool varNameAdded = false;
		for (AdvancedString var1 : e1.m_VarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				AdvancedString newVarName = var2;
				newVarName.push_back('b');
				m_VarNames.push_back(newVarName);
				replaceVarName(s2, var2, newVarName);
			}
		}
		if (!varNameAdded) {
			m_VarNames.push_back(var2);
		}
	}

	m_EquationString = "(" + s1 + ") & (" + s2 + ")";
}

void Equation::replaceVarName(AdvancedString& s, const AdvancedString& from, const AdvancedString& to) {
	for (int i = 0; i < s.size(); i++) {
		bool match = true;
		for (int j = 0; j < from.size(); j++) {
			if (s[i + j] != from[j]) {
				match = false;
				break;
			}
		}
		if (match) {
			int k = 0;
			while (s[i + from.size() + k] >= '0' && s[i + from.size() + k] <= '9') { k++; }
			if (k > 0 && (i == 0 || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i - 1]) != std::end(specialCharacters)) &&
				(i + from.size() + k == s.size() || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i + from.size() + k]) != std::end(specialCharacters)))
			{
				s.erase(s.begin() + i, s.begin() + i + from.size());
				s.insert(s.begin() + i, to.begin(), to.end());
			}
		}
	}
}

Equation operator+(const Equation& e1, const Equation& e2) {
	return Equation{ e1, e2 };
}

Equation operator!(const Equation& e) {
	AdvancedString newEquationStr = e.m_EquationString;
	newEquationStr.insert(newEquationStr.begin(), "!(");
	newEquationStr.insert(newEquationStr.end(), ')');
	return Equation{ e.m_VarNames, newEquationStr };
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
	std::map<AdvancedString, float> vars = linkVars(identifiers);
	return recIsTrue(m_EquationString, vars);
}

std::string Equation::toSmtLib(const std::vector<std::vector<float>>& identifiers) const {
	std::set<std::string> toDefine;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::map<AdvancedString, float> vars = linkVars(identifiers);
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

OrAnd Equation::toShader(const std::vector<std::vector<float>>& identifiers) const {
	std::map<AdvancedString, float> vars = linkVars(identifiers);
	//ToDo change
	//OrAnd res = *recCombineShaders(m_EquationString, vars);
	OrAnd res(true, recToShader(m_EquationString, vars), false, nullptr, nullptr);
	return res;
}

std::shared_ptr<OrAnd> Equation::recCombineShaders(const AdvancedString& s, std::map<AdvancedString, float>& vars) const {
	bool tmp;
	int operIndex = getNextOperator(s, tmp);
	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);
	if (s[operIndex] == '|') {
		return std::make_shared<OrAnd>(false, "", true, recCombineShaders(s1, vars), recCombineShaders(s2, vars));
	}
	else if (s[operIndex] == '&') {
		return std::make_shared<OrAnd>(false, "", false, recCombineShaders(s1, vars), recCombineShaders(s2, vars));
	}
	else {
		return std::make_shared<OrAnd>(true, recToShader(s, vars), false, nullptr, nullptr);
	}
}

float Equation::recIsTrue(const AdvancedString& s, const std::map<AdvancedString, float>& vars) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s.toFloat(); }
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

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

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

std::string Equation::recToSmtLib(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, bool isFirstLayer) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s.toString(); }
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
		toDefine.insert(s.toString());
		return s.toString();
	}

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

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

std::string Equation::recToShader(const AdvancedString& s, const std::map<AdvancedString, float>& vars) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::to_string(s.toFloat()); }
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
		if (s == "x" or s == "y") { return "coords." + s.toString(); }
		throw std::invalid_argument("Invalid statement");
	}	

 	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	//ToDo remove
	case '|': return "min(" + recToShader(s1, vars) + ", " + recToShader(s2, vars) + ")";
	case '&': return "abs(" + recToShader(s1, vars) + ") + abs(" + recToShader(s2, vars) + ")";
	case '!': return "((" + recToShader(s1, vars) + " - " + recToShader(s2, vars) + " == 0.0) ? 1/0.0 : 0.0)"; //Have to look into potential problems
	case '>':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " > " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars) + " >= " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
	case '<':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " < " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars) + " <= " + recToShader(s2, vars) + ") ? 0.0 : 1/0.0)"; }
	case '=': return recToShader(s1, vars) + " - (" + recToShader(s2, vars) + ")";
	case '+': return recToShader(s1, vars) + " + " + recToShader(s2, vars);
	case '-': return recToShader(s1, vars) + " - " + recToShader(s2, vars);
	case '*': return recToShader(s1, vars) + " * " + recToShader(s2, vars);
	case '/': return recToShader(s1, vars) + " / " + recToShader(s2, vars);
	case '^': return "customPow( " + recToShader(s1, vars) + ", " + recToShader(s2, vars) + ")"; 
	case '~': return "customPow( " + recToShader(s2, vars) + ", (1.0 / " + recToShader(s1, vars) + "))";
	default:  throw std::invalid_argument("Invalid operator");
	}
}

int Equation::getNextOperator(const AdvancedString& s, bool& orEquals ) const {
	int depth = 0;
	int best = OPERNUM;
	int operIndex = -1;
	for (int i{}; i < s.length(); ++i) {
		unsigned int c = s[i];
		if (c == '(' or c == '[') { depth += 1; }
		if (c == ')' or c == ']') { depth -= 1; }

		if (depth == 0) {
			const unsigned int* res = std::find(std::begin(calcOrder), std::begin(calcOrder) + best, c);
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

AdvancedString operator+(const AdvancedString& s1, const AdvancedString& s2) {
	AdvancedString res = s1;
	res.content.insert(res.content.end(), s2.content.begin(), s2.content.end());
	return res;
}

AdvancedString operator+(const AdvancedString& s1, const std::string& s2)	{
	AdvancedString res = s1;
	res.content.insert(res.content.end(), s2.begin(), s2.end());
	return res;
}

AdvancedString operator+(const std::string& s1, const AdvancedString& s2) {
	AdvancedString res = s2;
	res.content.insert(res.content.begin(), s1.begin(), s1.end());
	return res;
}

bool operator==(const AdvancedString& s1, const AdvancedString& s2) {
	return s1.content == s2.content;
}

bool operator==(const AdvancedString& s1, const std::string& s2) {
	for (int i = 0; i < s1.size(); i++) {
		if (s1[i] != s2[i]) {
			return false;
		}
	}
	return true;
}

bool operator==(const std::string& s1, const AdvancedString& s2) {
	for (int i = 0; i < s1.size(); i++) {
		if (s1[i] != s2[i]) {
			return false;
		}
	}
	return true;
}

bool operator<(const AdvancedString& s1, const AdvancedString& s2) {
	return s1.content < s2.content;
}