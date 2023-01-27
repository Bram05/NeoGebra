#include "Equation.h"

#define OPERNUM 13
const unsigned int calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', 0x221A, 0x33D2};
const unsigned int specialCharacters[] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', 0x221A, 0x33D2, '(', ')'};

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

std::map<AdvancedString, float> Equation::linkNumberedVars(const std::vector<std::vector<float>>& identifiers) const {
	if (m_NumberedVarNames.size() != identifiers.size() && m_NumberedVarNames.size() != 0) {
		throw std::invalid_argument("Invalid identifiers");
	}
	
	std::map<AdvancedString, float> m;
	for (int i = 0; i < m_NumberedVarNames.size(); ++i) {
		AdvancedString numberedVarName(m_NumberedVarNames[i]);
		for (int j = 0; j < identifiers[i].size(); ++j) {
			m[numberedVarName + std::to_string(j)] = identifiers[i][j];
		}
	}
	return m;
}

// replace logx with 10logx and sqrt(x) with 2sqrt(x) and 5(...) with 5*(...)
void cleanUpEquation(AdvancedString& s) {
	replaceAll(s, AdvancedString(" "), AdvancedString(""));
	replaceAll(s, AdvancedString("~"), AdvancedString({ 0x221A }));
	replaceAll(s, AdvancedString("log"), AdvancedString({ 0x33D2 }));
	replaceAll(s, AdvancedString("sqrt("), AdvancedString(std::vector<unsigned int>{ 0x221A, '('}));
	unsigned int prev;
	for (int i = 0; i < s.size(); i++) {
		prev = i == 0 ? 0 : s[i - 1];
		if (s[i] == 0x33D2 && (i == 0 || !((prev >= '0' && prev <= '9') || prev == '-' || prev == ')' || prev == ']'))) {
			s.insert(s.begin() + i, "10");
		}
		if (s[i] == 0x221A && (i == 0 || !((prev >= '0' && prev <= '9') || prev == '-' || prev == ')' || prev == ']'))) {
			s.insert(s.begin() + i, "2");
		}
		if (((s[i] >= 'A' && s[i] <= 'Z') || (s[i] >= 'a' && s[i] <= 'z') || s[i] == '(' || s[i] == '[') && ((prev >= '0' && prev <= '9') || prev == ')' || prev == ']')) {
			s.insert(s.begin() + i, "*");
		}
	}
}

Equation::Equation(const std::vector<AdvancedString>& numberedVarNames, const AdvancedString& equationString) : m_NumberedVarNames{ numberedVarNames }, m_EquationString{ equationString }
{
	cleanUpEquation(m_EquationString);
}

Equation::Equation(const AdvancedString& equationString) : m_EquationString{ equationString }
{
	cleanUpEquation(m_EquationString);
}

Equation::Equation(const Equation& e1, const Equation& e2) {
	AdvancedString s1 = e1.m_EquationString;
	AdvancedString s2 = e2.m_EquationString;
	if (e1.m_SolvedDefinedVars)
		m_SolvedDefinedVars = e1.m_SolvedDefinedVars;
	else
		m_SolvedDefinedVars = e2.m_SolvedDefinedVars;

	for (AdvancedString var1 : e1.m_NumberedVarNames) {
		bool varNameAdded = false;
		for (AdvancedString var2 : e2.m_NumberedVarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				AdvancedString newVarName = var1;
				newVarName.push_back('a');
				m_NumberedVarNames.push_back(newVarName);
				replaceVarName(s1, var1, newVarName);
			}
		}
		if (!varNameAdded) {
			m_NumberedVarNames.push_back(var1);
		}
	}
	for (AdvancedString var2 : e2.m_NumberedVarNames) {
		bool varNameAdded = false;
		for (AdvancedString var1 : e1.m_NumberedVarNames) {
			if (var1 == var2) {
				varNameAdded = true;
				AdvancedString newVarName = var2;
				newVarName.push_back('b');
				m_NumberedVarNames.push_back(newVarName);
				replaceVarName(s2, var2, newVarName);
			}
		}
		if (!varNameAdded) {
			m_NumberedVarNames.push_back(var2);
		}
	}

	m_EquationString = "(" + s1 + ") & (" + s2 + ")";
}

std::pair<bool, float> Equation::getVariable(const AdvancedString& key, std::vector<int> ids) const {
	if (key.find(AdvancedString(".")) == key.size()) { return { false, 0.0 }; }
	AdvancedString keyKey = key.substr(0, key.find(AdvancedString(".")));
	AdvancedString keyVal = key.substr(key.find(AdvancedString(".")) + 1, key.size() - key.find(AdvancedString(".")) - 1);
	ptrdiff_t i = std::find(m_NumberedVarNames.begin(), m_NumberedVarNames.end(), keyKey) - m_NumberedVarNames.begin();
	NEType t = m_NumberedVarInputTypes[i];
	if (m_SolvedDefinedVars->find({ t, keyVal }) == m_SolvedDefinedVars->end()) {
		return { false, 0.0 };
	}
	else {
		return { true, m_SolvedDefinedVars->at({t, keyVal}).at(ids[i]) };
	}
}

void Equation::replaceVarName(AdvancedString& s, const AdvancedString& from, const AdvancedString& to) const {
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
	return Equation{ e.m_NumberedVarNames, newEquationStr };
}

equationResult Equation::getSolution(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	//calculate vars
	z3::context c;
	z3::solver solver(c);

	std::string smtLibString = toSmtLib(identifiers, ids);
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

float Equation::getResult(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	//ToDo link self
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recGetResult(m_EquationString, vars, ids);
}

bool Equation::isTrue(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recGetResult(m_EquationString, vars, ids);
}

std::string Equation::toSmtLib(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	std::set<std::string> toDefine;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	std::string out = "(assert " + recToSmtLib(m_EquationString, vars, toDefine, sqrts, ids, true) + ")(check-sat)";

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

std::string Equation::toShader(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids, bool useCustomScroll, const Equation& customScrollX, const Equation& customScrollY) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	AdvancedString formula = m_EquationString;
	if (useCustomScroll) {
		replaceVarName(formula, AdvancedString("x"), AdvancedString("(x"));
	}
	//ToDo change
	//std::shared_ptr<OrAnd> res = recCombineShaders(m_EquationString, vars, ids);
	return recToShader(m_EquationString, vars, ids);
}

std::shared_ptr<OrAnd> Equation::recCombineShaders(const AdvancedString& s, std::map<AdvancedString, float>& vars, std::vector<int> ids) const {
	bool tmp;
	AdvancedString newS = s;
	int operIndex = getNextOperator(newS, tmp);
	while (operIndex == -1 && newS[0] == '(' && newS.back() == ')') { newS = newS.substr(1, newS.size() - 2); operIndex = getNextOperator(newS, tmp); }
	AdvancedString s1 = newS.substr(0, operIndex);
	AdvancedString s2 = newS.substr(operIndex + 1, newS.length() - operIndex - 1);
	if (newS[operIndex] == '|') {
		return std::make_shared<OrAnd>(false, "", true, recCombineShaders(s1, vars, ids), recCombineShaders(s2, vars, ids));
	}
	else if (newS[operIndex] == '&') {
		return std::make_shared<OrAnd>(false, "", false, recCombineShaders(s1, vars, ids), recCombineShaders(s2, vars, ids));
	}
	else {
		return std::make_shared<OrAnd>(true, recToShader(newS, vars, ids), false, nullptr, nullptr);
	}
}

float Equation::recGetResult(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::vector<int> ids) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s.toFloat(); }
		if (s[0] == '-') {
			return -recGetResult(s.substr(1, s.length() - 1), vars, ids);
		}
		if (vars.count(s)) { return vars.at(s); }
		if (s[0] == '(' and s.back() == ')') { return recGetResult(s.substr(1, s.length() - 2), vars, ids); }
		if (s[0] == '[' and s.back() == ']') { return std::abs(recGetResult(s.substr(1, s.length() - 2), vars, ids)); }
		if (s[0] == '!') { return !recGetResult(s.substr(1, s.length() - 1), vars, ids); }
		if (s.size() > 5) {
			if (s.substr(0, 4) == "sin(" and s.back() == ')') { return std::sin(recGetResult(s.substr(4, s.length() - 5), vars, ids)); }
			if (s.substr(0, 4) == "cos(" and s.back() == ')') { return std::cos(recGetResult(s.substr(4, s.length() - 5), vars, ids)); }
			if (s.substr(0, 4) == "tan(" and s.back() == ')') { return std::tan(recGetResult(s.substr(4, s.length() - 5), vars, ids)); }

			if (s.substr(0, 5) == "asin(" and s.back() == ')') { return std::asin(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }
			if (s.substr(0, 5) == "acos(" and s.back() == ')') { return std::acos(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }
			if (s.substr(0, 5) == "atan(" and s.back() == ')') { return std::atan(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }

			if (s.substr(0, 5) == "sinh(" and s.back() == ')') { return std::sinh(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }
			if (s.substr(0, 5) == "cosh(" and s.back() == ')') { return std::cosh(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }
			if (s.substr(0, 5) == "tanh(" and s.back() == ')') { return std::tanh(recGetResult(s.substr(5, s.length() - 6), vars, ids)); }

			if (s.substr(0, 6) == "asinh(" and s.back() == ')') { return std::asinh(recGetResult(s.substr(6, s.length() - 7), vars, ids)); }
			if (s.substr(0, 6) == "acosh(" and s.back() == ')') { return std::acosh(recGetResult(s.substr(6, s.length() - 7), vars, ids)); }
			if (s.substr(0, 6) == "atanh(" and s.back() == ')') { return std::atanh(recGetResult(s.substr(6, s.length() - 7), vars, ids)); }
		}

		if (s == "t") { return true; }
		if (s == "f") { return false; }
		if (s[0] == 0x03C0) { return piConstant; }
		bool succes; float val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes) { return val; }
		throw std::invalid_argument("Invalid operator");
	}

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return recGetResult(s1, vars, ids) or recGetResult(s2, vars, ids);
	case '&': return recGetResult(s1, vars, ids) and recGetResult(s2, vars, ids);
	case '!': return !floatCompare(recGetResult(s1, vars, ids), recGetResult(s2.substr(1, s2.length() - 1), vars, ids));
	case '>':
		if (!orEquals) { return recGetResult(s1, vars, ids) > recGetResult(s2, vars, ids); }
		else { return recGetResult(s1, vars, ids) >= recGetResult(s2.substr(1, s2.length() - 1), vars, ids); }
	case '<':
		if (!orEquals) { return recGetResult(s1, vars, ids) < recGetResult(s2, vars, ids); }
		else { return recGetResult(s1, vars, ids) <= recGetResult(s2.substr(1, s2.length() - 1), vars, ids); }
	case '=': return floatCompare(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	case '+': return recGetResult(s1, vars, ids) + recGetResult(s2, vars, ids);
	case '-': return recGetResult(s1, vars, ids) - recGetResult(s2, vars, ids);
	case '*': return recGetResult(s1, vars, ids) * recGetResult(s2, vars, ids);
	case '/': return recGetResult(s1, vars, ids) / recGetResult(s2, vars, ids);
	case '^': return std::pow(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	case 0x221A: return std::pow(recGetResult(s2, vars, ids), 1 / recGetResult(s1, vars, ids));
	case 0x33D2: return std::log(recGetResult(s2, vars, ids)) / std::log(recGetResult(s1, vars, ids));
	default:  throw std::invalid_argument("Invalid operator");
	}
}

std::string Equation::recToSmtLib(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, std::vector<int> ids, bool isFirstLayer) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s.toString(); }
		if (s[0] == '-') {
			return "(- " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts, ids) + ")";
		}
		if (vars.count(s)) { return std::to_string(vars.at(s)); }
		if (s[0] == '(' and s.back() == ')') { return recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts, ids); }
		if (s[0] == '[' and s.back() == ']') { return ("(abs " + recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts, ids) + ')'); }
		if (s[0] == '!') { return ("(not " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts, ids) + ')'); }
		//ToDo add cos and sin

		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		//toDo add pi
		bool succes; float val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes) { return std::to_string(val); }
		toDefine.insert(s.toString());
		return s.toString();
	}

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "(or " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '&': {
		if (isFirstLayer) {
			return recToSmtLib(s1, vars, toDefine, sqrts, ids) + ")(assert " + recToSmtLib(s2, vars, toDefine, sqrts, ids, true);
		}
		return "(and " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case '!': return "(not (feq " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + "))";
	case '>':
		if (!orEquals) { return "(> " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")"; }
		else { return "(>= " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts, ids) + ")"; }
	case '<':
		if (!orEquals) { return "(< " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")"; }
		else { return "(<= " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts, ids) + ")"; }
	case '=': return "(feq " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '+': return "(+ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '-': return "(- " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '*': return "(* " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '/': return "(/ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '^': return "(^ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")"; //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
	case 0x221A: {
		std::pair<std::string, std::string> sqrt = { recToSmtLib(s2, vars, toDefine, sqrts, ids) , recToSmtLib(s1, vars, toDefine, sqrts, ids) };
		auto it = std::find(sqrts.begin(), sqrts.end(), sqrt);
		if (it != sqrts.end()) {
			return "sqrt" + std::to_string(it - sqrts.begin());
		}
		else {
			sqrts.push_back(sqrt);
			return "sqrt" + std::to_string(sqrts.size() - 1); //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
		}
	}
	//ToDo add log to z3
	default:  throw std::invalid_argument("Invalid operator");
	}
}

std::string Equation::recToShader(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::vector<int> ids) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::to_string(s.toFloat()); }
		if (s[0] != '-') {
			if (vars.count(s)) { return std::to_string(vars.at(s)); }
			if (s[0] == '(' and s.back() == ')') { return "(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ")"; }
			if (s[0] == '[' and s.back() == ']') { return ("abs(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ')'); }
			if (s[0] == '!') { return ("((" + recToShader(s.substr(1, s.length() - 1), vars, ids) + " == 0.0) ? 1/0.0 : 0.0)"); } //Have to look into potential problems
		}
		if (s[0] == '-') {
			return "-(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ")";
		}

		if (vars.count(s)) { return std::to_string(vars.at(s)); }
		if (s[0] == '(' and s.back() == ')') { return "(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ")"; }
		if (s[0] == '[' and s.back() == ']') { return ("abs(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ')'); }
		if (s[0] == '!') { return ("((" + recToShader(s.substr(1, s.length() - 1), vars, ids) + " == 0.0) ? 1/0.0 : 0.0)"); } //Have to look into potential problems
		if (s.size() > 5) {
			if (s.substr(0, 4) == "sin(" and s.back() == ')') { return "cos(" + recToShader(s.substr(4, s.length() - 5), vars, ids) + ")"; }
			if (s.substr(0, 4) == "cos(" and s.back() == ')') { return "cos(" + recToShader(s.substr(4, s.length() - 5), vars, ids) + ")"; }
			if (s.substr(0, 4) == "tan(" and s.back() == ')') { return "tan(" + recToShader(s.substr(4, s.length() - 5), vars, ids) + ")"; }

			if (s.substr(0, 5) == "asin(" and s.back() == ')') { return "asin(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			if (s.substr(0, 5) == "acos(" and s.back() == ')') { return "acos(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			if (s.substr(0, 5) == "atan(" and s.back() == ')') { return "atan(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			
			if (s.substr(0, 5) == "sinh(" and s.back() == ')') { return "sinh(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			if (s.substr(0, 5) == "cosh(" and s.back() == ')') { return "cosh(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			if (s.substr(0, 5) == "tanh(" and s.back() == ')') { return "tanh(" + recToShader(s.substr(5, s.length() - 6), vars, ids) + ")"; }
			
			if (s.substr(0, 6) == "asinh(" and s.back() == ')') { return "asinh(" + recToShader(s.substr(6, s.length() - 7), vars, ids) + ")"; }
			if (s.substr(0, 6) == "acosh(" and s.back() == ')') { return "acosh(" + recToShader(s.substr(6, s.length() - 7), vars, ids) + ")"; }
			if (s.substr(0, 6) == "atanh(" and s.back() == ')') { return "atanh(" + recToShader(s.substr(6, s.length() - 7), vars, ids) + ")"; }
		}

		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		if (s[0] == 0x03C0) { return std::to_string(piConstant); }
		if (s == "x" or s == "y") { return "coords." + s.toString(); }
		bool succes; float val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes && isinf(val)) { return "1.0f/0.0f"; }
		if (succes && isnan(val)) { return "0.0f"; }
		if (succes) { return std::to_string(val); }
		throw std::invalid_argument("Invalid statement");
	}	

 	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	//ToDo remove
	case '|': return "min(abs(" + recToShader(s1, vars, ids) + "), abs(" + recToShader(s2, vars, ids) + "))";
	case '&': return "max(abs(" + recToShader(s1, vars, ids) + "), abs(" + recToShader(s2, vars, ids) + "))";
	case '!': return "((" + recToShader(s1, vars, ids) + " - " + recToShader(s2, vars, ids) + " == 0.0) ? -1 : 1.0)"; //Have to look into potential problems
	case '>':
		if (!orEquals) { return "((" + recToShader(s1, vars, ids) + " > " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars, ids) + " >= " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)"; }
	case '<':
		if (!orEquals) { return "((" + recToShader(s1, vars, ids) + " < " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)"; }
		else { return "((" + recToShader(s1, vars, ids) + " <= " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)"; }
	case '=': return recToShader(s1, vars, ids) + " - (" + recToShader(s2, vars, ids) + ")";
	case '+': return recToShader(s1, vars, ids) + " + " + recToShader(s2, vars, ids);
	case '-': return recToShader(s1, vars, ids) + " - " + recToShader(s2, vars, ids);
	case '*': return recToShader(s1, vars, ids) + " * " + recToShader(s2, vars, ids);
	case '/': return recToShader(s1, vars, ids) + " / " + recToShader(s2, vars, ids);
	case '^': return "customPow( " + recToShader(s1, vars, ids) + ", " + recToShader(s2, vars, ids) + ")"; 
	case 0x221A: return "customPow( " + recToShader(s2, vars, ids) + ", (1.0 / " + recToShader(s1, vars, ids) + "))";
	case 0x33D2: return "log( " + recToShader(s2, vars, ids) + " ) / log( " + recToShader(s1, vars, ids) + ")";
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