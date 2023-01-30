#include "Equation.h"
#include "Application.h"

#define OPERNUM 16
const unsigned int calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', 0x2265, 0x2264, 0x2260, '=', '+', '-', '*', '/', '^', 0x221A, 0x33D2};
const unsigned int specialCharacters[] = { '|', '&', '!', '>', '<', 0x2265, 0x2264, 0x2260, '=', '+', '-', '*', '/', '^', 0x221A, 0x33D2, '(', ')'};

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
			i -= from.length();
			i += to.length();
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
	replaceAll(s, AdvancedString("!="), AdvancedString({ 0x2260 }));
	replaceAll(s, AdvancedString(">="), AdvancedString({ 0x2265 }));
	replaceAll(s, AdvancedString("<="), AdvancedString({ 0x2264 }));
	unsigned int prev;
	for (int i = 0; i < s.size(); i++) {
		prev = i == 0 ? 0 : s[i - 1];
		if (s[i] == 0x33D2 && (i == 0 || !((prev >= '0' && prev <= '9') || prev == ')' || prev == ']'))) {
			s.insert(s.begin() + i, "10");
			if (prev == '-') {
				s.erase(s.begin()+i - 1);
				s.insert(s.begin() + i, "-1*");
			}
		}
		if (s[i] == 0x221A && (i == 0 || !((prev >= '0' && prev <= '9') || prev == ')' || prev == ']'))) {
			s.insert(s.begin() + i, "2");
			if (prev == '-') {
				s.erase(s.begin() + i - 1);
				s.insert(s.begin() + i-1, "-1*");
			}
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

std::pair<bool, double> Equation::getVariable(const AdvancedString& key, std::vector<int> ids) const {
	if (key.find(AdvancedString(".")) == key.size()) { return { false, 0.0 }; }
	if (ids.size() < m_NumberedVarNames.size()) { return { false, 0.0 }; }
	AdvancedString keyKey = key.substr(0, key.find(AdvancedString(".")));
	AdvancedString keyVal = key.substr(key.find(AdvancedString(".")) + 1, key.size() - key.find(AdvancedString(".")) - 1);
	ptrdiff_t i = std::find(m_NumberedVarNames.begin(), m_NumberedVarNames.end(), keyKey) - m_NumberedVarNames.begin();
	if (i == m_NumberedVarNames.size()) { return { false, 0.0 }; }
	NEType t = m_NumberedVarInputTypes[i];
	if (m_SolvedDefinedVars->find({ t, keyVal }) == m_SolvedDefinedVars->end()) {
		return { false, 0.0 };
	}
	else {
		return { true, m_SolvedDefinedVars->at({t, keyVal}).at(ids[i]) };
	}
}

void Equation::replaceVarName(AdvancedString& s, const AdvancedString& from, const AdvancedString& to) const {
	for (int i = 0; i < s.size() - from.size(); i++) {
		bool match = true;
		for (int j = 0; j < from.size(); j++) {
			if (s[i + j] != from[j]) {
				match = false;
				break;
			}
		}
		if (match) {
			int k = 0;
			while ((s[i + from.size() + k] >= '0' && s[i + from.size() + k] <= '9') || s[i + from.size() + k] == '.') { k++; }
			if (k > 0 && (i == 0 || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i - 1]) != std::end(specialCharacters)) &&
				(i + from.size() + k == s.size() || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i + from.size() + k]) != std::end(specialCharacters) || s[i + from.size()] == '.'))
			{
				if (s[i + from.size()] == '.') { k++; }
				s.erase(s.begin() + i, s.begin() + i + from.size());
				s.insert(s.begin() + i, to.begin(), to.end());
				i += to.length() + k;
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

Equation Equation::diff(const AdvancedString& remainingVar) const {
	AdvancedString eq1Content = m_EquationString;
	AdvancedString eq2Content = m_EquationString;
	std::vector<AdvancedString> numberedVarNamesA = m_NumberedVarNames;

	std::vector<NEType> inpTypes = m_NumberedVarInputTypes;
	if (inpTypes.size() > 0) {
		inpTypes.insert(inpTypes.end(), inpTypes.begin(), inpTypes.end());
		inpTypes.erase(inpTypes.begin() + (std::find(numberedVarNamesA.begin(), numberedVarNamesA.end(), remainingVar) - numberedVarNamesA.begin()) + m_NumberedVarInputTypes.size());
		inpTypes.erase(inpTypes.begin() + (std::find(numberedVarNamesA.begin(), numberedVarNamesA.end(), remainingVar) - numberedVarNamesA.begin()));
	}

	numberedVarNamesA.erase(std::find(numberedVarNamesA.begin(), numberedVarNamesA.end(), remainingVar));
	std::vector<AdvancedString> numberedVarNamesB = numberedVarNamesA;
	for (int i = 0; i < numberedVarNamesA.size(); ++i) {
		replaceVarName(eq1Content, numberedVarNamesA[i], numberedVarNamesA[i] + "a");
		replaceVarName(eq2Content, numberedVarNamesB[i], numberedVarNamesB[i] + "b");
		numberedVarNamesA[i] = numberedVarNamesA[i] + "a";
		numberedVarNamesB[i] = numberedVarNamesB[i] + "b";
	}
	numberedVarNamesA.insert(numberedVarNamesA.end(), numberedVarNamesB.begin(), numberedVarNamesB.end());
	Equation res(numberedVarNamesA, recDiff(eq1Content, eq2Content)+"&"+ eq1Content);
	res.linkVars(m_SolvedDefinedVars, inpTypes);
	return res;
}

AdvancedString Equation::recDiff(const AdvancedString& s1, const AdvancedString& s2) const {
	bool tmp;
	AdvancedString newS1 = s1;
	AdvancedString newS2 = s2;
	int operIndex1 = getNextOperator(newS1, tmp);
	while (operIndex1 == -1 && newS1[0] == '(' && newS1.back() == ')') { 
		newS1 = newS1.substr(1, newS1.size() - 2);
		newS2 = newS2.substr(1, newS2.size() - 2);
		operIndex1 = getNextOperator(newS1, tmp); 
	}
	int operIndex2 = getNextOperator(newS2, tmp);

	if (newS1[operIndex1] == '|' || newS1[operIndex1] == '&') {
		const AdvancedString& resP1 = recDiff(newS1.substr(0, operIndex1), newS2.substr(0, operIndex2));
		const AdvancedString& resP2 = recDiff(newS1.substr(operIndex1 + 1, newS1.length() - operIndex1 - 1), newS2.substr(operIndex2 + 1, newS2.length() - operIndex2 - 1));
		if (resP1 == resP2) {
			return resP1;
		}
		AdvancedString res = resP1 + newS1[operIndex1] + resP2;
		return res;
	}
	if (newS1[operIndex1] == '=') {
		AdvancedString res = newS1.substr(0, operIndex1) + " - (" + newS2.substr(0, operIndex2) + ") = " + newS1.substr(operIndex1 + 1, newS1.length() - operIndex1 - 1) + " - (" + newS2.substr(operIndex2 + 1, newS2.length() - operIndex2 - 1) + ")";
		return res;
	}
	return newS1;
}

bool Equation::getSolution(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids, std::vector<std::string>& resNames, z3::context* cPtr, z3::solver* solverPtr, const std::vector<std::pair<std::string, std::string>>& extraSqrts, const std::string& extraSMT) const {
	//calculate vars
	if (!solverPtr) {
		z3::context c;
		z3::solver solver(c);
		cPtr = &c;
		solverPtr = &solver;
	}

	std::string smtLibString = toSmtLib(identifiers, ids, resNames, extraSqrts, extraSMT);
	Z3_ast_vector test2 = Z3_parse_smtlib2_string(*cPtr, smtLibString.c_str(), 0, 0, 0, 0, 0, 0);

	if (Z3_ast_vector_size(*cPtr, test2) == 0) {
		Application::Get()->GetWindowUI()->DisplayError("Error with smtLibString:\n"+smtLibString);
	}

	for (int i{}; i < Z3_ast_vector_size(*cPtr, test2); ++i) {
		z3::expr tmp(*cPtr, Z3_ast_vector_get(*cPtr, test2, i));
		solverPtr->add(tmp);
	}

	z3::params p(*cPtr);
	p.set(":timeout", 3000u);
	solverPtr->set(p);

	//std::cout << *solverPtr << "\n";
	//std::cout << solverPtr->to_smt2() << "\n\n::\n\n";
	switch (solverPtr->check()) {
	case z3::sat: { return true; }
	case z3::unsat: 
		Application::Get()->GetWindowUI()->DisplayError("No solution found\nIf this is incorrect: Add manual function for this action");
		return false;
	case z3::unknown: 
		Application::Get()->GetWindowUI()->DisplayError("Solver timeout: Add manual function for this action");
	default: return false;
	}
}

double Equation::getResult(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recGetResult(m_EquationString, vars, ids);
}

bool Equation::isTrue(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recGetResult(m_EquationString, vars, ids);
}

std::string Equation::toSmtLib(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids, const std::vector<std::string>& resNames, const std::vector<std::pair<std::string, std::string>>& extraSqrts, const std::string& extraSMT) const {
	std::set<std::string> toDefine;
	std::vector<std::pair<std::string, std::string>> sqrts;
	sqrts.insert(sqrts.begin(), extraSqrts.begin(), extraSqrts.end());
	int definedSqrts = sqrts.size();
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	std::string out = "(assert " + recToSmtLib(m_EquationString, vars, toDefine, sqrts, ids, true) + ")(check-sat)";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		std::string def = sqrts[i].first;
		std::string pow = sqrts[i].second;
		out = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + out;
	}
	out = extraSMT + out;

	for (std::string s : resNames) {
		toDefine.insert(s);
	}

	for (std::string var : toDefine) {
		out = "(declare-const " + var + " Real)" + out;
	}

	return "(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))" + out;
}

std::string Equation::toShader(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids, bool useCustomScroll, const Equation& customScrollX, const Equation& customScrollY) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recToShader(m_EquationString, vars, ids);
}

double Equation::recGetResult(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::vector<int> ids) const {
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
		if (s.size() > 4) {
			if (s.substr(0, 3) == "ln(" and s.back() == ')') { return std::log(recGetResult(s.substr(4, s.length() - 4), vars, ids)); }
		}
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
		bool succes; double val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes) { return val; }
		throw std::invalid_argument("Invalid operator");
	}

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return recGetResult(s1, vars, ids) or recGetResult(s2, vars, ids);
	case '&': return recGetResult(s1, vars, ids) and recGetResult(s2, vars, ids);
	case 0x2260: return !floatCompare(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	case '>': return recGetResult(s1, vars, ids) > recGetResult(s2, vars, ids);
	case 0x2265: return recGetResult(s1, vars, ids) >= recGetResult(s2, vars, ids); 
	case '<': return recGetResult(s1, vars, ids) < recGetResult(s2, vars, ids);
	case 0x2264: return recGetResult(s1, vars, ids) <= recGetResult(s2, vars, ids);
	case '=': return floatCompare(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	case '+': return recGetResult(s1, vars, ids) + recGetResult(s2, vars, ids);
	case '-': return recGetResult(s1, vars, ids) - recGetResult(s2, vars, ids);
	case '*': return recGetResult(s1, vars, ids) * recGetResult(s2, vars, ids);
	case '/': return recGetResult(s1, vars, ids) / recGetResult(s2, vars, ids);
	case '^': {
		if (s1[0] == '-') {
			return -std::pow(recGetResult(s1.substr(1,s1.size()-1), vars, ids), recGetResult(s2, vars, ids));
		}
		return std::pow(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	}
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
		if (s.size() > 5) {
			if (s.substr(0, 4) == "sin(" and s.back() == ')') { return "(cos " + recToSmtLib(s.substr(4, s.length() - 5), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 4) == "cos(" and s.back() == ')') { return "(cos " + recToSmtLib(s.substr(4, s.length() - 5), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 4) == "tan(" and s.back() == ')') { return "(tan " + recToSmtLib(s.substr(4, s.length() - 5), vars, toDefine, sqrts, ids) + ")"; }

			if (s.substr(0, 5) == "asin(" and s.back() == ')') { return "(asin " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 5) == "acos(" and s.back() == ')') { return "(acos " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 5) == "atan(" and s.back() == ')') { return "(atan " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }

			if (s.substr(0, 5) == "sinh(" and s.back() == ')') { return "(sinh " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 5) == "cosh(" and s.back() == ')') { return "(cosh " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 5) == "tanh(" and s.back() == ')') { return "(tanh " + recToSmtLib(s.substr(5, s.length() - 6), vars, toDefine, sqrts, ids) + ")"; }

			if (s.substr(0, 6) == "asinh(" and s.back() == ')') { return "(asinh " + recToSmtLib(s.substr(6, s.length() - 7), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 6) == "acosh(" and s.back() == ')') { return "(acosh " + recToSmtLib(s.substr(6, s.length() - 7), vars, toDefine, sqrts, ids) + ")"; }
			if (s.substr(0, 6) == "atanh(" and s.back() == ')') { return "(atanh " + recToSmtLib(s.substr(6, s.length() - 7), vars, toDefine, sqrts, ids) + ")"; }
		}

		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		
		if (s[0] == 0x03C0) { return std::to_string(piConstant); }
		bool succes; float val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes) { return std::to_string(val); }
		if (s.find(AdvancedString(".")) != s.size()) {return s.toString();}
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

		if (vars.count(s)) { 
			if (isinf(vars.at(s))) { return "1.0f/0.0f"; }
			if (isnan(vars.at(s))) { return "0.0f"; }
			return std::to_string(vars.at(s)); 
		}
		if (s[0] == '(' and s.back() == ')') { return "(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ")"; }
		if (s[0] == '[' and s.back() == ']') { return ("abs(" + recToShader(s.substr(1, s.length() - 2), vars, ids) + ')'); }
		if (s[0] == '!') { return ("((" + recToShader(s.substr(1, s.length() - 1), vars, ids) + " == 0.0) ? 1/0.0 : 0.0)"); } //Have to look into potential problems
		if (s.size() > 4) {
			if (s.substr(0, 3) == "ln(" and s.back() == ')') { return "log(" + recToShader(s.substr(4, s.length() - 4), vars, ids) + ")"; }
		}
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
	for (int i = s.length() - 1; i >= 0; --i) {
		unsigned int c = s[i];
		if (c == '(' or c == '[') { depth += 1; }
		if (c == ')' or c == ']') { depth -= 1; }

		if (depth == 0) {
			const unsigned int* res = std::find(std::begin(calcOrder), std::begin(calcOrder) + best, c);
			if (res != std::begin(calcOrder) + best) {
				// If operator is '-', the program needs to check if there is another operator in front of it, such as 5*-3=-15
				if (!(c == '-' && (i == 0 || (std::find(std::begin(calcOrder), std::end(calcOrder), s[i - 1]) == std::end(calcOrder))) )) {
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