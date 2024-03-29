#include "Equation.h"
#include "Application.h"

#define OPERNUM 15
const unsigned int calcOrder[OPERNUM] = { '|', '&', '>', '<', 0x2265, 0x2264, 0x2260, '=', '+', '-', '*', '/', '^', 0x221A, 0x33D2};
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
void Equation::replaceAll(AdvancedString& str, const AdvancedString& from, const AdvancedString& to) {
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
		std::string identifierString;
		identifierString += "( ";
		for (const std::vector<float>& ids : identifiers) {
			identifierString += "( ";
			for (float id : ids) {
				identifierString += std::format("{:.2f}", id) + " ";
			}
			identifierString += ") ";
		}
		identifierString += ")";
		Application::Get()->GetWindowUI()->DisplayError("Invalid identifiers: " + identifierString + ". There should be " + std::to_string(m_NumberedVarNames.size()) + " sets of identifiers");
		throw ErrorBoxException();
	}
	
	std::map<AdvancedString, float> m{};
	for (int i = 0; i < m_NumberedVarNames.size(); ++i) {
		AdvancedString numberedVarName(m_NumberedVarNames[i]);
		for (int j = 0; j < identifiers[i].size(); ++j) {
			auto[it, worked] = m.insert({numberedVarName + std::to_string(j), identifiers[i][j]});
			if (!worked)
			{
				Application::Get()->GetWindowUI()->DisplayError("Invalid identifier names. Did you chose the same name twice?");
				throw ErrorBoxException();
			}
		}
	}
	return m;
}

// replace logx with 10logx and sqrt(x) with 2sqrt(x) and 5(...) with 5*(...)
void Equation::cleanUpEquation(AdvancedString& s) {
	replaceAll(s, AdvancedString(" "), AdvancedString(""));
	replaceVarName(s, AdvancedString("pi"), AdvancedString({ 0x03C0 }));
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
	for (int i = 0; i < (int)(s.size() - from.size()); i++) {
		bool match = true;
		for (int j = 0; j < from.size(); j++) {
			if (s[i + j] != from[j]) {
				match = false;
				break;
			}
		}
		if (match) {
			int k = 0;
			while (i + from.size() + k != s.size() && ((s[i + from.size() + k] >= '0' && s[i + from.size() + k] <= '9') || s[i + from.size() + k] == '.')) { k++; }
			if (k > 0 && (i == 0 || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i - 1]) != std::end(specialCharacters)) &&
				(i + from.size() + k == s.size() || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i + from.size() + k]) != std::end(specialCharacters) || s[i + from.size()] == '.'))
			{
				if (s[i + from.size()] == '.') { k++; }
				s.erase(s.begin() + i, s.begin() + i + from.size());
				s.insert(s.begin() + i, to.begin(), to.end());
				i += to.length() + k;
			}
			else if ((from == "x" || from == "y" || from == "pi") && (i == 0 || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i - 1]) != std::end(specialCharacters)) &&
				(i + from.size() == s.size() || std::find(std::begin(specialCharacters), std::end(specialCharacters), s[i + from.size()]) != std::end(specialCharacters))) {
				s.erase(s.begin() + i, s.begin() + i + from.size());
				s.insert(s.begin() + i, to.begin(), to.end());
				i += to.length();
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

bool Equation::SolutionExists(const std::vector<float>& identifiers, int id, NEType t, const Model* model) const {
	//calculate vars
	z3::context c;
	z3::solver solver(c);

	std::string smtLibString = defToSmtLib(identifiers, id, t, model);
	Z3_ast_vector test2 = Z3_parse_smtlib2_string(c, smtLibString.c_str(), 0, 0, 0, 0, 0, 0);

	if (Z3_ast_vector_size(c, test2) == 0) {
		Application::Get()->GetWindowUI()->DisplayError("Error with smtLibString");
		throw ErrorBoxException();
	}

	for (int i{}; i < Z3_ast_vector_size(c, test2); ++i) {
		z3::expr tmp(c, Z3_ast_vector_get(c, test2, i));
		solver.add(tmp);
	}

	z3::params p(c);
	p.set(":timeout", z3TimeOut);
	solver.set(p);

	//std::cout << *solverPtr << "\n";
	//std::cout << solverPtr->to_smt2() << "\n\n\n\n";
	switch (solver.check()) {
	case z3::sat: return true; 
	case z3::unsat: return false;
	case z3::unknown: 
		Application::Get()->GetWindowUI()->DisplayError("Solver timeout");
	default: return true;
	}
}

double Equation::getResult(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids, const std::map<AdvancedString, float>& extraVars) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	for (auto it = extraVars.begin(); it != extraVars.end(); it++) {
		vars[it->first] = it->second;
	}
	return recGetResult(m_EquationString, vars, ids);
}

bool Equation::isTrue(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
	std::map<AdvancedString, float> vars = linkNumberedVars(identifiers);
	return recGetResult(m_EquationString, vars, ids);
}

std::string Equation::getVarFunsSmt(NEType t, const Model& model, std::string& smt, std::vector<std::string>& sqrts, int amountOfVars) {
	std::set<std::string> tmp;
	std::map<AdvancedString, float> tmp2;

	std::string identName = t == point ? model.m_PointDef.m_NumberedVarNames[0].toString() : model.m_LineDef.m_NumberedVarNames[0].toString();
	

	const std::vector< std::pair < AdvancedString, std::shared_ptr<Equation> >>& extraVars = (t == point ? model.m_Variables.first : model.m_Variables.second);

	if (amountOfVars == 1) {
		std::string indentifierString;
		for (int i = 0; i < (t == point ? model.m_PointIdentifiers : model.m_LineIdentifiers); ++i) {
			indentifierString += " " + identName + std::to_string(i);
		}
		for (const std::pair < AdvancedString, std::shared_ptr<Equation>>& var : extraVars) {
			std::string varName = var.first.toString();
			auto loc = smt.find(identName + "." + varName);
			while (loc != std::string::npos) {
				smt.replace(loc, identName.length() + varName.length() + 1, "(" + identName + "." + varName + indentifierString + ")");
				loc = smt.find(identName + "." + varName, loc + 2);
			}
		}
	}
	else {
		for (int n = 0; n < amountOfVars; ++n) {
			std::string indentifierString;
			for (int i = 0; i < (t == point ? model.m_PointIdentifiers : model.m_LineIdentifiers); ++i) {
				indentifierString += " " + identName + (char)('a' + n) + std::to_string(i);
			}
			for (const std::pair < AdvancedString, std::shared_ptr<Equation>>& var : extraVars) {
				std::string varName = var.first.toString();
				auto loc = smt.find(identName + (char)('a'+n) + "." + varName);
				while (loc != std::string::npos) {
					smt.replace(loc, identName.length() + varName.length() + 2, "(" + identName + "." + varName + indentifierString + ")");
					loc = smt.find(identName + (char)('a' + n) + "." + varName, loc + 2);
				}
			}
		}
	}

	std::string indentifierString;
	for (int i = 0; i < (t == point ? model.m_PointIdentifiers : model.m_LineIdentifiers); ++i) {
		indentifierString += " " + identName + std::to_string(i);
	}

	std::vector<std::string> otherVars;
	std::string funcDefsSmt;
	for (const std::pair < AdvancedString, std::shared_ptr<Equation>>& var : extraVars) {
		std::string tmpSmt = "(define-fun " + identName + "." + var.first.toString() + " (";
		for (int i = 0; i < (t == point ? model.m_PointIdentifiers : model.m_LineIdentifiers); i++) {
			tmpSmt += "(" + identName + std::to_string(i) + " Real)";
		}

		tmpSmt += ") Real " + var.second->recToSmtLib(var.second->m_EquationString, tmp2, tmp, sqrts, {}, true, false) + ")";
		
		for (std::string otherVar : otherVars) {
			auto loc = tmpSmt.find(identName + "." + otherVar);
			while (loc != std::string::npos) {
				tmpSmt.replace(loc, identName.length() + otherVar.length() + 1, "(" + identName + "." + otherVar + indentifierString + ")");
				loc = tmpSmt.find(identName + "." + otherVar, loc + 2);
			}
		}
		otherVars.push_back(var.first.toString());

		funcDefsSmt += tmpSmt;
	}
	return funcDefsSmt;
}

std::string Equation::defToSmtLib(const std::vector<float>& identifiers, int id, NEType t, const Model* model) const {
	std::set<std::string> toDefine;
	std::vector<std::string> sqrts;
	int definedSqrts = 0;
	std::map<AdvancedString, float> vars = linkNumberedVars({ identifiers });
	std::string out = "(assert " + recToSmtLib(m_EquationString, vars, toDefine, sqrts, { id }, true, false) + ")(check-sat)";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		out = "(assert " + sqrts[i] + ")" + out;
	}
	definedSqrts = sqrts.size();

	std::map<AdvancedString, float> tmpVarStorage;

	for (const std::pair < AdvancedString, std::shared_ptr<Equation> >& var : (t == point ? model->m_Variables.first : model->m_Variables.second)) {
		AdvancedString varName = m_NumberedVarNames[0] + "." + var.first;
		float varDef = var.second->getResult({ identifiers }, { id }, tmpVarStorage);
		tmpVarStorage[varName] = varDef;
		auto loc = out.find(varName.toString());
		while (loc != std::string::npos) {
			out.replace(loc, varName.length(), std::to_string(varDef));
			loc = out.find(varName.toString(), loc + 1 + varName.length());
		}
	}

	for (std::string var : toDefine) {
		out = "(declare-const " + var + " Real)" + out;
	}

	///
	//  (define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))
	//  (define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0))
	//	(define-fun feqReal ((a Real)(b Real)) Real(ite(< (abs(- a b)) 0.0001) 1.0 0.0))
	//	(define-fun gReal ((a Real)(b Real)) Real(ite(> a b) 1.0 0.0))
	//	(define-fun geReal ((a Real)(b Real)) Real(ite(>= a b) 1.0 0.0))
	//	(define-fun lReal ((a Real)(b Real)) Real(ite(< a b) 1.0 0.0))
	//	(define-fun leReal ((a Real)(b Real)) Real(ite(<= a b) 1.0 0.0))
	//  (declare-fun sqrt (Real) Real)
	//  (declare-fun root3 (Real) Real)
	//  (declare-fun root4 (Real) Real)
	//  (assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))
	//  (assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))
	/// 
	return "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + out;
}

std::string Equation::toShader(const std::vector<std::vector<float>>& identifiers, std::vector<int> ids) const {
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
			if (s.substr(0, 3) == "ln(" and s.back() == ')') { return std::log(recGetResult(s.substr(3, s.length() - 4), vars, ids)); }
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
		if (s[0] == 'e') { return eConstant; }
		if (s == "NaN") { return std::numeric_limits<double>::quiet_NaN(); }
		bool succes; double val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes) { return val; }
		Application::Get()->GetWindowUI()->DisplayError("Invalid statement: " + s.toString());
		throw ErrorBoxException();
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
	case '*':
	{
		double res1 = recGetResult(s1, vars, ids);
		double res2 = recGetResult(s2, vars, ids);
		if (floatCompare(res1, 0.0f) || floatCompare(res2, 0.0f))
			return 0.0;
		return res1 * res2;
	}
	case '/': return recGetResult(s1, vars, ids) / recGetResult(s2, vars, ids);
	case '^': {
		if (s1[0] == '-') {
			return -std::pow(recGetResult(s1.substr(1,s1.size()-1), vars, ids), recGetResult(s2, vars, ids));
		}
		return std::pow(recGetResult(s1, vars, ids), recGetResult(s2, vars, ids));
	}
	case 0x221A: return std::pow(recGetResult(s2, vars, ids), 1 / recGetResult(s1, vars, ids));
	case 0x33D2: return std::log(recGetResult(s2, vars, ids)) / std::log(recGetResult(s1, vars, ids));
	default: {
		Application::Get()->GetWindowUI()->DisplayError("Next operator not found: " + s.toString());
		throw ErrorBoxException();
	}
	}
}

std::string Equation::recToSmtLib(const AdvancedString& s, const std::map<AdvancedString, float>& vars, std::set<std::string>& toDefine, std::vector<std::string>& sqrts, std::vector<int> ids, bool isFirstLayer, bool embeddedEquals) const {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s.toString(); }
		if (s[0] == '-') {
			return "(- " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts, ids) + ")";
		}
		if (vars.count(s)) { return std::to_string(vars.at(s)); }
		if (s[0] == '(' and s.back() == ')') { return recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts, ids, isFirstLayer, embeddedEquals); }
		if (s[0] == '[' and s.back() == ']') { return ("(abs " + recToSmtLib(s.substr(1, s.length() - 2), vars, toDefine, sqrts, ids) + ')'); }
		if (s[0] == '!') { 
			if (embeddedEquals) {
				return ("(notReal " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts, ids, isFirstLayer, embeddedEquals) + ')');
			}
			else {
				return ("(not " + recToSmtLib(s.substr(1, s.length() - 1), vars, toDefine, sqrts, ids, isFirstLayer, embeddedEquals) + ')');
			}
		}
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
		if (s == "NaN") { return "1000000000000000"; }
		if (s[0] == 'e') { return std::to_string(eConstant); }
		if (s[0] == 0x03C0) { return std::to_string(piConstant); }
		if (s.find(AdvancedString(".")) != s.size()) { return s.toString();}
		toDefine.insert(s.toString());
		return s.toString();
	}

	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "(or " + recToSmtLib(s1, vars, toDefine, sqrts, ids, false, embeddedEquals) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids, false, embeddedEquals) + ")";
	case '&': {
		if (isFirstLayer) {
			return recToSmtLib(s1, vars, toDefine, sqrts, ids, true, embeddedEquals) + ")(assert " + recToSmtLib(s2, vars, toDefine, sqrts, ids, true, embeddedEquals);
		}
		return "(and " + recToSmtLib(s1, vars, toDefine, sqrts, ids, isFirstLayer, embeddedEquals) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids, isFirstLayer, embeddedEquals) + ")";
	}
	case 0x2260: {
		if (embeddedEquals) 
			return "(notReal (feqReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + "))";
		else 
			return "(not (feq " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + "))";
	}
	case '>': {
		if (embeddedEquals)
			return "(gReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
		else
			return "(> " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case 0x2265: {
		if (embeddedEquals)
			return "(geReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
		else
			return "(>= " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case '<': {
		if (embeddedEquals)
			return "(lReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
		else
			return "(< " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case 0x2264: {
		if (embeddedEquals) 
			return "(leReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
		else
			return "(<= " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case '=': {
		if (embeddedEquals) 
			return "(feqReal " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
		else 
			return "(feq " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	}
	case '+': return "(+ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '-': return "(- " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '*': return "(* " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '/': return "(/ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")";
	case '^': return "(^ " + recToSmtLib(s1, vars, toDefine, sqrts, ids) + " " + recToSmtLib(s2, vars, toDefine, sqrts, ids) + ")"; //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
	case 0x221A: {
		float rootBase = recGetResult(s1, vars, ids);
		std::string rootContent = recToSmtLib(s2, vars, toDefine, sqrts, ids);
		std::string rootFunName = (rootBase == 2.0 ? "sqrt" : (rootBase == 3.0 ? "root3" : (rootBase == 4.0 ? "root4" : "error")));
		if (rootFunName == "error") { //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
			Application::Get()->GetWindowUI()->DisplayError("Z3 can't process sqrt with power: " + std::to_string(rootBase));
			throw ErrorBoxException();
		}
		std::string sqrt = "(= (^ (" + rootFunName + " " + rootContent + ") " + std::to_string((int)rootBase) + ") " + rootContent + ")";
		auto it = std::find(sqrts.begin(), sqrts.end(), sqrt);
		if (it == sqrts.end()) {
			sqrts.push_back(sqrt);
		}
		return "(" + rootFunName + " " + rootContent + ")";
	}
	//ToDo add log to z3
	default: {
		Application::Get()->GetWindowUI()->DisplayError("Next operator not found: " + s.toString());
		throw ErrorBoxException();
	}
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
			if (s.substr(0, 3) == "ln(" and s.back() == ')') { return "log(" + recToShader(s.substr(3, s.length() - 4), vars, ids) + ")"; }
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
		if (s[0] == 'e') { return std::to_string(eConstant); }
		if (s[0] == 0x03C0) { return std::to_string(piConstant); }
		if (s == "x" or s == "y") { return "coords." + s.toString(); }
		bool succes; float val;
		std::tie(succes, val) = getVariable(s, ids);
		if (succes && isinf(val)) { return "1.0f/0.0f"; }
		if (succes && isnan(val)) { return "0.0f"; }
		if (succes) { return std::to_string(val); }
		Application::Get()->GetWindowUI()->DisplayError("Invalid statement: " + s.toString());
		throw ErrorBoxException();
	}	

 	AdvancedString s1 = s.substr(0, operIndex);
	AdvancedString s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "min(abs(" + recToShader(s1, vars, ids) + "), abs(" + recToShader(s2, vars, ids) + "))";
	case '&': return "max(abs(" + recToShader(s1, vars, ids) + "), abs(" + recToShader(s2, vars, ids) + "))";
	case 0x2260: return "((" + recToShader(s1, vars, ids) + " - " + recToShader(s2, vars, ids) + " == 0.0) ? -1 : 1.0)"; //Have to look into potential problems
	case '>': return "((" + recToShader(s1, vars, ids) + " > " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)";
	case 0x2265: return "((" + recToShader(s1, vars, ids) + " >= " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)";
	case '<': return "((" + recToShader(s1, vars, ids) + " < " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)";
	case 0x2264: return "((" + recToShader(s1, vars, ids) + " <= " + recToShader(s2, vars, ids) + ") ? 0.0 : 1/0.0)";
	case '=': return recToShader(s1, vars, ids) + " - (" + recToShader(s2, vars, ids) + ")";
	case '+': return recToShader(s1, vars, ids) + " + " + recToShader(s2, vars, ids);
	case '-': return recToShader(s1, vars, ids) + " - " + recToShader(s2, vars, ids);
	case '*': return recToShader(s1, vars, ids) + " * " + recToShader(s2, vars, ids);
	case '/': return recToShader(s1, vars, ids) + " / " + recToShader(s2, vars, ids);
	case '^': return "customPow( " + recToShader(s1, vars, ids) + ", " + recToShader(s2, vars, ids) + ")"; 
	case 0x221A: return "customPow( " + recToShader(s2, vars, ids) + ", (1.0 / " + recToShader(s1, vars, ids) + "))";
	case 0x33D2: return "log( " + recToShader(s2, vars, ids) + " ) / log( " + recToShader(s1, vars, ids) + ")";
	default: {
		Application::Get()->GetWindowUI()->DisplayError("Next operator not found: " + s.toString());
		throw ErrorBoxException();
	}
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
				if (!(c == '-' && (i == 0 || (std::find(std::begin(calcOrder), std::end(calcOrder), s[i - 1]) != std::end(calcOrder))) )) {
					best = std::distance(calcOrder, res);
					operIndex = i;
				}
			}
		}
	}

	if (depth != 0) {
		Application::Get()->GetWindowUI()->DisplayError("Invalid brackets:  " + s.toString());
		throw ErrorBoxException();
	}

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

AdvancedString operator+(const AdvancedString& s1, const unsigned int& s2) {
	AdvancedString res = s1;
	res.content.insert(res.content.end(), s2);
	return res;
}

AdvancedString operator+(const unsigned int& s1, const AdvancedString& s2) {
	AdvancedString res = s2;
	res.content.insert(res.content.begin(), s1);
	return res;
}

void operator+=(AdvancedString& s1, const AdvancedString& s2)
{
	s1.content.insert(s1.content.end(), s2.content.begin(), s2.content.end());
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

bool operator==(const AdvancedString& s1, const char& s2) {
	return s1.size() == 1 && s1[0] == s2;
}

bool operator==(const char& s1, const AdvancedString& s2) {
	return s2 == s1;
}

bool operator<(const AdvancedString& s1, const AdvancedString& s2) {
	return s1.content < s2.content;
}