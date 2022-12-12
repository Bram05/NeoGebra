#include "Z3Tools.h"

#define OPERNUM 12
const char calcOrder[OPERNUM] = { '|', '&', '!', '>', '<', '=', '+', '-', '*', '/', '^', '~' };

std::map<std::string, float> Z3Tools::extractVars(equation& s, const std::vector<std::vector<float>>& identifiers) {
	if (s.vars.size() != identifiers.size()) {
		throw std::invalid_argument("Invalid identifiers");
	}
	replace(s.eq, " ", "");
	std::map<std::string, float> m;
	for (int i = 0; i < s.vars.size(); ++i) {
		std::string varName = s.vars[i];
		for (int j = 0; j < identifiers[i].size(); ++j) {
			m[varName + std::to_string(j)] = identifiers[i][j];
		}
	}
	return m;
}

equation::equation(std::vector<std::string> vars, std::string eq) : vars{ vars }, eq{ eq } {}

equation::equation(const equation& e1, const equation& e2) {
	std::string s1 = e1.eq;
	std::string s2 = e2.eq;
	Z3Tools::replace(s1, " ", "");
	Z3Tools::replace(s2, " ", "");
	for (std::string var1 : e1.vars) {
		bool varNameAdded = false;
		for (std::string var2 : e2.vars) {
			if (var1 == var2) {
				varNameAdded = true;
				vars.push_back(var1 + 'a');
				Z3Tools::replaceVar(s1, var1, var1 + 'a');
			}
		}
		if (!varNameAdded) {
			vars.push_back(var1);
		}
	}
	for (std::string var2 : e2.vars) {
		bool varNameAdded = false;
		for (std::string var1 : e1.vars) {
			if (var1 == var2) {
				varNameAdded = true;
				vars.push_back(var2 + 'b');
				Z3Tools::replaceVar(s2, var2, var2 + 'b');
			}
		}
		if (!varNameAdded) {
			vars.push_back(var2);
		}
	}
	eq = "(" + s1 + ")&(" + s2 + ")";
}

void Z3Tools::replaceVar(std::string& s, const std::string& from, const std::string& to) {
	replace(s, " ", "");
	std::regex reg("(^|[\\(\\)\\[\\]|&!><=+\\-*\\^~])(" + from + ")([0-9]*)([\\(\\)\\[\\]|&!><=+\\-*\\^~]|$)");
	// Needs to be run twice in case matches overlap
	for (int i = 0; i < 2; ++i) {
		s = std::regex_replace(s, reg, "$1" + to + "$3$4");
	}
}

equation operator+(const equation e1, const equation e2) {
	return equation{ e1, e2 };
}

equation operator!(const equation e) {
	return equation{ e.vars, "!(" + e.eq + ")" };
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
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::stof(s); }
		if (s[0] != '-') {
			if (vars.count(s)) { return vars.at(s); }
			if (s[0] == '(' and s.back() == ')') { return eval(s.substr(1, s.length() - 2), vars); }
			if (s[0] == '[' and s.back() == ']') { return std::abs(eval(s.substr(1, s.length() - 2), vars)); }
			if (s[0] == '!') { return !eval(s.substr(1, s.length() - 1), vars); }
		}
		else {
			if (vars.count(s.substr(1, s.length() - 1))) { return -vars.at(s.substr(1, s.length() - 1)); }
			if (s[1] == '(' and s.back() == ')') { return -eval(s.substr(2, s.length() - 3), vars); }
			if (s[1] == '[' and s.back() == ']') { return -std::abs(eval(s.substr(2, s.length() - 3), vars)); }
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
	case '~': return std::pow(eval(s2, vars), 1 / eval(s1, vars));
	default:  throw std::invalid_argument("Invalid operator");
	}
}

equationResult Z3Tools::isSolvable(equation s, const std::vector<std::vector<float>>& identifiers) {
	z3::context c;
	z3::solver solver(c);

	Z3_ast_vector test2 = Z3_parse_smtlib2_string(c, toLisp(s.eq, extractVars(s, identifiers)).c_str(), 0, 0, 0, 0, 0, 0);

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

std::string Z3Tools::toLisp(const std::string& s, const std::map<std::string, float>& vars) {
	std::set<std::string> toDefine;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::string out = "(assert " + recToLisp(s, vars, toDefine, sqrts, true) + ")(check-sat)";

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

std::string Z3Tools::recToLisp(const std::string& s, const std::map<std::string, float>& vars, std::set<std::string>& toDefine, std::vector<std::pair<std::string, std::string>>& sqrts, bool isFirstLayer) {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return s; }
		if (s[0] != '-') {
			if (vars.count(s)) { return std::to_string(vars.at(s)); }
			if (s[0] == '(' and s.back() == ')') { return recToLisp(s.substr(1, s.length() - 2), vars, toDefine, sqrts); } 
			if (s[0] == '[' and s.back() == ']') { return ("(abs " + recToLisp(s.substr(1, s.length() - 2), vars, toDefine, sqrts) + ')'); }
			if (s[0] == '!') { return ("(not " + recToLisp(s.substr(1, s.length() - 1), vars, toDefine, sqrts) + ')'); }
		}
		else {
			if (vars.count(s.substr(1, s.length() - 1))) { return std::to_string(-vars.at(s.substr(1, s.length() - 1))); }
			if (s[1] == '(' and s.back() == ')') { return ("(- " + recToLisp(s.substr(2, s.length() - 3), vars, toDefine, sqrts) + ")"); }
			if (s[1] == '[' and s.back() == ']') { return ("(- (abs " + recToLisp(s.substr(2, s.length() - 3), vars, toDefine, sqrts) + "))"); }
		}
		if (s == "t") { return "true"; }
		if (s == "f") { return "false"; }
		toDefine.insert(s);
		return s;
	}

	std::string s1 = s.substr(0, operIndex);
	std::string s2 = s.substr(operIndex + 1, s.length() - operIndex - 1);

	switch (s[operIndex]) {
	case '|': return "(or " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '&': {
		if (isFirstLayer) {
			return recToLisp(s1, vars, toDefine, sqrts) + ")(assert " + recToLisp(s2, vars, toDefine, sqrts, true);
		}
		return "(and " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	}
	case '!': return "(not (feq " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + "))";
	case '>':
		if (!orEquals) { return "(> " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")"; }
		else { return "(>= " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts) + ")"; }
	case '<':
		if (!orEquals) { return "(< " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")"; }
		else { return "(<= " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2.substr(1, s2.length() - 1), vars, toDefine, sqrts) + ")"; }
	case '=': return "(feq " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '+': return "(+ " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '-': return "(- " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '*': return "(* " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '/': return "(/ " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")";
	case '^': return "(^ " + recToLisp(s1, vars, toDefine, sqrts) + " " + recToLisp(s2, vars, toDefine, sqrts) + ")"; //s2 only ints (https://stackoverflow.com/questions/36812843/why-z3-always-return-unknown-when-assertions-have-power)
	case '~': {
		std::pair<std::string, std::string> sqrt = { recToLisp(s2, vars, toDefine, sqrts) , recToLisp(s1, vars, toDefine, sqrts) };
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

std::string Z3Tools::recToShader(const std::string& s, const std::map<std::string, float>& vars) {
	bool orEquals = false; // True if the > or < is a >= or <=
	int operIndex = getNextOperator(s, orEquals);

	// No operator found, can be: number, negative, brackets, abs, sqrt, not, t, f
	if (operIndex == -1) {
		if (isNumber(s)) { return std::to_string(std::stof(s)); }
		if (s[0] != '-') {
			if (vars.count(s)) { return std::to_string(vars.at(s)); }
			if (s[0] == '(' and s.back() == ')') { return "(" + recToShader(s.substr(1, s.length() - 2), vars) + ")"; }
			if (s[0] == '[' and s.back() == ']') { return ("abs(" + recToShader(s.substr(1, s.length() - 2), vars) + ')'); }
			if (s[0] == '!') { return ("((" + recToShader(s.substr(1, s.length() - 1), vars) + " == 0.0) ? 1<<100 : 0.0)"); } //Have to look into potential problems
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
	case '!': return "((" + recToShader(s1, vars) + " - " + recToShader(s2, vars) + " == 0.0) ? 1<<100 : 0.0)"; //Have to look into potential problems
	case '>':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " > " + recToShader(s2, vars) + ") ? 0.0 : 1<<100)"; }
		else { return "((" + recToShader(s1, vars) + " >= " + recToShader(s2, vars) + ") ? 0.0 : 1<<100)"; }
	case '<':
		if (!orEquals) { return "((" + recToShader(s1, vars) + " < " + recToShader(s2, vars) + ") ? 0.0 : 1<<100)"; }
		else { return "((" + recToShader(s1, vars) + " <= " + recToShader(s2, vars) + ") ? 0.0 : 1<<100)"; }
	case '=': return recToShader(s1, vars) + " - " + recToShader(s2, vars);
	case '+': return recToShader(s1, vars) + " + " + recToShader(s2, vars);
	case '-': return recToShader(s1, vars) + " - " + recToShader(s2, vars);
	case '*': return recToShader(s1, vars) + " * " + recToShader(s2, vars);
	case '/': return recToShader(s1, vars) + " / " + recToShader(s2, vars);
	case '^': return "pow( " + recToShader(s1, vars) + ", " + recToShader(s2, vars) + ")"; 
	case '~': return "pow( " + recToShader(s2, vars) + ", (1.0 / " + recToShader(s1, vars) + "))";
	default:  throw std::invalid_argument("Invalid operator");
	}
}

int Z3Tools::getNextOperator(const std::string& s, bool& orEquals) {
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