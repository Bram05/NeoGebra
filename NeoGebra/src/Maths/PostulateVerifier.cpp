#include "PostulateVerifier.h"
#include "Application.h"

bool PostulateVerifier::I2(const Model& model) {
	///
	/// Check if there exists a line, for which (not (exists (two distinct points)))
	/// 
	/// (declare-const l0 Real)
	/// ...
	/// (declare-const lm Real)
	/// [line def]
	/// (assert 
	///		(not 
	///			(exists ((p0 Real) ... (pn Real) (q0 Real) ... (qn Real))
	///				(and [point def p] 
	///					(and [point def q]
	///						[p != q]
	///					)
	///				)
	///			)
	///		)
	/// )
	/// 
	// Generate extra code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::pair<std::string, std::string>> sqrts;
	std::map<AdvancedString, float> tmp2;
	std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >> m = model.m_Variables.second;

	//Line def
	int definedSqrts = 0;
	smt = "(assert " + model.m_LineDef.recToSmtLib(model.m_LineDef.m_EquationString, tmp2, tmp, sqrts, {}, true) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		std::string def = sqrts[i].first;
		std::string pow = sqrts[i].second;
		smt = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + smt;
	}
	smt = "(declare-const x Real)(declare-const y Real)" + smt;

	// Not exists with two point definitions
	smt += "(assert (not (exists (";
	std::string pointVarName = model.m_PointDef.m_NumberedVarNames[0].toString();
	for (int p = 0; p < model.m_PointIdentifiers; p++) {
		smt += "(" + pointVarName + "a" + std::to_string(p) + " Real)";
		smt += "(" + pointVarName + "b" + std::to_string(p) + " Real)";
	}
	Equation pointDefA = model.m_PointDef;
	Equation pointDefB = model.m_PointDef;
	pointDefA.replaceVarName(pointDefA.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "a");
	pointDefB.replaceVarName(pointDefB.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "b");
	std::string ABsmt = "(and " + pointDefA.recToSmtLib(pointDefA.m_EquationString, tmp2, tmp, sqrts, {}, false) + " " + pointDefB.recToSmtLib(pointDefB.m_EquationString, tmp2, tmp, sqrts, {}, false) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		std::string def = sqrts[i].first;
		std::string pow = sqrts[i].second;
		smt += "(sqrt" + std::to_string(i) + " Real)";
		ABsmt = "(and " + ABsmt + " " + "(and (>= sqrt" + std::to_string(i) + " 0) (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + ")))";
	}
	// Points identifiers are not the same
	smt += ") (and " + ABsmt + " ";
	std::string isNotTheSameSmt = "(not (= " + pointVarName + "a0 " + pointVarName + "b0))";
	for (int i = 1; i < model.m_PointIdentifiers; ++i) {
		isNotTheSameSmt = "(and " + isNotTheSameSmt + " (not (= " + pointVarName + "a" + std::to_string(i) + " " + pointVarName + "b" + std::to_string(i) + ")))";
	}
	smt += isNotTheSameSmt + "))))(check-sat)";

	std::vector<std::string> resNames;
	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}
	smt = "(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))" + smt;

	// Check if solution exists
	z3::context c;
	z3::solver solver(c);
	Z3_ast_vector test2 = Z3_parse_smtlib2_string(c, smt.c_str(), 0, 0, 0, 0, 0, 0);

	if (Z3_ast_vector_size(c, test2) == 0) {
		Application::Get()->GetWindowUI()->DisplayError("Error with smtLibString:\n" + smt);
		throw ErrorBoxException();
	}

	for (int i{}; i < Z3_ast_vector_size(c, test2); ++i) {
		z3::expr tmp(c, Z3_ast_vector_get(c, test2, i));
		solver.add(tmp);
	}

	z3::params p(c);
	p.set(":timeout", 3000u);
	solver.set(p);
	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("Unable to test I-2");
		throw ErrorBoxException();
		}
	}
}