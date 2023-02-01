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
	///				(and [incidence p] 
	///					(and [incidence q]
	///						(and [pointdef p] 
	///							(and [pointdef q]
	///								[p != q]
	///							)
	///						)
	///					)
	///				)
	///			)
	///		)
	/// )
	/// 
	
	// Generate extra code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;
	std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >> m = model.m_Variables.second;

	//Line def
	int definedSqrts = 0;
	AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
	smt = "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = "(declare-const xl Real)(declare-const yl Real)" + smt;

	// Not exists with two point definitions
	smt += "(assert (not (exists (";
	std::string pointVarName = model.m_PointDef.m_NumberedVarNames[0].toString();
	for (int p = 0; p < model.m_PointIdentifiers; p++) {
		smt += "(" + pointVarName + "a" + std::to_string(p) + " Real)";
		smt += "(" + pointVarName + "b" + std::to_string(p) + " Real)";
	}
	smt += "(xa Real)(xb Real)(ya Real)(yb Real)";
	Equation incidenceA = model.m_IncidenceConstr;
	Equation incidenceB = model.m_IncidenceConstr;
	Equation pointDefA = model.m_PointDef;
	Equation pointDefB = model.m_PointDef;
	pointDefA.replaceVarName(pointDefA.m_EquationString, AdvancedString("x"), AdvancedString("xa"));
	pointDefA.replaceVarName(pointDefA.m_EquationString, AdvancedString("y"), AdvancedString("ya"));
	pointDefB.replaceVarName(pointDefB.m_EquationString, AdvancedString("x"), AdvancedString("xb"));
	pointDefB.replaceVarName(pointDefB.m_EquationString, AdvancedString("y"), AdvancedString("yb"));

	incidenceA.replaceVarName(incidenceA.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0]);
	incidenceB.replaceVarName(incidenceB.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0]);
	incidenceA.replaceVarName(incidenceA.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
	incidenceB.replaceVarName(incidenceB.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);

	pointDefA.replaceVarName(pointDefA.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "a");
	incidenceA.replaceVarName(incidenceA.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_IncidenceConstr.m_NumberedVarNames[0] + "a");
	pointDefB.replaceVarName(pointDefB.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "b");
	incidenceB.replaceVarName(incidenceB.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_IncidenceConstr.m_NumberedVarNames[0] + "b");
	std::string ABsmt = "(and (and " + incidenceA.recToSmtLib(incidenceA.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " " + incidenceB.recToSmtLib(incidenceB.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + + ") (and " + pointDefA.recToSmtLib(pointDefA.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " " + pointDefB.recToSmtLib(pointDefB.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + "))";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		ABsmt = "(and " + sqrts[i] + " " + ABsmt + ")";
	}
	definedSqrts = sqrts.size();

	smt = Equation::getVarFunsSmt(point, model, ABsmt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		for (int j = 0; j < 2; ++j) {
			std::string tmpSqrt = sqrts[i];
			for (int k = 0; k < model.m_PointIdentifiers; ++k) {
				auto loc = tmpSqrt.find(model.m_PointDef.m_NumberedVarNames[0].toString() + std::to_string(k));
				while (loc != std::string::npos) {
					tmpSqrt.replace(loc, model.m_PointDef.m_NumberedVarNames[0].length() + 1, model.m_PointDef.m_NumberedVarNames[0].toString() + (char)('a' + j) + std::to_string(k));
					loc = tmpSqrt.find(model.m_PointDef.m_NumberedVarNames[0].toString() + std::to_string(k), loc + 1 + model.m_PointDef.m_NumberedVarNames[0].length());
				}
			}
			ABsmt = "(and " + tmpSqrt + " " + ABsmt + ")";
		}
	}
	definedSqrts = sqrts.size();

	smt += ") (and " + ABsmt + " ";
	
	// Points identifiers are not the same
	std::string isNotTheSameSmt = "(= " + pointVarName + "a0 " + pointVarName + "b0)";
	for (int i = 1; i < model.m_PointIdentifiers; ++i) {
		isNotTheSameSmt = "(and " + isNotTheSameSmt + " (= " + pointVarName + "a" + std::to_string(i) + " " + pointVarName + "b" + std::to_string(i) + "))";
	}
	smt += "(not " + isNotTheSameSmt + ")))))(check-sat)";

	std::string tmpSmt = Equation::getVarFunsSmt(line, model, smt, sqrts);
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = tmpSmt + smt;

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}

	///
	//  (define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))
	//	(define-fun feqReal((a Real)(b Real)) Real(ite(< (abs(- a b)) 0.0001) 1.0 0.0))
	//	(define-fun gReal((a Real)(b Real)) Real(ite(> a b) 1.0 0.0))
	//	(define-fun geReal((a Real)(b Real)) Real(ite(>= a b) 1.0 0.0))
	//	(define-fun lReal((a Real)(b Real)) Real(ite(< a b) 1.0 0.0))
	//	(define-fun leReal((a Real)(b Real)) Real(ite(<= a b) 1.0 0.0))
	//  (declare-fun sqrt (Real) Real)
	//  (declare-fun root3 (Real) Real)
	//  (declare-fun root4 (Real) Real)
	//  (assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))
	//  (assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))
	/// 
	smt =  "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;
	
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

bool PostulateVerifier::I3(const Model& model) {
	///
	/// Check if there exists a line, for which (not (exists (two distinct points)))
	/// 
	/// (declare-const p0 Real)
	/// ...
	/// (declare-const pn Real)
	/// (declare-const q0 Real)
	/// ...
	/// (declare-const qn Real)
	/// (declare-const r0 Real)
	/// ...
	/// (declare-const rn Real)
	/// 
	/// [p != q != r]
	/// 
	/// [point def p]
	/// [point def q]
	/// [point def r]
	/// (assert 
	///		(not 
	///			(exists ((l0 Real)...(ln Real))
	///				(and
	///					(and [incidence p] 
	///						(and [incidence q]
	///							[incidence r]
	///						)
	///					)
	///					[linedef]
	///				)
	///			)
	///		)
	/// )
	/// 
	
	// Generate extra code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;
	std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >> m = model.m_Variables.second;
	
	int definedSqrts = 0;

	for (int pNameN = 0; pNameN < 3; ++pNameN) {
		//Point def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString pointDefEquation = model.m_PointDef.m_EquationString;
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("x"), AdvancedString("x") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("y"), AdvancedString("y") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, model.m_PointDef.m_NumberedVarNames[0], pName);
		smt += "(assert " + model.m_PointDef.recToSmtLib(pointDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
		smt = std::string("(declare-const x") + (char)('a' + pNameN) + std::string(" Real)(declare-const y") + (char)('a' + pNameN) + " Real)" + smt;
	}

	//Points are not the same
	for (int p = 0; p < 3; ++p) {
		std::string pointVarName1 = model.m_PointDef.m_NumberedVarNames[0].toString() + (p == 1 ? 'b' : 'a');
		std::string pointVarName2 = model.m_PointDef.m_NumberedVarNames[0].toString() + (p == 2 ? 'b' : 'c');
		std::string isNotTheSameSmt = "(= " + pointVarName1 + "0 " + pointVarName2 + "0)";
		for (int i = 1; i < model.m_PointIdentifiers; ++i) {
			isNotTheSameSmt = "(and " + isNotTheSameSmt + " (= " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
		}
		smt += "(assert (not " + isNotTheSameSmt + "))";
	}

	// Not exists line incident with all three points
	smt += "(assert (not (exists (";
	std::string lineVarName = model.m_LineDef.m_NumberedVarNames[0].toString();
	for (int p = 0; p < model.m_LineIdentifiers; p++) {
		smt += "(" + lineVarName + std::to_string(p) + " Real)";
	}
	smt += "(xl Real)(yl Real)";
	std::string incidenceSmt = "(and (and ";
	for (int pNameN = 0; pNameN < 3; ++pNameN) {
		// Incidence per point
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		Equation incidence = model.m_IncidenceConstr;

		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], pName);
		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		incidenceSmt += incidence.recToSmtLib(incidence.m_EquationString, tmp2, tmp, sqrts, {}, false, false);
		incidenceSmt += pNameN == 0 ? " " : ") ";
	}

	// Line definition
	AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
	incidenceSmt = "(and " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, false, false) + " " + incidenceSmt + ")";

	smt = Equation::getVarFunsSmt(line, model, incidenceSmt, sqrts) + smt ;

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		incidenceSmt = "(and " + sqrts[i] + " " + incidenceSmt + ")";
	}
	definedSqrts = sqrts.size();

	smt += ") " + incidenceSmt + ")))(check-sat)";

	smt = Equation::getVarFunsSmt(point, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		for (int j = 0; j < 3; ++j) {
			std::string tmpSqrt = sqrts[i];
			for (int k = 0; k < model.m_PointIdentifiers; ++k) {
				auto loc = tmpSqrt.find(model.m_PointDef.m_NumberedVarNames[0].toString() + std::to_string(k));
				while (loc != std::string::npos) {
					tmpSqrt.replace(loc, model.m_PointDef.m_NumberedVarNames[0].length() + 1, model.m_PointDef.m_NumberedVarNames[0].toString() + (char)('a' + j) + std::to_string(k));
					loc = tmpSqrt.find(model.m_PointDef.m_NumberedVarNames[0].toString() + std::to_string(k), loc + 1 + model.m_PointDef.m_NumberedVarNames[0].length());
				}
			}
			smt = "(assert " + tmpSqrt + ")" + smt;
		}
	}
	definedSqrts = sqrts.size();

	for (int i = 0; i < model.m_PointIdentifiers; ++i) {
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "a" + std::to_string(i) + " Real)" + smt;
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "b" + std::to_string(i) + " Real)" + smt;
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "c" + std::to_string(i) + " Real)" + smt;
	}

	///
	//  (define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))
	//	(define-fun feqReal((a Real)(b Real)) Real(ite(< (abs(- a b)) 0.0001) 1.0 0.0))
	//	(define-fun gReal((a Real)(b Real)) Real(ite(> a b) 1.0 0.0))
	//	(define-fun geReal((a Real)(b Real)) Real(ite(>= a b) 1.0 0.0))
	//	(define-fun lReal((a Real)(b Real)) Real(ite(< a b) 1.0 0.0))
	//	(define-fun leReal((a Real)(b Real)) Real(ite(<= a b) 1.0 0.0))
	//  (declare-fun sqrt (Real) Real)
	//  (declare-fun root3 (Real) Real)
	//  (declare-fun root4 (Real) Real)
	//  (assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))
	//  (assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))
	/// 
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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
	case z3::sat: return true;
	case z3::unsat: return false;
	case z3::unknown: return false;
	}
}