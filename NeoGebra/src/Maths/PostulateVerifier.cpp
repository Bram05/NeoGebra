#include "PostulateVerifier.h"
#include "Application.h"

///
// Standard functions:
//  (define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))
//  (define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0))
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


bool PostulateVerifier::I2(const Model& model) {
	///
	/// Check if there exists a line, for which (not (exists (two distinct points)))
	/// 
	/// (declare-const l0 Real)
	/// ...
	/// (declare-const ln Real)
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
	
	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

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

	incidenceA.replaceVarName(incidenceA.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
	incidenceB.replaceVarName(incidenceB.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);

	pointDefA.replaceVarName(pointDefA.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "a");
	incidenceA.replaceVarName(incidenceA.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "a");
	pointDefB.replaceVarName(pointDefB.m_EquationString, model.m_PointDef.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "b");
	incidenceB.replaceVarName(incidenceB.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + "b");
	std::string ABsmt = "(and (and " + incidenceA.recToSmtLib(incidenceA.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " " + incidenceB.recToSmtLib(incidenceB.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + + ") (and " + pointDefA.recToSmtLib(pointDefA.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " " + pointDefB.recToSmtLib(pointDefB.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + "))";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		ABsmt = "(and " + sqrts[i] + " " + ABsmt + ")";
	}
	definedSqrts = sqrts.size();

	// Point vars, sqrt definitions inside exists
	smt = Equation::getVarFunsSmt(point, model, ABsmt, sqrts, 2) + smt;
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
	std::string isNotTheSameSmt = "(feq " + pointVarName + "a0 " + pointVarName + "b0)";
	for (int i = 1; i < model.m_PointIdentifiers; ++i) {
		isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName + "a" + std::to_string(i) + " " + pointVarName + "b" + std::to_string(i) + "))";
	}
	smt += "(not " + isNotTheSameSmt + ")))))(check-sat)";

	// Add vars
	smt = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}

	//  Standard functions (See top of document)
	smt =  "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;
	
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
	
	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;
	
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
		std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
		for (int i = 1; i < model.m_PointIdentifiers; ++i) {
			isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
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

	// Line Vars, sqrts inside exists
	smt = Equation::getVarFunsSmt(line, model, incidenceSmt, sqrts) + smt ;

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		incidenceSmt = "(and " + sqrts[i] + " " + incidenceSmt + ")";
	}
	definedSqrts = sqrts.size();

	smt += ") " + incidenceSmt + ")))(check-sat)";

	// Add vars
	smt = Equation::getVarFunsSmt(point, model, smt, sqrts, 3) + smt;
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

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("C-3: Not 100% certain");
		return false;
	}
	}
}

bool PostulateVerifier::B1(const Model& model) {
	///	
	///  (declare-const p0 Real)
	///  ...
	///  (declare-const pn Real)
	///  (declare-const q0 Real)
	///  ...
	///  (declare-const qn Real)
	///  (declare-const r0 Real)
	///  ...
	///  (declare-const rn Real)
	///  [point def p]
	///  [point def q]
	///  [point def r]
	///  
	///  (assert [p*q*r])
	///  (assert ![r*q*p])
	/// 
	
	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

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
		std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
		for (int i = 1; i < model.m_PointIdentifiers; ++i) {
			isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
		}
		smt += "(assert (not " + isNotTheSameSmt + "))";
	}

	//Line def
	AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
	smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = "(declare-const xl Real)(declare-const yl Real)" + smt;

	for (int pNameN = 0; pNameN < 3; ++pNameN) {
		//Incidence def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString incidenceEquation = model.m_IncidenceConstr.m_EquationString;
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[0], pName);
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		smt += "(assert " + model.m_IncidenceConstr.recToSmtLib(incidenceEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
	}

	//betweenness 1 (p*q*r)
	AdvancedString betweennessEquation = model.m_BetweennessConstr.m_EquationString;
	for (int i = 0; i < 3; ++i) {
		model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a' + i));
	}
	smt += "(assert " + model.m_BetweennessConstr.recToSmtLib(betweennessEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	
	//betweenness 2 (not r*q*p)
	AdvancedString betweennessEquation2 = model.m_BetweennessConstr.m_EquationString;
	for (int i = 2; i >= 0; --i) {
		model.m_BetweennessConstr.replaceVarName(betweennessEquation2, model.m_BetweennessConstr.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a' + i));
	}
	smt += "(assert (not " + model.m_BetweennessConstr.recToSmtLib(betweennessEquation2, tmp2, tmp, sqrts, {}, false, false) + "))";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//Add vars
	smt  = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	smt = Equation::getVarFunsSmt(point, model, smt, sqrts, 3) + smt;
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

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}
	smt += "(check-sat)";

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;
	
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

	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("B-1: Not 100% certain");
		return false;
	}
	}
}

bool PostulateVerifier::B2(const Model& model) {
	///	
	///  (declare-const p0 Real)
	///  ...
	///  (declare-const pn Real)
	///  (declare-const q0 Real)
	///  ...
	///  (declare-const qn Real)
	///  (declare-const l0 Real)
	///  ...
	///  (declare-const ln Real)
	///  [point def p]
	///  [point def q]
	///  [line def]
	///  [incidence p]
	///  [incidence q]
	///  (assert 
	///    (or
	///      (not
	///        (exists ((r0 Real)...(rn Real))
	///          (and
	///            [point def r]
	///            (and 
	///              [incidence r]
	///              [p*r*q]
	///            )
	///          )
	///        )
	///      )
	///      (not
	///        (exists ((r0 Real)...(rn Real))
	///          (and
	///            [point def r]
	///            (and 
	///              [incidence r]
	///              [p*q*r]
	///            )
	///          )
	///        )
	///      )
	///    )
	///  )
	/// 

	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

	int definedSqrts = 0;

	for (int pNameN = 0; pNameN < 2; ++pNameN) {
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
	std::string pointVarName1 = model.m_PointDef.m_NumberedVarNames[0].toString() + 'a';
	std::string pointVarName2 = model.m_PointDef.m_NumberedVarNames[0].toString() + 'b';
	std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
	for (int i = 1; i < model.m_PointIdentifiers; ++i) {
		isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
	}
	smt += "(assert (not " + isNotTheSameSmt + "))";

	//Line def
	AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
	smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = "(declare-const xl Real)(declare-const yl Real)" + smt;

	for (int pNameN = 0; pNameN < 2; ++pNameN) {
		//Incidence def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString incidenceEquation = model.m_IncidenceConstr.m_EquationString;
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[0], pName);
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		smt += "(assert " + model.m_IncidenceConstr.recToSmtLib(incidenceEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
	}

	smt += "(assert (or ";
	for (int n = 0; n < 2; n++) {
		// Not exists point with betweenness condition
		smt += "(not (exists (";
		AdvancedString pointVarName = model.m_PointDef.m_NumberedVarNames[0] + 'c';
		for (int p = 0; p < model.m_PointIdentifiers; p++) {
			smt += "(" + pointVarName.toString() + std::to_string(p) + " Real)";
		}

		smt += "(xc Real)(yc Real)) ";

		std::string insideExistsSmt = "(and (and ";
		// Incidence
		Equation incidence = model.m_IncidenceConstr;
		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], pointVarName);
		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		insideExistsSmt += incidence.recToSmtLib(incidence.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " ";

		// Point definition
		AdvancedString pointDefEquation = model.m_PointDef.m_EquationString;
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("x"), AdvancedString("xc"));
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("y"), AdvancedString("yc"));
		model.m_PointDef.replaceVarName(pointDefEquation, model.m_PointDef.m_NumberedVarNames[0], pointVarName);

		insideExistsSmt += model.m_PointDef.recToSmtLib(pointDefEquation, tmp2, tmp, sqrts, {}, false, false) + ") ";

		// Betweenness
		AdvancedString betweennessEquation = model.m_BetweennessConstr.m_EquationString;

		model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + 'a');
		model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[n == 0 ? 2 : 1], model.m_PointDef.m_NumberedVarNames[0] + 'b');
		model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[n == 0 ? 1 : 2], model.m_PointDef.m_NumberedVarNames[0] + 'c');

		insideExistsSmt += model.m_BetweennessConstr.recToSmtLib(betweennessEquation, tmp2, tmp, sqrts, {}, false, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			insideExistsSmt = "(and " + sqrts[i] + " " + insideExistsSmt + ")";
		}
		definedSqrts = sqrts.size();

		// Point Vars, sqrts inside exists
		smt = Equation::getVarFunsSmt(point, model, insideExistsSmt, sqrts, 3) + smt;
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
				if (j != 2) {
					smt = "(assert " + tmpSqrt + ")" + smt;
				}
				else {
					insideExistsSmt = "(and " + tmpSqrt + " " + insideExistsSmt + ")";
				}
			}
		}
		definedSqrts = sqrts.size();

		smt += insideExistsSmt + (n == 0 ? ")) " : "))))");
	}

	//Add vars
	smt = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	for (int i = 0; i < model.m_PointIdentifiers; ++i) {
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "a" + std::to_string(i) + " Real)" + smt;
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "b" + std::to_string(i) + " Real)" + smt;
	}

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}
	smt += "(check-sat)";

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("B-2: Not 100% certain");
		return true;
	}
	}
}

bool PostulateVerifier::B3(const Model& model) {
	///	
	///  (declare-const p0 Real)
	///  ...
	///  (declare-const pn Real)
	///  (declare-const q0 Real)
	///  ...
	///  (declare-const qn Real)
	///  (declare-const r0 Real)
	///  ...
	///  (declare-const rn Real)
	///  [point def p]
	///  [point def q]
	///  [point def r]
	///  
	///  (assert [p*q*r])
	///  (assert ![r*q*p])
	/// 

	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

	int definedSqrts = 0;

	for (int pNameN = 0; pNameN < 3; ++pNameN) {
		//Point def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString pointDefEquation = model.m_PointDef.m_EquationString;
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("x"), AdvancedString("x") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("y"), AdvancedString("y") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, model.m_PointDef.m_NumberedVarNames[0], pName);
		smt += "(assert " + model.m_PointDef.recToSmtLib(pointDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		smt = std::string("(declare-const x") + (char)('a' + pNameN) + std::string(" Real)(declare-const y") + (char)('a' + pNameN) + " Real)" + smt;
	}
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//Points are not the same
	for (int p = 0; p < 3; ++p) {
		std::string pointVarName1 = model.m_PointDef.m_NumberedVarNames[0].toString() + (p == 1 ? 'b' : 'a');
		std::string pointVarName2 = model.m_PointDef.m_NumberedVarNames[0].toString() + (p == 2 ? 'b' : 'c');
		std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
		for (int i = 1; i < model.m_PointIdentifiers; ++i) {
			isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
		}
		smt += "(assert (not " + isNotTheSameSmt + "))";
	}

	//Line def
	AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
	model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
	smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = "(declare-const xl Real)(declare-const yl Real)" + smt;

	for (int pNameN = 0; pNameN < 3; ++pNameN) {
		//Incidence def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString incidenceEquation = model.m_IncidenceConstr.m_EquationString;
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[0], pName);
		model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		smt += "(assert " + model.m_IncidenceConstr.recToSmtLib(incidenceEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		definedSqrts = sqrts.size();
	}
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}

	//betweenness 1 (p*q*r)
	AdvancedString betweennessEquation = model.m_BetweennessConstr.m_EquationString;
	for (int i = 0; i < 3; ++i) {
		model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a' + i));
	}
	smt += "(assert " + model.m_BetweennessConstr.recToSmtLib(betweennessEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//betweenness 2 (p*r*q)
	AdvancedString betweennessEquation2 = model.m_BetweennessConstr.m_EquationString;
	model.m_BetweennessConstr.replaceVarName(betweennessEquation2, model.m_BetweennessConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0] + 'a');
	model.m_BetweennessConstr.replaceVarName(betweennessEquation2, model.m_BetweennessConstr.m_NumberedVarNames[1], model.m_PointDef.m_NumberedVarNames[0] + 'c');
	model.m_BetweennessConstr.replaceVarName(betweennessEquation2, model.m_BetweennessConstr.m_NumberedVarNames[2], model.m_PointDef.m_NumberedVarNames[0] + 'b');
	smt += "(assert " + model.m_BetweennessConstr.recToSmtLib(betweennessEquation2, tmp2, tmp, sqrts, {}, true, false) + ")";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//Add vars
	smt = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	smt = Equation::getVarFunsSmt(point, model, smt, sqrts, 3) + smt;
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

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}
	smt += "(check-sat)";

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("B-3: Not 100% certain");
		return false;
	}
	}
}

bool PostulateVerifier::C3(const Model& model) {
	///	
	///  (declare-const p0 Real)
	/// ...
	/// (declare-const pn Real)
	/// (declare-const q0 Real)
	/// ...
	/// (declare-const qn Real)
	/// (declare-const r0 Real)
	/// ...
	/// (declare-const rn Real)
	/// (declare-const p'0 Real)
	/// ...
	/// (declare-const p'n Real)
	/// (declare-const q'0 Real)
	/// ...
	/// (declare-const q'n Real)
	/// (declare-const r'0 Real)
	/// ...
	/// (declare-const r'n Real)
	/// (declare-const l0 Real)
	/// ...
	/// (declare-const ln Real)
	/// (declare-const m0 Real)
	/// ...
	/// (declare-const mn Real)
	/// [point def p]
	/// [point def q]
	/// [point def r]
	/// [line def l]
	/// [incidence l p]
	/// [incidence l q]
	/// [incidence l r]
	/// [point def p']
	/// [point def q']
	/// [point def r']
	/// [line def m]
	/// [incidence m p']
	/// [incidence m q']
	/// [incidence m r']
	/// 
	/// (assert [p*q*r])
	/// (assert [p'*q'*r'])
	/// (assert (= [d p q] [d p' q']))
	/// (assert (= [d q r] [d q' r']))
	/// (assert !(= [d p r] [d p' r']))
	/// 

	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

	int definedSqrts = 0;

	for (int pNameN = 0; pNameN < 6; ++pNameN) {
		//Point def
		AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN);
		AdvancedString pointDefEquation = model.m_PointDef.m_EquationString;
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("x"), AdvancedString("x") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("y"), AdvancedString("y") + ('a' + pNameN));
		model.m_PointDef.replaceVarName(pointDefEquation, model.m_PointDef.m_NumberedVarNames[0], pName);
		smt += "(assert " + model.m_PointDef.recToSmtLib(pointDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		smt = std::string("(declare-const x") + (char)('a' + pNameN) + std::string(" Real)(declare-const y") + (char)('a' + pNameN) + " Real)" + smt;
	}
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	// Sets of three points are not the same
	for (int n = 0; n < 2; ++n) {
		for (int p = 0; p < 3; ++p) {
			std::string pointVarName1 = model.m_PointDef.m_NumberedVarNames[0].toString() + (char)((p == 1 ? 'b' : 'a')+3*n);
			std::string pointVarName2 = model.m_PointDef.m_NumberedVarNames[0].toString() + (char)((p == 2 ? 'b' : 'c')+3*n);
			std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
			for (int i = 1; i < model.m_PointIdentifiers; ++i) {
				isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
			}
			smt += "(assert (not " + isNotTheSameSmt + "))";
		}
	}

	for (int n = 0; n < 2; ++n) {
		//Line def
		AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
		model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl")+('a'+n));
		model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl")+('a'+n));
		model.m_LineDef.replaceVarName(lineDefEquation, model.m_LineDef.m_NumberedVarNames[0], model.m_LineDef.m_NumberedVarNames[0] + ('a' + n));
		smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
	}
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();
	smt = "(declare-const xla Real)(declare-const yla Real)(declare-const xlb Real)(declare-const ylb Real)" + smt;

	for (int n = 0; n < 2; ++n) {
		for (int pNameN = 0; pNameN < 3; ++pNameN) {
			//Incidence def
			AdvancedString pName = model.m_PointDef.m_NumberedVarNames[0] + ('a' + pNameN + n*3);
			AdvancedString incidenceEquation = model.m_IncidenceConstr.m_EquationString;
			model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[0], pName);
			model.m_IncidenceConstr.replaceVarName(incidenceEquation, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0] + ('a'+n));
			smt += "(assert " + model.m_IncidenceConstr.recToSmtLib(incidenceEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
			for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
				smt = "(assert " + sqrts[i] + ")" + smt;
			}
			definedSqrts = sqrts.size();
		}
	}

	//betweenness 1&2 (p*q*r & p*q*r)
	for (int n = 0; n < 2; ++n) {
		AdvancedString betweennessEquation = model.m_BetweennessConstr.m_EquationString;
		for (int i = 0; i < 3; ++i) {
			model.m_BetweennessConstr.replaceVarName(betweennessEquation, model.m_BetweennessConstr.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a' + i + 3*n));
		}
		smt += "(assert " + model.m_BetweennessConstr.recToSmtLib(betweennessEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
	}

	//Distance 1&2
	for (int n = 0; n < 2; ++n) {
		AdvancedString distanceEquation1 = model.m_DistanceDef.m_EquationString;
		AdvancedString distanceEquation2 = model.m_DistanceDef.m_EquationString;
		for (int i = 0; i < 2; ++i) {
			model.m_DistanceDef.replaceVarName(distanceEquation1, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a'+i+n));
			model.m_DistanceDef.replaceVarName(distanceEquation2, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('d'+i+n));
		}
		smt += "(assert (feq " + model.m_DistanceDef.recToSmtLib(distanceEquation1, tmp2, tmp, sqrts, {}, false, false) + " " + model.m_DistanceDef.recToSmtLib(distanceEquation2, tmp2, tmp, sqrts, {}, false, false) + "))";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
	}

	//Distance 3
	AdvancedString distanceEquation1 = model.m_DistanceDef.m_EquationString;
	AdvancedString distanceEquation2 = model.m_DistanceDef.m_EquationString;
	for (int i = 0; i < 2; ++i) {
		model.m_DistanceDef.replaceVarName(distanceEquation1, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a' + 2 * i));
		model.m_DistanceDef.replaceVarName(distanceEquation2, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('d' + 2 * i));
	}
	smt += "(assert (not (feq " + model.m_DistanceDef.recToSmtLib(distanceEquation1, tmp2, tmp, sqrts, {}, false, false) + " " + model.m_DistanceDef.recToSmtLib(distanceEquation2, tmp2, tmp, sqrts, {}, false, false) + ")))";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//Add vars
	definedSqrts = sqrts.size();
	smt = Equation::getVarFunsSmt(line, model, smt, sqrts, 2) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		for (int j = 0; j < 2; ++j) {
			std::string tmpSqrt = sqrts[i];
			for (int k = 0; k < model.m_LineIdentifiers; ++k) {
				auto loc = tmpSqrt.find(model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(k));
				while (loc != std::string::npos) {
					tmpSqrt.replace(loc, model.m_LineDef.m_NumberedVarNames[0].length() + 1, model.m_LineDef.m_NumberedVarNames[0].toString() + (char)('a' + j) + std::to_string(k));
					loc = tmpSqrt.find(model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(k), loc + 1 + model.m_LineDef.m_NumberedVarNames[0].length());
				}
			}
			smt = "(assert " + tmpSqrt + ")" + smt;
		}
	}
	definedSqrts = sqrts.size();

	smt = Equation::getVarFunsSmt(point, model, smt, sqrts, 6) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		for (int j = 0; j < 6; ++j) {
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

	for (int n = 0; n < 6; ++n) {
		for (int i = 0; i < model.m_PointIdentifiers; ++i) {
			smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + (char)('a'+n) + std::to_string(i) + " Real)" + smt;
		}
	}

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + "a" + std::to_string(i) + " Real)" + smt;
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + "b" + std::to_string(i) + " Real)" + smt;
	}
	smt += "(check-sat)";

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("C-3: Not 100% certain");
		return true;
	}
	}
}

bool PostulateVerifier::DISTANCE(const Model& model) {
	///	
	///  (declare-const p0 Real)
	///  ...
	///  (declare-const pn Real)
	///  (declare-const q0 Real)
	///  ...
	///  (declare-const qn Real)
	///  [point def p]
	///  [point def q]
	///  
	///  (assert !(= [d p q] [d q p]))
	/// 

	// Generate code for z3
	std::string smt{};
	std::set<std::string> tmp;
	std::vector<std::string> sqrts;
	std::map<AdvancedString, float> tmp2;

	int definedSqrts = 0;

	for (int pNameN = 0; pNameN < 2; ++pNameN) {
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
	std::string pointVarName1 = model.m_PointDef.m_NumberedVarNames[0].toString() + 'a';
	std::string pointVarName2 = model.m_PointDef.m_NumberedVarNames[0].toString() + 'b';
	std::string isNotTheSameSmt = "(feq " + pointVarName1 + "0 " + pointVarName2 + "0)";
	for (int i = 1; i < model.m_PointIdentifiers; ++i) {
		isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feq " + pointVarName1 + std::to_string(i) + " " + pointVarName2 + std::to_string(i) + "))";
	}
	smt += "(assert (not " + isNotTheSameSmt + "))";

	//Distance
	AdvancedString distanceEquation1 = model.m_DistanceDef.m_EquationString;
	AdvancedString distanceEquation2 = model.m_DistanceDef.m_EquationString;
	for (int i = 0; i < 2; ++i) {
		model.m_DistanceDef.replaceVarName(distanceEquation1, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('a'+i));
		model.m_DistanceDef.replaceVarName(distanceEquation2, model.m_DistanceDef.m_NumberedVarNames[i], model.m_PointDef.m_NumberedVarNames[0] + ('b'-i));
	}
	smt += "(assert (not (feq " + model.m_DistanceDef.recToSmtLib(distanceEquation1, tmp2, tmp, sqrts, {}, false, false) + " " + model.m_DistanceDef.recToSmtLib(distanceEquation2, tmp2, tmp, sqrts, {}, false, false) + ")))";
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	//Add vars
	smt = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
		smt = "(assert " + sqrts[i] + ")" + smt;
	}
	definedSqrts = sqrts.size();

	smt = Equation::getVarFunsSmt(point, model, smt, sqrts, 2) + smt;
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
			smt = "(assert " + tmpSqrt + ")" + smt;
		}
	}
	definedSqrts = sqrts.size();

	for (int i = 0; i < model.m_PointIdentifiers; ++i) {
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "a" + std::to_string(i) + " Real)" + smt;
		smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + "b" + std::to_string(i) + " Real)" + smt;
	}

	for (int i = 0; i < model.m_LineIdentifiers; ++i) {
		smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
	}
	smt += "(check-sat)";

	//  Standard functions (See top of document)
	smt = "(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

	switch (solver.check()) {
	case z3::sat: return false;
	case z3::unsat: return true;
	case z3::unknown: {
		Application::Get()->GetWindowUI()->DisplayError("DISTANCE: Not 100% certain");
		return true;
	}
	}
}

ParallelType PostulateVerifier::PARALLEL(const Model& model) {
	///	
	///  Use Z3 to find any valid line and point not on the line
	/// (declare-const p0 Real)
	/// ...
	/// (declare-const pn Real)
	/// (declare-const l0 Real)
	/// ...
	/// (declare-const ln Real)
	/// [point def]
	/// [line def]
	/// (assert ![incidence])
	/// (get-model)
	/// 
	/// 
	/// Run new Z3 instance to check if parallel lines exist
	/// (define-const p0 Real [p0])
	/// ...
	/// (define-const pn Real [pn])
	/// (define-const l0 Real [l0])
	/// ...
	/// (define-const ln Real [ln])
	/// (declare-const k0 Real)
	/// ...
	/// (declare-const kn Real)
	/// [line def k]
	/// [incidence p k]
	/// (assert (! (= [intersection0 l k] NaN)))
	/// 
	/// If true, run another Z3 instances to check if two parallel lines exist
	/// (define-const p0 Real [p0])
	/// ...
	/// (define-const pn Real [pn])
	/// (define-const l0 Real [l0])
	/// ...
	/// (define-const ln Real [ln])
	/// (declare-const k0 Real)
	/// ...
	/// (declare-const kn Real)
	/// (declare-const m0 Real)
	/// ...
	/// (declare-const mn Real)
	/// [line def k]
	/// [line def m]
	/// [incidence p k]
	/// [incidence p m]
	/// [k != m]
	/// (assert (= [intersection0 l k] NaN))
	/// (assert (= [intersection0 l m] NaN))
	/// 

	std::vector<float> pointIdentifiers(model.m_PointIdentifiers);
	std::vector<float> lineIdentifiers(model.m_LineIdentifiers);

	// Scope to prevent redefinition
	{
		// Generate code for z3
		std::string smt{};
		std::set<std::string> tmp;
		std::vector<std::string> sqrts;
		std::map<AdvancedString, float> tmp2;

		int definedSqrts = 0;

		//Point def
		AdvancedString pointDefEquation = model.m_PointDef.m_EquationString;
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("x"), AdvancedString("x") + 'p');
		model.m_PointDef.replaceVarName(pointDefEquation, AdvancedString("y"), AdvancedString("y") + 'p');
		smt += "(assert " + model.m_PointDef.recToSmtLib(pointDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
		smt = "(declare-const xp Real)(declare-const yp Real)" + smt;

		//Line def
		AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
		model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl"));
		model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl"));
		smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();
		smt = "(declare-const xl Real)(declare-const yl Real)" + smt;

		// Not Incidence
		Equation incidence = model.m_IncidenceConstr;

		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0]);
		incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0]);
		std::string incidenceRes = incidence.recToSmtLib(incidence.m_EquationString, tmp2, tmp, sqrts, {}, false, false);
		auto loc = incidenceRes.find("feq");
		while (loc != std::string::npos) {
			incidenceRes.replace(loc, 3, "feqBiggerError");
			loc = incidenceRes.find("feq", loc + 4);
		}
		smt += "(assert (not " + incidenceRes + "))";

		//Add vars
		smt = Equation::getVarFunsSmt(point, model, smt, sqrts) + smt;
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();

		smt = Equation::getVarFunsSmt(line, model, smt, sqrts) + smt;
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();

		for (int i = 0; i < model.m_PointIdentifiers; ++i) {
			smt = "(declare-const " + model.m_PointDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
		}

		for (int i = 0; i < model.m_LineIdentifiers; ++i) {
			smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i) + " Real)" + smt;
		}
		smt += "(check-sat)";

		//  Standard functions (See top of document)
		//  Also feqBiggerError function for incidence, to prevent future rounding errors when transfering values between z3 instances
		smt = "(define-fun feqBiggerError ((a Real)(b Real)) Bool (< (abs (- a b)) 0.1)) (define-fun feqBiggerErrorReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.1) 1.0 0.0))(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

		switch (solver.check()) {
		case z3::unsat:
		case z3::unknown: {
			Application::Get()->GetWindowUI()->DisplayError("PARALLEL: Could not find valid point/line");
			throw ErrorBoxException();
		}
		}
		// Get Z3 output
		z3::model z3model = solver.get_model();
		std::cout << z3model;
		std::string pointVarName = model.m_PointDef.m_NumberedVarNames[0].toString();
		std::string lineVarName = model.m_LineDef.m_NumberedVarNames[0].toString();
		for (int i = 0; i < z3model.num_consts(); ++i) {
			z3::func_decl ffunc = z3model.get_const_decl(i);
			std::string f = ffunc.name().str();
			if (pointVarName == f.substr(0, pointVarName.size()) && f.substr(pointVarName.size(), f.size() - pointVarName.size()).find_first_not_of("0123456789") == std::string::npos) {
				z3::expr fVal = z3model.get_const_interp(ffunc);
				pointIdentifiers[std::stoi(f.substr(pointVarName.size(), f.size() - pointVarName.size()))] = fVal.as_double();
			}
			if (lineVarName == f.substr(0, lineVarName.size()) && f.substr(lineVarName.size(), f.size() - lineVarName.size()).find_first_not_of("0123456789") == std::string::npos) {
				z3::expr fVal = z3model.get_const_interp(ffunc);
				lineIdentifiers[std::stoi(f.substr(lineVarName.size(), f.size() - lineVarName.size()))] = fVal.as_double();
			}
		}
	}

	// Run once with one parallel line and once with two
	for (int parallelLines = 1; parallelLines < 3; ++parallelLines) {
		// New Z3 instance
		// Generate code for z3
		std::string smt{};
		std::set<std::string> tmp;
		std::vector<std::string> sqrts;
		std::map<AdvancedString, float> tmp2;

		int definedSqrts = 0;

		for (int n = 0; n < parallelLines; ++n) {
			//Line def
			AdvancedString lName = model.m_LineDef.m_NumberedVarNames[0] + ('b' + n);
			AdvancedString lineDefEquation = model.m_LineDef.m_EquationString;
			model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("x"), AdvancedString("xl") + ('b' + n));
			model.m_LineDef.replaceVarName(lineDefEquation, AdvancedString("y"), AdvancedString("yl") + ('b' + n));
			model.m_LineDef.replaceVarName(lineDefEquation, model.m_LineDef.m_NumberedVarNames[0], lName);
			smt += "(assert " + model.m_LineDef.recToSmtLib(lineDefEquation, tmp2, tmp, sqrts, {}, true, false) + ")";

			for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
				smt = "(assert " + sqrts[i] + ")" + smt;
			}
			definedSqrts = sqrts.size();
		}
		smt = "(declare-const xlb Real)(declare-const ylb Real)(declare-const xlc Real)(declare-const ylc Real)" + smt;


		for (int n = 0; n < parallelLines; ++n) {
			// Incidence
			Equation incidence = model.m_IncidenceConstr;

			incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[0], model.m_PointDef.m_NumberedVarNames[0]);
			incidence.replaceVarName(incidence.m_EquationString, model.m_IncidenceConstr.m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0] + ('b'+n));
			smt += "(assert " + incidence.recToSmtLib(incidence.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + ")";
		}

		if (parallelLines == 2) {
			//Lines are not the same
			std::string lineVarName1 = model.m_LineDef.m_NumberedVarNames[0].toString() + 'b';
			std::string lineVarName2 = model.m_LineDef.m_NumberedVarNames[0].toString() + 'c';
			std::string isNotTheSameSmt = "(feqBiggerError " + lineVarName1 + "0 " + lineVarName2 + "0)";
			for (int i = 1; i < model.m_PointIdentifiers; ++i) {
				isNotTheSameSmt = "(and " + isNotTheSameSmt + " (feqBiggerError " + lineVarName1 + std::to_string(i) + " " + lineVarName2 + std::to_string(i) + "))";
			}
			smt += "(assert (not " + isNotTheSameSmt + "))";
		}

		for (int n = 0; n < parallelLines; ++n) {
			//Line parameters < 100000000000. To prevent Z3 from finding line with big parameters to satisfy equation
			for (int i = 0; i < model.m_LineIdentifiers; ++i) {
				smt += "(assert (< " + model.m_LineDef.m_NumberedVarNames[0].toString() + (char)('b' + n) + std::to_string(i) + " 100000000000))";
			}
		}

		for (int n = 0; n < parallelLines; ++n) {
			// Lines intersect
			Equation intersection0 = model.m_PointFromLines[0];
			intersection0.replaceVarName(intersection0.m_EquationString, model.m_PointFromLines[0].m_NumberedVarNames[0], model.m_LineDef.m_NumberedVarNames[0] + 'a');
			intersection0.replaceVarName(intersection0.m_EquationString, model.m_PointFromLines[0].m_NumberedVarNames[1], model.m_LineDef.m_NumberedVarNames[0] + ('b' + n));
			smt += "(assert (=" + intersection0.recToSmtLib(intersection0.m_EquationString, tmp2, tmp, sqrts, {}, false, false) + " 1000000000000000))";
		}

		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();

		// Add previously found line and point
		for (int i = 0; i < model.m_PointIdentifiers; ++i) {
			smt = "(define-const p" + std::to_string(i) + " Real " + std::to_string(pointIdentifiers[i]) + ")" + smt;
		}
		for (int i = 0; i < model.m_LineIdentifiers; ++i) {
			smt = "(define-const la" + std::to_string(i) + " Real " + std::to_string(lineIdentifiers[i]) + ")" + smt;
		}

		//Add vars
		smt = Equation::getVarFunsSmt(point, model, smt, sqrts) + smt;
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			smt = "(assert " + sqrts[i] + ")" + smt;
		}
		definedSqrts = sqrts.size();

		smt = Equation::getVarFunsSmt(line, model, smt, sqrts, 2) + smt;
		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
			for (int j = 0; j < parallelLines; ++j) {
				std::string tmpSqrt = sqrts[i];
				for (int k = 0; k < model.m_LineIdentifiers; ++k) {
					auto loc = tmpSqrt.find(model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(k));
					while (loc != std::string::npos) {
						tmpSqrt.replace(loc, model.m_LineDef.m_NumberedVarNames[0].length() + 1, model.m_LineDef.m_NumberedVarNames[0].toString() + (char)('b' + j) + std::to_string(k));
						loc = tmpSqrt.find(model.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(k), loc + 1 + model.m_LineDef.m_NumberedVarNames[0].length());
					}
				}
				smt = "(assert " + tmpSqrt + ")" + smt;
			}
		}
		definedSqrts = sqrts.size();

		for (int n = 0; n < parallelLines; ++n) {
			for (int i = 0; i < model.m_LineIdentifiers; ++i) {
				smt = "(declare-const " + model.m_LineDef.m_NumberedVarNames[0].toString() + (char)('b' + n) + std::to_string(i) + " Real)" + smt;
			}
		}

		smt += "(check-sat)";
		
		//  Standard functions (See top of document)
		//  Also feqBiggerError function for line comparison, to prevent future rounding errors 
		smt = "(define-fun feqBiggerError ((a Real)(b Real)) Bool (< (abs (- a b)) 0.1)) (define-fun feqBiggerErrorReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.1) 1.0 0.0))(declare-fun sqrt (Real) Real)(declare-fun root3 (Real) Real)(declare-fun root4 (Real) Real)(assert (forall ((rootInp Real)) (> (sqrt rootInp) 0.0)))(assert (forall ((rootInp Real)) (> (root4 rootInp) 0.0)))(define-fun feq ((a Real)(b Real)) Bool (< (abs (- a b)) 0.0001))(define-fun notReal ((a Real)) Real (ite (feq a 0) 1.0 0.0)) (define-fun feqReal ((a Real)(b Real)) Real (ite (< (abs (- a b)) 0.0001) 1.0 0.0)) (define-fun gReal ((a Real)(b Real)) Real (ite (> a b) 1.0 0.0)) (define-fun geReal ((a Real)(b Real)) Real (ite (>= a b) 1.0 0.0)) (define-fun lReal ((a Real)(b Real)) Real (ite (< a b) 1.0 0.0)) (define-fun leReal ((a Real)(b Real)) Real (ite (<= a b) 1.0 0.0))" + smt;

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

		if (parallelLines == 1) {
			switch (solver.check()) {
			case z3::unsat: return ELLIPTIC;
			case z3::unknown: {
				Application::Get()->GetWindowUI()->DisplayError("PARALLEL: Not 100% certain");
				return ELLIPTIC;
			}
			}
		}
		else {
			switch (solver.check()) {
			case z3::sat: return HYPERBOLIC;
			case z3::unsat: return EUCLIDEAN;
			case z3::unknown: {
				Application::Get()->GetWindowUI()->DisplayError("PARALLEL: Not 100% certain");
				return EUCLIDEAN;
			}
			}
		}
	}
}