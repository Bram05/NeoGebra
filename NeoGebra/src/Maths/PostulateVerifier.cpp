//#include "PostulateVerifier.h"
//
//bool PostulateVerifier::I2(const Model& m) {
//	///
//	/// Check if there exists a line, for which (not (exists (two distinct points)))
//	/// 
//	/// (declare-const l0 Real)
//	/// ...
//	/// (declare-const lm Real)
//	/// [line def]
//	/// (assert 
//	///		(not 
//	///			(exists ((p0 Real) ... (pn Real) (q0 Real) ... (qn Real))
//	///				(and [point def p] 
//	///					(and [point def q]
//	///						[p != q]
//	///					)
//	///				)
//	///			)
//	///		)
//	/// )
//	/// 
//	// Generate extra code for z3
//	std::string extraSMT{};
//	std::set<std::string> tmp;
//	std::vector<std::pair<std::string, std::string>> sqrts;
//	std::map<AdvancedString, float> tmp2;
//	std::vector<std::pair < AdvancedString, std::shared_ptr<Equation> >> m = e1.getType() == line ? m_Variables.first : m_Variables.second;
//	Equation& def = e1.getType() == line ? m_PointDef : m_LineDef;
//	int definedSqrts = 0;
//	extraSMT = "(assert " + def.recToSmtLib(def.m_EquationString, tmp2, tmp, sqrts, {}, true) + ")";
//	for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
//		std::string def = sqrts[i].first;
//		std::string pow = sqrts[i].second;
//		extraSMT = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + extraSMT;
//	}
//	extraSMT = "(declare-const x Real)(declare-const y Real)" + extraSMT;
//	definedSqrts = sqrts.size();
//	for (int i = m.size() - 1; i >= 0; --i) {
//		extraSMT = "(define-fun " + m_IncidenceConstr.m_NumberedVarNames[e1.getType() == line ? 0 : 1].toString() + "." + m[i].first.toString() + " () Real " + m[i].second->recToSmtLib(m[i].second->m_EquationString, tmp2, tmp, sqrts, {}, true) + ")" + extraSMT;
//		for (int i = sqrts.size() - 1; i >= definedSqrts; --i) {
//			std::string def = sqrts[i].first;
//			std::string pow = sqrts[i].second;
//			extraSMT = "(declare-const sqrt" + std::to_string(i) + " Real)(assert (>= sqrt" + std::to_string(i) + " 0))(assert (= (^ sqrt" + std::to_string(i) + " " + pow + ") " + def + "))" + extraSMT;
//		}
//		definedSqrts = sqrts.size();
//	}
//
//	std::vector<std::string> resNames;
//	for (int i = 0; i < m.m_LineIdentifiers; ++i) {
//		resNames.push_back(m.m_LineDef.m_NumberedVarNames[0].toString() + std::to_string(i));
//	}
//
//	// Check if solution exists
//	return eq.getSolution({ e1.getIdentifiers(), e2.getIdentifiers() }, { e1.getID(), e2.getID() }, resNames, nullptr, nullptr, sqrts, extraSMT);
//	
//}