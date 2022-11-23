#include "Z3Tools.h"

bool verifyString(std::string str) {
	z3::context c;
	z3::solver s(c);

	Z3_ast_vector cond_vector = Z3_parse_smtlib2_string(c, str.c_str(), 0, 0, 0, 0, 0, 0); //, 1, & declName, & decl);

	for (int i{}; i < Z3_ast_vector_size(c, cond_vector); ++i) {
		s.add(z3::expr(c, Z3_ast_vector_get(c, cond_vector, i)));
	}

	//std::cout << s << "\n\nsmt2:\n";
	//std::cout << s.to_smt2() << "\n";

	if (s.check() == z3::sat) {
		//std::cout << "solution:\n" << s.get_model() << std::endl;
		return true;
	}
	else {
		return false;
	}
}