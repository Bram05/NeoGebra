#include "Point.h"

#include "z3++.h"

Point::Point(int x1, int y1) : m_X{ x1 }, m_Y{ y1 } {
    std::cout << "de-Morgan example\n";

    z3::context c;

    z3::expr x = c.bool_const("x");
    z3::expr y = c.bool_const("y");
    z3::expr conjecture = (!(x && y)) == (!x || !y);

    z3::solver s(c);
    // adding the negation of the conjecture as a constraint.
    s.add(!conjecture);
    std::cout << s << "\n";
    std::cout << s.to_smt2() << "\n";
    switch (s.check()) {
    case z3::unsat:   std::cout << "de-Morgan is valid\n"; break;
    case z3::sat:     std::cout << "de-Morgan is not valid\n"; break;
    case z3::unknown: std::cout << "unknown\n"; break;
    }
}

int Point::getX() {
	return m_X;
}

int Point::getY() {
	return m_Y;
}