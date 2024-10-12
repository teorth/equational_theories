#!/usr/bin/env python3

import sympy

from parser import Equation

def non_commutative_sympify(expr_string):
    parsed_expr = sympy.parsing.sympy_parser.parse_expr(
        expr_string,
        evaluate=False
    ).expand()

    new_locals = {sym.name:sympy.Symbol(sym.name, commutative=False)
                  for sym in parsed_expr.atoms(sympy.Symbol)}

    ex = sympy.sympify(expr_string, locals=new_locals)
    coeffs = [ex.expand().coeff(v) for k,v in new_locals.items() if k not in ('a', 'b')] if ex != 0 else []
    return ex, ex.expand(), coeffs

def linear_subs(eq):
    # Replace (x ◇ z) with a*x + b*y
    parts = []
    for expr in (eq.lhs, eq.rhs):
        def print_sub_expr(subex):
            if subex.left and subex.right:
                return f"(a*{print_sub_expr(subex.left)} + b*{print_sub_expr(subex.right)})"
            elif not subex.left and not subex.right:
                return subex.value
            else:
                assert False
        parts.append(print_sub_expr(expr))
    eq_str = f"{parts[1]} -({parts[0]})"
    return eq_str, non_commutative_sympify(eq_str)

with open("data/equations.txt") as f:
    with open("data/linear_magma_restrictions.txt", "w") as out:
        eqs = {}
        for i, line in enumerate(f):
            line = line.strip()
            if not line:
                continue
            eqs[i+1] = linear_subs(Equation(line))
            print(f"{i+1} {line} | {eqs[i+1]}")
            out.write(f"{i+1} {eqs[i+1][-1][-1]}\n")
