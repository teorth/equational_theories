#!/usr/bin/env python3

# This scripts allows one, given a left_eqn and a right_eqn, to
# generate a lean file which validates a Z3 counterexample.  This
# script requires the Z3 python bindings and passing in the equation
# numbers on the command line. It depends on the `generate_eqs_list`
# script.

from generate_eqs_list import *
from z3 import *
import sys

big_eqn_list = eqs

M = DeclareSort('M')

x = Const('x', M)
y = Const('y', M)
z = Const('z', M)
w = Const('w', M)
u = Const('u', M)
v = Const('v', M)

m = Function('m', M, M, M)

left = 4283

right = 4358

def tup_to_term(tup):
    if isinstance(tup, int):
        return Const(VAR_NAMES[tup], M)
    elif isinstance(tup, tuple):
        assert len(tup) == 2
        return m(tup_to_term(tup[0]), tup_to_term(tup[1]))
    else:
        raise ValueError("Expected an int or a tuple")

def eqn_to_z3(tup):
    left = tup[0]
    right = tup[1]
    return tup_to_term(left) == tup_to_term(right)

def get_vars(t: ExprRef):
    all_vars = set()
    if is_const(t):
        all_vars.add(t)
    else:
        for u in t.children():
            all_vars = all_vars.union(get_vars(u))
    return all_vars

def Univ(t: ExprRef):
    return ForAll(list(get_vars(t)), t)

def mk_goal(lhs, rhs):
    return Implies(Univ(lhs), Univ(rhs))

def prove(f):
    s = Solver()
    s.add(Not(f))
    res = s.check()
    if res == sat:
        model = s.model()
        return model
    elif res == unsat:
        return True
    else:
        return None

def get_elts(model: ModelRef):
    m_type = model.get_universe(M)
    m_dict = {}
    for v in m_type:
        m_dict[v] = str(v).replace('!', '_')
    return m_dict

def get_val(model: ModelRef, f, a, b):
    return model.evaluate(f(a, b))

def print_incs():
    return ("import equational_theories.Magma\n"
            "import equational_theories.Equations.All\n"
            "import Mathlib.Data.Fintype.Basic\n"
            "import Mathlib.Tactic.DeriveFintype\n\n")

def print_ind_dec():
    return "inductive M :=\n"

def print_ind_ctr(d: dict):
    s = ""
    for k in d:
        s += "| {}\n".format(d[k])
    return s

def print_derives():
    return "deriving DecidableEq, Fintype\n"

def print_ind(model: ModelRef):
    print(model)
    univ = get_elts(model)
    s = ""
    s += print_ind_dec()
    s += print_ind_ctr(univ)
    s += print_derives()
    s += "\n"
    return s

def print_fun_decl():
    return "def m (x y : M) : M :=\n"

# inspired by an example at https://ericpony.github.io/z3py-tutorial/guide-examples.htm
def print_cases(model: ModelRef, f: FuncDeclRef, univ: dict):
    s = ""
    for x in univ:
        for y in univ:
            s += "| M.{}, M.{} => M.{}\n".format(
                univ[x],
                univ[y],
                univ[model.evaluate(m(x, y))])
    return s

def print_match(model: ModelRef):
    s = "match x, y with\n"
    return s + print_cases(model, m, get_elts(model))

def print_fun(model: ModelRef):
    s = ""
    s += print_fun_decl()
    s += print_match(model)
    s += "\n"
    return s

def print_instance():
    return "instance M.Magma : Magma M := ⟨ m ⟩\n\n"


def print_non_imp_proof(left: int, right: int):
    return ("@[equational_result]\ntheorem Equation{left}_not_implies_Equation{right} :  "
            "∃ (G: Type) (_: Magma G), Equation{left} G ∧ ¬ Equation{right} G :=\n"
            "by exists M, M.Magma\n\n".format(left = left, right = right))

def pretty_eqn(tup):
    return "{} = {}".format(format_expr(tup[0]), format_expr(tup[1]))

def print_file(left, right):
    tup_l = big_eqn_list[left-1]
    tup_r = big_eqn_list[right-1]
    l = eqn_to_z3(tup_l)
    r = eqn_to_z3(tup_r)
    goal = mk_goal(l, r)
    model = prove(goal)
    s = ""
    if model == True:
        s += "For {} -> {}\n".format(pretty_eqn(tup_l), pretty_eqn(tup_r))
        s += "No countermodel was generated because the implication is true!"
        return s
    elif model == None:
        s += "For {} -> {}\n".format(pretty_eqn(tup_l), pretty_eqn(tup_r))
        s += "No countermodel was generated because the implication could not be refuted by Z3."
        return s
    else:
        s += "-- This countermodel was automatically generated using Z3.\n"
        s += "-- It refutes {} -> {}\n".format(pretty_eqn(tup_l), pretty_eqn(tup_r))
        s += print_incs()
        s += print_ind(model)
        s += print_fun(model)
        s += print_instance()
        s += print_non_imp_proof(left, right)
        return s

if __name__ == "__main__":
    print(print_file(int(sys.argv[1]), int(sys.argv[2])))
