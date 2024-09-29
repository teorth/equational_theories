# This scripts allows one, given a left_eqn and a right_eqn,
# to generate a lean file wich validates a Z3 counterexample.
# This script requires Z3 and, for now, entering the left and
# right equations and their "theorem numbers" by hand.

M = DeclareSort('M')

x = Const('x', M)
y = Const('y', M)
z = Const('z', M)
w = Const('w', M)
t = Const('t', M)
u = Const('u', M)

m = Function('m', M, M, M)

left_eqn = m(x, m(x, y)) == m(x, m(y, x))

right_eqn = m(x, m(y, z)) == m(x, m(z, y))

left = 4283

right = 4358

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

goal = mk_goal(left_eqn, right_eqn)

def prove(f):
    s = Solver()
    s.add(Not(f))
    res = s.check()
    if res == sat:
        # print ("found countermodel")
        model = s.model()
        # print (model)
        return model
    elif res == unsat:
        # print ("proved")
        return None
    else:
        # print ("found neither proof nor countermodel")
        # print (res)
        return None

def get_elts(model: ModelRef):
    m_type = model.get_universe(M)
    m_dict = {}
    for v in m_type:
        m_dict[v] = str(v).replace('!', '_')
    return m_dict

def get_val(model: ModelRef, f, a, b):
    return model.evaluate(f(a, b))

mod = prove(goal)
univ = get_elts(mod)

def print_incs():
    return ("import equational_theories.Magma\n"
            "import equational_theories.AllEquations\n"
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
    univ = get_elts(mod)
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
    return ("theorem Equation{left}_not_implies_Equation{right} :  "
            "∃ (G: Type) (_: Magma G), Equation{left} G ∧ ¬ Equation{right} G :=\n"
            "by exists M, M.Magma\n\n".format(left = left, right = right))

#for now we assume goal is set
def print_file():
    model = prove(goal)
    univ = get_elts(model)
    s = ""
    s = "-- This countermodel was automatically generated using Z3.\n"
    s += print_incs()
    s += print_ind(univ)
    s += print_fun(mod)
    s += print_instance()
    s += print_non_imp_proof(left, right)
    return s
