#!/usr/bin/env python3

import sys
import highspy
import random

from parser import read_eqs, Equation
from finite_magma import enumerate_assignments, FiniteMagma, Theorem


def find_counter_example(
    N: int, eq1: Equation, eq2_list: list[Equation], debug_output=False
):
    if debug_output:
        print(f"N={N}")
    h = highspy.Highs()
    h.HandleKeyboardInterrupt = True
    h.setOptionValue("presolve", "off")
    h.setOptionValue("time_limit", 60)
    if not debug_output:
        h.setOptionValue("log_to_console", "off")

    # t_{i,j}^k = 1 <=> i j -> k
    t = {}
    n = range(N)
    for i in n:
        for j in n:
            for k in n:
                t[(i, j, k)] = h.addBinary()
            h.addConstr(sum(t[(i, j, k)] for k in n) == 1)

    # For each possible assignment, eq1 must be satisfied
    is_unsat = False

    def add_vars():
        vars = [h.addBinary() for _ in n]
        h.addConstr(sum(vars) == 1)
        return vars

    def add_eq(lhs, rhs):
        nonlocal is_unsat
        """force rhs == lhs"""
        if isinstance(lhs, int) and isinstance(rhs, int):
            if lhs != rhs:
                is_unsat = True
            else:
                pass  # Always satisfied
        elif not isinstance(lhs, int) and not isinstance(rhs, int):
            for v1, v2 in zip(lhs, rhs):
                h.addConstr(v1 == v2)
        else:
            fixed = lhs if isinstance(lhs, int) else rhs
            vars = rhs if isinstance(lhs, int) else lhs
            for i, v in enumerate(vars):
                if i == fixed:
                    h.addConstr(v == 1)
                else:
                    h.addConstr(v == 0)

    def add_neq(neq_var, lhs, rhs):
        """force rhs != lhs if neq_var=1"""
        if isinstance(rhs, int):
            rhs = [1 if i == rhs else 0 for i in n]
        if isinstance(lhs, int):
            lhs = [1 if i == lhs else 0 for i in n]
        for v1, v2 in zip(lhs, rhs):
            h.addConstr(v1 + v2 + neq_var <= 2)

    op_result_cache = {}

    def op_result(lhs, rhs, cache_key):
        """Force the result vars to be the result of lhs * rhs"""
        if isinstance(lhs, int) and isinstance(rhs, int):
            return [t[(lhs, rhs, k)] for k in n]
        else:
            if cache_key in op_result_cache:
                return op_result_cache[cache_key]

            result = add_vars()
            if isinstance(rhs, int):
                rhs = [1 if i == rhs else 0 for i in n]
            if isinstance(lhs, int):
                lhs = [1 if i == lhs else 0 for i in n]
            for k in n:
                X = []
                for i in n:
                    for j in n:
                        x = h.addBinary()  # x == 1 <=> lhs[i] and rhs[j] and t[i,j,k]
                        h.addConstr(lhs[i] + rhs[j] + t[(i, j, k)] <= 2 + x)
                        h.addConstr(lhs[i] + rhs[j] + t[(i, j, k)] >= 3 * x)
                        X.append(x)
                h.addConstr(result[k] == sum(X))
            op_result_cache[cache_key] = result
            return result

    A = list(enumerate_assignments(N, eq1.free_variables))
    if debug_output:
        print(f"Adding eq1: {eq1}")

    for a in A:

        def eval(node):
            if node.is_op:
                v = op_result(eval(node.left), eval(node.right), eval_print(node))
                return v
            else:
                return a[node.value]

        def eval_print(node):
            if node.is_op:
                return f"({eval_print(node.left)} * {eval_print(node.right)})"
            else:
                return a[node.value]

        add_eq(eval(eq1.lhs), eval(eq1.rhs))

    if is_unsat:
        if debug_output:
            print("unsat. nothing to do")
        return None

    eq2_solved_vars = []
    for eq2 in eq2_list:
        if debug_output:
            print(f"Adding eq2: {eq2}")
        eq2_solved_var = h.addBinary()
        eq2_solved_vars.append(eq2_solved_var)
        assignment_satisfied_vars = []
        for a in enumerate_assignments(N, eq2.free_variables):
            assignment_not_satisfied_var = h.addBinary()
            assignment_satisfied_vars.append(assignment_not_satisfied_var)

            def eval(node):
                if node.is_op:
                    v = op_result(eval(node.left), eval(node.right), eval_print(node))
                    return v
                else:
                    return a[node.value]

            def eval_print(node):
                if node.is_op:
                    return f"({eval_print(node.left)} * {eval_print(node.right)})"
                else:
                    return a[node.value]

            add_neq(assignment_not_satisfied_var, eval(eq2.lhs), eval(eq2.rhs))
        h.addConstr(eq2_solved_var <= sum(assignment_satisfied_vars))

    if eq2_list:
        h.maximize(sum(eq2_solved_vars))
    else:
        h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    if debug_output:
        print(h.getModelStatus())

    solution = [-1] * N**2
    for i in n:
        for j in n:
            for k in n:
                if round(h.val(t[(i, j, k)])) == 1:
                    solution[i + N * j] = k

    m = FiniteMagma(N, solution)
    assert all(eq1.eval(a, m.op) for a in A)

    solved = []
    for eq2 in eq2_list:
        for a in enumerate_assignments(N, eq2.free_variables):
            if not eq2.eval(a, m.op):
                solved.append(eq2)
                break

    if not eq2_list:
        return m
    elif solved:
        return Theorem(m, [eq1], solved)
    else:
        return None


def solve(n, lhs, rhs_list, n_min=2, debug_output=False) -> list[Theorem]:
    theorems = []
    for N in range(n_min, n + 1):
        while rhs_list:
            theorem = find_counter_example(N, lhs, rhs_list, debug_output=debug_output)
            if theorem:
                rerun = len(theorem.unsat) < len(rhs_list)
                theorems.append(theorem)
                rhs_list = [x for x in rhs_list if x not in theorem.unsat]
                if not rerun:
                    break
            else:
                break

    return theorems


def search_satisfying_magma(eq, n_min, n_max, debug_output=False):
    for n in range(n_min, n_max + 1):
        m = find_counter_example(n, eq, [], debug_output=debug_output)
        if m:
            return m
    return None


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} N lhs [rhs1, rhs2, ...]")
        sys.exit(1)

    search_all = "--search-all" in sys.argv
    if search_all:
        sys.argv.remove("--search-all")

    all_eqs = {e.equation_number: e for e in read_eqs()}
    n, lhs = int(sys.argv[1]), all_eqs[int(sys.argv[2])]
    rhs_list = [all_eqs[int(x)] for x in sys.argv[3:]]
    if rhs_list:
        theorems = solve(n, lhs, rhs_list)
        for t in theorems:
            print(t.magma.to_data(all_eqs.values()))
    elif search_all:
        magma = search_satisfying_magma(lhs, n, n)
        if not magma:
            print("-- none found")
        else:
            print(magma.to_data(all_eqs.values()))
            todo = [
                eq
                for eq in all_eqs.values()
                if magma.proves(eq) and eq.equation_number != lhs.equation_number
            ]
            while todo:
                rhs = random.choice(todo)
                print(f"--todo: {len(todo)}, searching for counter example to {rhs}")
                theorems = solve(n, lhs, [rhs])
                if theorems:
                    magma = theorems[0].magma
                    print(magma.to_data(all_eqs.values()))
                    todo = [eq for eq in todo if magma.proves(eq)]
                else:
                    print("-- none found")
                    todo.remove(rhs)
    else:
        magma = search_satisfying_magma(lhs, n, n)
        if magma:
            print(magma.to_data(all_eqs.values()))
        else:
            print("-- none found")


if __name__ == "__main__":
    main()
