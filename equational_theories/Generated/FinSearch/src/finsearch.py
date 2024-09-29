import sys
import highspy

from parser import read_eqs, Equation
from finite_magma import enumerate_assignments, FiniteMagma


def get_theorem(N: int, eq1: Equation, eq2: Equation, m: FiniteMagma, assignment):
  assignments = []
  for x in range(m.num_elements):
      for y in range(m.num_elements):
          assignments.append(f"        | {x}, {y} => {m.op(x,y)}")

  newline = "\n"
  ret = f"""
theorem Equation{eq1.equation_number}_not_implies_Equation{eq2.equation_number} : ∃ (G: Type) (_: Magma G), Equation{eq1.equation_number} G ∧ ¬ Equation{eq2.equation_number} G := by
  let G := Fin {N}
  let hG : Magma G := {{
      op := fun x y ↦ match x, y with
{newline.join(assignments)}
  }}
  refine ⟨G, hG, ?eq{eq1.equation_number}, ?neq{eq2.equation_number}⟩
  ·
    intro {' '.join(eq1.free_variables)}
{newline.join(f'    fin_cases {x} <;>' for x in eq1.free_variables)}
    all_goals simp [hG]
  ·
    intro h
    specialize h {' '.join(str(assignment[x]) for x in eq2.free_variables)}
    simp [hG] at h
    try {{ exact Fin.ne_of_val_ne (by decide) h }}
"""
  return ret



def find_counter_example(N: int, eq1: Equation, eq2_list: list[Equation]):
  h = highspy.Highs()
  h.HandleKeyboardInterrupt = True
  #h.setOptionValue("presolve", "off")

  # t_{i,j}^k = 1 <=> i j -> k
  t = {}
  n = range(N)
  for i in n:
      for j in n:
          for k in n:
              t[(i,j,k)] = h.addBinary()
          h.addConstr(sum(t[(i,j,k)] for k in n) == 1)

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
              pass # Always satisfied
      elif not isinstance(lhs, int) and not isinstance(rhs, int):
          for v1, v2 in zip(lhs, rhs):
              h.addConstr(v1==v2)
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
          h.addConstr(v1+v2+neq_var<=2)

  op_result_cache = {}
  def op_result(lhs, rhs, cache_key):
      """Force the result vars to be the result of lhs * rhs"""
      if isinstance(lhs, int) and isinstance(rhs, int):
          return [t[(lhs,rhs,k)] for k in n]
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
                      x = h.addBinary() # x == 1 <=> lhs[i] and rhs[j] and t[i,j,k]
                      h.addConstr(lhs[i] + rhs[j] + t[(i,j,k)] <= 2 + x)
                      h.addConstr(lhs[i] + rhs[j] + t[(i,j,k)] >= 3*x)
                      X.append(x)
              h.addConstr(result[k] == sum(X))
          op_result_cache[cache_key] = result
          return result

  A = enumerate_assignments(N, eq1.free_variables)
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
      print("unsat. nothing to do")
      return False

  eq2_solved_vars = []
  for eq2 in eq2_list:
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

  assert h.maximize(sum(eq2_solved_vars)) == highspy.HighsStatus.kOk
  if h.getModelStatus() == highspy.HighsModelStatus.kInfeasible:
      return False
  have_any_solved = round(h.getObjectiveValue() >= 1)

  solution = [-1]*N**2
  for i in n:
      for j in n:
          for k in n:
              if round(h.val(t[(i,j,k)])) == 1:
                  solution[i+N*j] = k

  m = FiniteMagma(N, solution)
  assert all(eq1.eval(a, m.op) for a in A)

  theorems = {}
  for eq2 in eq2_list:
      for a in enumerate_assignments(N, eq2.free_variables):
          if not eq2.eval(a, m.op):
              theorems[eq2] = get_theorem(N, eq1, eq2, m, a)
              break

  return theorems

def solve(n, lhs, rhs_list):
  theorems = {}
  for N in range(2, n+1):
    while rhs_list:
      new_theorems = find_counter_example(N, lhs, rhs_list)
      if new_theorems:
          rerun = len(new_theorems) < len(rhs_list)
          for eq, t in new_theorems.items():
              theorems[eq] = t
              rhs_list.remove(eq)
          if not rerun:
              break
      else:
          break

  return theorems


def main():
  if len(sys.argv) < 4:
    print(f"Usage: {sys.argv[0]} N lhs rhs [rhs2, ...]")
    sys.exit(1)

  all_eqs = {e.equation_number:e for e in read_eqs()}
  n, lhs = int(sys.argv[1]), all_eqs[int(sys.argv[2])]
  rhs_list = [all_eqs[int(x)] for x in sys.argv[3:]]
  theorems = solve(n, lhs, rhs_list)

  for t in theorems.values():
    print(t)

  print(f"-- Found {len(theorems)}/{len(theorems)+len(rhs_list)} theorems")


if __name__ == "__main__":
    main()
