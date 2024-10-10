import json, random

f = open(f'equational_theories/Generated/VampireProven/Conjectures.lean', 'w')

print('import equational_theories.Equations.All', file=f)
print('import equational_theories.Magma', file=f)
print('import Mathlib.Tactic.TypeStar', file=f)

for line in open('conjectures.txt'):
  lhs, rhs = map(int, line.strip(' \n()').split(','))
  print(f'@[equational_result] conjecture Equation{lhs+1}_not_implies_Equation{rhs+1} : ∃ (G: Type) (_: Magma G), Equation{lhs+1} G ∧ ¬ Equation{rhs+1} G', file=f)

f.close()
