import json, random

uid = random.randint(1, 100000)

f = open(f'equational_theories/Generated/Vampire/Vampire_conjecture_{uid}.lean', 'w')

of = open('equational_theories/Generated/Vampire.lean', 'a')
print(f'import equational_theories.Generated.Vampire.Vampire_conjecture_{uid}', file=of)
of.close()

print('import equational_theories.AllEquations', file=f)
print('import equational_theories.Magma', file=f)
print('import Mathlib.Tactic.TypeStar', file=f)

size = 0

for eq, _ in json.load(open('proven.json')):
  size += 1
  if size == 5000:
    f.close()
    uid = random.randint(1, 100000)
    f = open(f'equational_theories/Generated/Vampire/Vampire_conjecture_{uid}.lean', 'w')
    of = open('equational_theories/Generated/Vampire.lean', 'a')
    print(f'import equational_theories.Generated.Vampire.Vampire_conjecture_{uid}', file=of)
    of.close()
    print('import equational_theories.AllEquations', file=f)
    print('import equational_theories.Magma', file=f)
    print('import Mathlib.Tactic.TypeStar', file=f)
    size = 0
  print(f'@[equational_result] conjecture {eq["lhs"]}_implies_{eq["rhs"]} (G: Type*) [Magma G] (_: {eq["lhs"]} G) : {eq["rhs"]} G', file=f)


for eq, _ in json.load(open('disproven.json')):
  size += 1
  if size == 5000:
    f.close()
    uid = random.randint(1, 100000)
    f = open(f'equational_theories/Generated/Vampire/Vampire_conjecture_{uid}.lean', 'w')
    of = open('equational_theories/Generated/Vampire.lean', 'a')
    print(f'import equational_theories.Generated.Vampire.Vampire_conjecture_{uid}', file=of)
    of.close()
    print('import equational_theories.AllEquations', file=f)
    print('import equational_theories.Magma', file=f)
    print('import Mathlib.Tactic.TypeStar', file=f)
    size = 0
  print(f'@[equational_result] conjecture {eq["lhs"]}_not_implies_{eq["rhs"]} : ∃ (G: Type) (_: Magma G), {eq["lhs"]} G ∧ ¬ {eq["rhs"]} G', file=f)

f.close()
