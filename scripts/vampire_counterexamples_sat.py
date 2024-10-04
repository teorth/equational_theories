import subprocess, json, random
from tqdm import tqdm
import time
from generate_eqs_list import *
import re
from collections import defaultdict

random.seed(17)

with open('remaining.json') as fs:
  problems = json.load(fs)

problems = problems

print(len(problems))

BVARS = 'XYZWUV'

def format_expr2(expr):
    if isinstance(expr, int):
        return BVARS[expr]
    return f'mul({format_expr2(expr[0])}, {format_expr2(expr[1])})'

def format_eq(eq):
  v = ''
  for i in BVARS[:count_vars(eq)]:
    v += f'! [{i}] : '
  return f'{v}{format_expr2(eq[0])} = {format_expr2(eq[1])}'


def encode_problem(problem):
  assumption, goal = eqs[int(problem['lhs'].split('n')[1]) - 1], eqs[int(problem['rhs'].split('n')[1]) - 1]
  if format_expr2(assumption[0]) in format_expr2(assumption[1]): return None
  # assert format_expr2(assumption[0]) in format_expr2(assumption[1]), (assumption)
  return f'fof(lhs, axiom, {format_eq(assumption)}).\nfof(rhs, conjecture, {format_eq(goal)}).\n'

def build_model(output):
  model = defaultdict(dict)
  for a, b, c in re.findall(r'mul\(\'([$\w]+)\',\'([$\w]+)\'\) = \'([$\w]+)\'', output):
    model[a][b] = c
  if len(model) == 0:
    print(output)
    exit(1)
  return model

def table(model : dict):
  vals = list(model.keys())
  return [[vals.index(model[a][b]) for b in vals] for a in vals]

# disproofs = open('equational_theories/Generated/Vampire/Disproofs.lean', 'a')
remaining = []

for problem in tqdm(problems):
  pr = encode_problem(problem)
  if pr is None:
    continue
  start_time = time.perf_counter()
  try:
    out = subprocess.check_output(['/home/commandmaster/Downloads/vampire',
                                  '/proc/self/fd/0', '-t', '1'], input=pr.encode()).decode()
  except Exception:
    remaining.append(problem)
    continue
    # try:
    #   print('Interesting')
    #   print(pr)
    #   out = subprocess.check_output(['/home/commandmaster/Downloads/vampire',
    #                                 '/proc/self/fd/0', '-t', '1'], input=pr.encode()).decode()
    # except Exception:
    #   print('Error with', problem)
    #   continue
  # assert 'Termination reason: Satisfiable' in out
  print(pr)
  print(out)
  exit(1)
  # model = build_model(out)
  # print('@[equational_result]', file=disproofs)
  # print(f'theorem {problem["lhs"]}_not_implies_{problem["rhs"]} : ∃ (G: Type) (_: Magma G), '
  #       f'{problem["lhs"]} G ∧ ¬ {problem["rhs"]} G :=', file=disproofs)
  # print(f'  ⟨Fin {len(model)}, ⟨memoFinOp fun x y => {table(model)}[x.val]![y.val]!⟩, by decideFin!⟩', file=disproofs)
  # print(file=disproofs)
  # print(model)

# json.dump(remaining, open('remaining.json', 'w'))
