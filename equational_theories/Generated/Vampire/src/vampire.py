# Use the vampire solver to solve implications without proof
# Use as lake exe extract_implications unknowns equational_theories > out.json; python vampire.py

import subprocess, json, random
from tqdm import tqdm
import time
from generate_eqs_list import *

random.seed(17)

with open('out.json') as fs:
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
  return f'fof(lhs, axiom, {format_eq(assumption)}).\nfof(rhs, conjecture, {format_eq(goal)}).\n'

count_proven = 0
proven = []
count_disproven = 0
disproven = []
count_unsolved = 0

for problem in tqdm(problems):
  pr = encode_problem(problem)

  try:
    start_time = time.perf_counter()
    out = subprocess.check_output(['~/Downloads/vampire',
                                    '/proc/self/fd/0', '-t', '0.5'], input=pr.encode()).decode()
    # print(out)
    dur = time.perf_counter() - start_time
    if 'Termination reason: Satisfiable' in out:
      count_disproven += 1
      if 'outcome' in problem:
         assert problem['outcome'] == 'unknown' or 'false' in problem['outcome']
      disproven.append([problem, f'inter {dur}'])
    elif 'Termination reason: Refutation' in out:
      if 'outcome' in problem:
         assert problem['outcome'] == 'unknown' or 'true' in problem['outcome']
      count_proven += 1
      proven.append([problem, dur])
    else:
       print("Anomaly!!")
       print(out)
  except subprocess.CalledProcessError as e:
    assert e.returncode == 1
    count_unsolved += 1

print('Unsolved', count_unsolved)
print('Proven', count_proven)
print('Disproven', count_disproven)
# print(proven)
json.dump(proven, open('./proven.json', 'w'))
json.dump(disproven, open('./disproven.json', 'w'))
