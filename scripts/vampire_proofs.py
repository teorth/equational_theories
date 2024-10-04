import subprocess, json, random
from tqdm import tqdm
import time
from generate_eqs_list import *
import re
from collections import defaultdict

random.seed(17)

with open('conjectures.json') as fs:
  problems = json.load(fs)

problems = problems['implications']

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

for problem in tqdm(problems):
  pr = encode_problem(problem)

  start_time = time.perf_counter()
  print(pr)
  out = subprocess.check_output(['/home/commandmaster/Downloads/vampire', '--latex_output', 'on',
                                 '--proof_extra', 'full',
                                '/proc/self/fd/0', '-t', '1'], input=pr.encode()).decode()
  print(out)
  exit(1)

json.dump(remaining, open('remaining.json', 'w'))
