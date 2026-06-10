import re
import sys
from generate_eqs_list import *

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

def encode(h, goal):
  h_eq, goal_eq = eqs[h - 1], eqs[goal - 1]
  return f'%---- TPTP for equational_theories {h} => {goal}\nfof(lhs, axiom, {format_eq(h_eq)}).\nfof(rhs, conjecture, {format_eq(goal_eq)}).\n'

def main():
  if len(sys.argv) >= 3:
    print(encode(int(sys.argv[1]), int(sys.argv[2])))
  else:
    print(f"Provide the hypothesis and goal numbers on the command line to write TPTP to standard output (in any format), or provide them one per line on standard input to write TPTP to an <h>_<goal>.tptp file", file=sys.stderr)
    pattern = re.compile(r'^\D*(\d+)\D+(\d+)\D*$')

    for line in sys.stdin:
        match = pattern.match(line)
        if match:
            h, goal = match.groups()
            problem = encode(int(h), int(goal))

            filename = f"{h}_{goal}.tptp"
            with open(filename, 'w') as f:
                f.write(problem)

            print(f"Wrote {h} => {goal} to {filename}", file=sys.stderr)

if __name__ == "__main__":
    main()
