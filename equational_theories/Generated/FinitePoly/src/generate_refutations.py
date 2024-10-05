import re
import inspect
import random
import numpy as np
from itertools import product
from utils import get_fns

fns = get_fns()

def check_rule(nvar, check, S, op):
    for args in product(S, repeat=nvar):
        if not check(op, *args):
            return False
    return True

def doall(S, op):
    ok = []
    for i,(eqn, nvar, fn) in enumerate(fns):
        if check_rule(nvar, fn, S, op):
            ok.append(i)
    return ok


rules = {}

seen = {}

while True:
    N = random.randint(2, 12)
    S = set(range(N))
    a, b, c, d, e, f = np.random.randint(0, N, 6)
    src = f"({a} * x**2 + {b} * y**2 + {c} * x + {d} * y + {e} * x * y) % {N}"
    op = lambda x, y: (a * x**2 + b * y**2 + c * x + d * y + e * x * y) % N

    ok = tuple(doall(S, op))
    if ok not in seen:
        print(repr(src), ok)
    seen[ok] = True


