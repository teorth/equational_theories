#!/usr/bin/env python3

import re
import inspect
import random
import numpy as np
from itertools import product
import sys
sys.path.append("../../FinitePoly/src")
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

tables = list(product([0,1,2], repeat=9))
tables = np.array(tables).reshape((-1, 3, 3))
S = set(range(3))

for table in tables:
    #a, b, c, d, e, f = np.random.randint(0, N, 6)
    #src = f"({a} * x**2 + {b} * y**2 + {c} * x + {d} * y + {e} * x * y) % {N}"
    #op = lambda x, y: (a * x**2 + b * y**2 + c * x + d * y + e * x * y) % N
    src = str(table.tolist())
    op = lambda x, y: table[x][y]

    ok = tuple(doall(S, op))
    if ok not in seen:
        print(repr(src), ok)
    seen[ok] = True


