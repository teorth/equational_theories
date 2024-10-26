#!/usr/bin/env python3

import argparse
import itertools
import json
import os, io
import re
import subprocess
import sys
import time
from collections import defaultdict, Counter
from subprocess import CalledProcessError
from typing import Tuple, List

import networkx as nx

from generate_eqs_list import eqs


def pos_powerset(iterable):
    "powerset([1,2,3]) --> (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(s, r) for r in range(1, len(s) + 1)
    )


def tptp_single(op, data):
    if len(data) == 2:
        return f"{data[0]} = {data[1]}"
    else:
        return f"{op}({data[0]}, {data[1]}, {data[2]})"


def lean_single(op, data):
    if len(data) == 2:
        return f"{data[0]} = {data[1]}"
    else:
        return f"{op} {data[0]} {data[1]} {data[2]}"


def tptp_single_negated(op, data):
    if len(data) == 2:
        return f"{data[0]} != {data[1]}"
    else:
        return f"~{op}({data[0]}, {data[1]}, {data[2]})"


def lean_single_negated(op, data):
    if len(data) == 2:
        return f"{data[0]} ≠ {data[1]}"
    else:
        return f"¬ {op} {data[0]} {data[1]} {data[2]}"


false_rules = set()
true_rules = set()

eq = ()


def format_expr2(expr):
    if isinstance(expr, int):
        return f"X{expr}"
    return f"mul({format_expr2(expr[0])}, {format_expr2(expr[1])})"


def format_eq(eq):
    return f"{format_expr2(eq[0])} = {format_expr2(eq[1])}"


models = []


def parse_model(out):
    model = defaultdict(dict)
    for a, b, c in re.findall(r"mul\(([$\w\']+),([$\w\']+)\) = ([$\w\']+)", out):
        model[a][b] = c
    vals = list(model.keys())
    return [[vals.index(model[a][b]) for b in vals] for a in vals]


failed = 0


class Rule:
    def __init__(self, preconditions, conclusion):
        vars = {}
        for v in preconditions + [conclusion]:
            for a in v:
                if a not in vars:
                    vars[a] = len(vars)
        self.vars = len(vars)
        self.varmap = vars
        self.preconditions = sorted([vars[i] for i in x] for x in preconditions)
        self.conclusion = [vars[i] for i in conclusion]

        self.graph = nx.Graph()
        for v in range(self.vars):
            self.graph.add_node(f"var{v}", type=0)
        for i, pc in enumerate(self.preconditions):
            self.graph.add_node(f"pc{i}", type=1)
            for j, v in enumerate(pc):
                self.graph.add_edge(f"pc{i}", f"var{v}")
                self.graph[f"pc{i}"][f"var{v}"]["ind"] = self.graph[f"pc{i}"][
                    f"var{v}"
                ].get("ind", 0) | (1 << j)
        self.graph.add_node("conclusion", type=2)
        for j, v in enumerate(self.conclusion):
            self.graph.add_edge("conclusion", f"var{v}")
            if len(self.conclusion) == 3:
                self.graph["conclusion"][f"var{v}"]["ind"] = self.graph["conclusion"][
                    f"var{v}"
                ].get("ind", 0) | (1 << j)
            else:
                self.graph["conclusion"][f"var{v}"]["ind"] = 1
        self.ghash = nx.weisfeiler_lehman_graph_hash(
            self.graph, node_attr="type", edge_attr="ind"
        )

    def __eq__(self, other):
        return nx.is_isomorphic(
            self.graph,
            other.graph,
            node_match=nx.isomorphism.categorical_node_match("type", -1),
            edge_match=nx.isomorphism.categorical_edge_match("ind", -1),
        )

    def __hash__(self):
        return hash(self.ghash)

    def check(self):
        global failed
        for model in models:
            if not self.check_model(model):
                print("Quickly ruled out")
                return False
        tptp_r = f"fof(eq, axiom, {format_eq(eq)}).\n"
        for i, (a, b, c) in enumerate(self.preconditions):
            tptp_r += f"fof(pc_{i}, axiom, mul(sk{a}, sk{b}) = sk{c}).\n"
        if len(self.conclusion) == 2:
            tptp_r += f"fof(test, conjecture, sk{self.conclusion[0]} = sk{self.conclusion[1]}).\n"
        else:
            tptp_r += f"fof(test, conjecture, mul(sk{self.conclusion[0]}, sk{self.conclusion[1]}) = sk{self.conclusion[2]}).\n"
        try:
            st = time.perf_counter()
            out = subprocess.check_output(
                ["~/Downloads/vampire", "-t", "2", "/proc/self/fd/0"],
                input=tptp_r.encode(),
            ).decode()
            if "Termination reason: Refutation" in out:
                print(f"Confirmed in {time.perf_counter() - st:.3}s")
                return True
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            pass
        if failed > 20:
            return False
        try:
            print("Looking for counterexample")
            out = subprocess.check_output(
                [
                    "~/Downloads/vampire",
                    "-sa",
                    "fmb",
                    "-t",
                    "1",
                    "/proc/self/fd/0",
                ],
                input=tptp_r.encode(),
            ).decode()
            models.append(parse_model(out))
            print("Found counterexample")
            with open(f"data/forcing_rules/{eqid}.models", "w") as f:
                json.dump(models, f)
            return False
        except subprocess.CalledProcessError as e:
            print("Couldn't find counterexample", self)
            failed += 1
            return False

    def generalizations(self):
        for i in range(len(self.preconditions)):
            yield Rule(
                self.preconditions[:i] + self.preconditions[i + 1 :], self.conclusion
            )
        inds = defaultdict(list)
        for i, pc in enumerate(self.preconditions):
            for j, v in enumerate(pc):
                inds[v].append((i, j))
        for j, v in enumerate(self.conclusion):
            inds[v].append((-1, j))
        for v, hv in inds.items():
            for nv in pos_powerset(hv[1:]):
                npc = [x[:] for x in self.preconditions]
                ncon = self.conclusion[:]
                for i, j in nv:
                    if i == -1:
                        ncon[j] = self.vars
                    else:
                        npc[i][j] = self.vars
                yield Rule(npc, ncon)

    def minimize(self):
        print("Minimizing", self)
        # assert self.check()
        all_false = True
        for nr in self.generalizations():
            if nr in true_rules:
                all_false = False
                continue
            if nr in false_rules:
                continue
            if nr.check():
                true_rules.add(nr)
                return nr.minimize()
            else:
                false_rules.add(nr)
        if not all_false:
            print("Weird!!!", self)
        print("Found", self)
        return self

    def dualize(self):
        nc = (
            self.conclusion
            if len(self.conclusion) == 2
            else (self.conclusion[1], self.conclusion[0], self.conclusion[2])
        )
        return Rule([(b, a, c) for a, b, c in self.preconditions], nc)

    def to_tptp(self, op):
        return (
            f'(! [{", ".join(f"X{i}" for i in range(self.vars))}] : '
            f'({" | ".join(map(lambda x: tptp_single_negated(op, [f"X{a}" for a in x]), self.preconditions))} | '
            f'{tptp_single(op, [f"X{a}" for a in self.conclusion])}))'
        )

    def to_lean_no_binders(self, op):
        return (
            f'{" ∨ ".join(map(lambda x: lean_single_negated(op, [f"X{a}" for a in x]), self.preconditions))} ∨ '
            f'{lean_single(op, [f"X{a}" for a in self.conclusion])}'
        )

    def to_lean(self, op):
        return (
            f'(∀ {" ".join(f"X{i}" for i in range(self.vars))}, '
            + self.to_lean_no_binders(op)
            + ")"
        )

    def to_lean_max(self):
        subjs = [f"(Nat.pair X{a} X{b})" for a, b, c in self.preconditions] + [
            f"(Nat.pair X{self.conclusion[0]} X{self.conclusion[1]})"
        ]
        return "max " + " (max ".join(subjs) + " 0" + ")" * (len(subjs) - 1)

    def to_fun_app(self, op):
        names = [None] * self.vars
        for a, b in self.varmap.items():
            if isinstance(a, int):
                names[b] = f"X{a}"
        while None in names:
            for a, b, c in self.preconditions:
                if names[c] is None and names[a] is not None and names[b] is not None:
                    names[c] = f"({op} {names[a]} {names[b]})"
        print(self, self.varmap, names)
        return " ".join(names)

    def to_tptp_negated(self, op):
        return [tptp_single(op, [f"sk{a}" for a in x]) for x in self.preconditions] + [
            tptp_single_negated(op, [f"sk{a}" for a in self.conclusion])
        ]

    def to_latex(self):
        varnames = ["x", "y", "z", "w", "u", "v", "x'", "y'", "z'"]
        word = (
            r" \wedge ".join(
                f"R({varnames[a]}, {varnames[b]}, {varnames[c]})"
                for a, b, c in self.preconditions
            )
            + " \\to "
        )
        if len(self.conclusion) == 2:
            word += f"{varnames[self.conclusion[0]]} = {varnames[self.conclusion[1]]}"
        else:
            word += f"R({varnames[self.conclusion[0]]},{varnames[self.conclusion[1]]},{varnames[self.conclusion[2]]})"
        return word

    def to_defs(self):
        if len(self.conclusion) == 2:
            return
        for eq_c in pos_powerset(self.conclusion):
            goals = []
            good = True
            aeqb = False
            varass = {}
            for v in eq_c:
                varass[v] = "c"
            for l, r, g in self.preconditions:
                if l in eq_c or r in eq_c:
                    good = False
                    break
                if g in eq_c:
                    if l in varass and varass[l] == "b":
                        aeqb = True
                    varass[l] = "a"
                    if r in varass and varass[r] == "a":
                        aeqb = True
                    varass[r] = "b"
            if not good:
                continue
            if aeqb:
                goals.append(["a", "b"])
            for varname, varval in zip("XYZ", self.conclusion):
                if varval in varass:
                    goals.append([varass[varval], varname])
                else:
                    varass[varval] = varname
            for pc in self.preconditions:
                if pc[2] in eq_c:
                    continue
                for a in pc:
                    if a not in varass:
                        varass[a] = f"X{a}"
                goals.append([varass[a] for a in pc])
            rvars = [i for i in varass.values() if i not in "abcXYZ"]
            yield rvars, goals

    def __repr__(self):
        return f"Rule({self.preconditions!r}, {self.conclusion!r})"

    def __str__(self):
        return repr(self)

    def find_var_assignemnts(self) -> Tuple[List[int], List[Tuple[int, int, int]]]:
        nvars = []
        then = []
        unassigned = set(range(self.vars))
        while unassigned:
            cnt = Counter()
            found = False
            for a, b, c in self.preconditions:
                if a not in unassigned and b not in unassigned and c in unassigned:
                    then.append((a, b, c))
                    unassigned.remove(c)
                    found = True
                    break
                cnt[a] += 1
                if a != b:
                    cnt[b] += 1
                cnt[c] -= 2
            if found:
                continue
            chosen = max(unassigned, key=lambda x: cnt[x])
            nvars.append(chosen)
            unassigned.remove(chosen)

        return nvars, then

    def precond(self, assn, mulm):
        for a, b, c in self.preconditions:
            if (assn[a], assn[b]) not in mulm or mulm[(assn[a], assn[b])] != assn[c]:
                return False
        return True

    def conc(self, assn, mulm):
        if len(self.conclusion) == 2:
            return assn[self.conclusion[0]], assn[self.conclusion[1]]
        else:
            assert len(self.conclusion) == 3
            if (assn[self.conclusion[0]], assn[self.conclusion[1]]) in mulm:
                return (
                    mulm[(assn[self.conclusion[0]], assn[self.conclusion[1]])],
                    assn[self.conclusion[2]],
                )
            else:
                return (
                    assn[self.conclusion[0]],
                    assn[self.conclusion[1]],
                    assn[self.conclusion[2]],
                )

    def precond2(self, assn, model):
        for a, b, c in self.preconditions:
            if model[assn[a]][assn[b]] != assn[c]:
                return False
        return True

    def conc2(self, assn, model):
        if len(self.conclusion) == 2:
            return assn[self.conclusion[0]] == assn[self.conclusion[1]]
        else:
            return (
                model[assn[self.conclusion[0]]][assn[self.conclusion[1]]]
                == assn[self.conclusion[2]]
            )

    def check_model(self, model):
        nvars, then = self.find_var_assignemnts()
        for assignment in itertools.islice(
            itertools.product(range(len(model)), repeat=len(nvars)), 2 * 10**5
        ):
            nassignment = [0] * self.vars
            for i, j in enumerate(nvars):
                nassignment[j] = assignment[i]
            for a, b, c in then:
                nassignment[c] = model[nassignment[a]][nassignment[b]]

            if self.precond2(nassignment, model) and not self.conc2(nassignment, model):
                return False
        return True


def flatten_eq(eq, ecache, preconds, predetermined):
    if eq in ecache:
        return ecache[eq]
    if isinstance(eq, int):
        return eq
    l, r = eq
    l = flatten_eq(l, ecache, preconds, predetermined)
    r = flatten_eq(r, ecache, preconds, predetermined)
    tv = predetermined.get(eq, f"t{len(preconds)}")
    preconds.append((l, r, tv))
    ecache[eq] = tv
    return tv


def rulify_eq(eq):
    print("Rulifying", eq)
    if not isinstance(eq[1], int):
        preconds = []
        ecache = {}
        l = flatten_eq(eq[0], ecache, preconds, {})
        r = flatten_eq(eq[1], ecache, preconds, {eq[1]: l})
        print("Rulified", eq, preconds)
        yield Rule(preconds[:-1], preconds[-1])
    if not isinstance(eq[0], int):
        preconds = []
        ecache = {}
        r = flatten_eq(eq[1], ecache, preconds, {})
        l = flatten_eq(eq[0], ecache, preconds, {eq[0]: r})
        print("Rulified", eq, preconds)
        yield Rule(preconds[:-1], preconds[-1])


rules = None


def normalize_eq(a, b, aeqb):
    assert a != b
    if a == "c":
        return "a", "ba"[aeqb], b
    elif b == "c":
        return "a", "ba"[aeqb], a
    return a, b


def find_problems(model, aeqb):
    mp = {}
    vars = set()
    for a, b, c in model:
        if (a, b) in mp:
            return normalize_eq(mp[(a, b)], c, aeqb)
        mp[(a, b)] = c
        vars.update((a, b, c))

    for rule in rules:
        nvars, then = rule.find_var_assignemnts()
        for assignment in itertools.product(vars, repeat=len(nvars)):
            nassignment = [0] * rule.vars
            for i, j in enumerate(nvars):
                nassignment[j] = assignment[i]
            for a, b, c in then:
                if (nassignment[a], nassignment[b]) not in mp:
                    continue
                nassignment[c] = mp[(nassignment[a], nassignment[b])]

            if rule.precond(nassignment, mp):
                v = rule.conc(nassignment, mp)
                if v is not None and not (len(v) == 2 and v[0] == v[1]):
                    if len(v) == 2:
                        return normalize_eq(v[0], v[1], aeqb)
                    elif len(v) == 3:
                        return v

    raise RuntimeError(f"Couldn't find problem with model {model}")


def construct_tptp(rules):
    default_rules = """fof(ac, axiom, a != c).
fof(bc, axiom, b != c).
fof(p3, axiom, ! [Z] : ~old(a, b, Z)).
fof(p4XY, axiom, ! [X, Y] : ~old(X, Y, c)).
fof(p4XZ, axiom, ! [X, Z] : ~old(X, c, Z)).
fof(p4YZ, axiom, ! [Y, Z] : ~old(c, Y, Z)).
"""

    if False:  # idempotent
        default_rules += f"fof(aaa, axiom, old(a, a, a)).\n"
        default_rules += f"fof(bbb, axiom, old(b, b, b)).\n"

    for i, rule in enumerate(rules):
        default_rules += f'fof(old_{i}, axiom, {rule.to_tptp("old")}).\n'
    defs = [((), [("X", "Y", "Z")]), ((), [("a", "X"), ("b", "Y"), ("c", "Z")])] + [
        y for x in rules for y in x.to_defs()
    ]
    skolem_index = 0
    def_index = 0
    for i, (vars, d) in enumerate(defs):
        default_rules += f'fof(imp_new_{i}, axiom, ! [{", ".join(["X", "Y", "Z", *vars])}] : ({" | ".join(tptp_single_negated("old", x) for x in d)} | new(X, Y, Z))).\n'
        if len(d) == 1:
            assert d[0] == ("X", "Y", "Z")
            continue
        skolemification = {}
        for v in vars:
            skolemification[v] = f"sF{skolem_index}(X, Y, Z)"
            skolem_index += 1
        for j, sk in enumerate(d):
            default_rules += f'fof(rule_def_{def_index}_{j}, axiom, ! [X, Y, Z] : (~sP{def_index}(X, Y, Z) | {tptp_single("old", [skolemification.get(x, x) for x in sk])})).\n'
        def_index += 1
    default_rules += "fof(new_new, axiom, new(a, b, c)).\n"

    default_rules += f'fof(new_imp, axiom, ! [X, Y, Z] : (~new(X, Y, Z) | old(X, Y, Z) | {" | ".join(f"sP{i}(X, Y, Z)" for i in range(def_index))})).\n'

    return default_rules


def load_file(filename):
    if not os.path.isfile(filename):
        return None
    with open(filename, "r") as f:
        data = f.read()
        rules = []
        for rule in re.findall(r"Rule\(([^()]+)\)", data):
            rule = json.loads(f"[{rule}]")
            rules.append(Rule(rule[0], rule[1]))
    return rules


def load_models(filename):
    if not os.path.isfile(filename):
        return []
    with open(filename, "r") as f:
        return json.load(f)


def main(timeout, find_rules, self_dual):
    startt = time.perf_counter()
    while time.perf_counter() - startt < timeout:
        print("Trying again, rules:")
        print(rules, len(rules))
        with open(f"data/forcing_rules/{eqid}.rules_wip", "w") as f:
            print(rules, file=f)

        default_rules = construct_tptp(rules)

        inp = (
            default_rules
            + f'fof(preserve, conjecture, {" & ".join(rule.to_tptp("new") for rule in rules)}).\n'
        )
        inp += f"fof(new_def2, axiom, new(X, Y, Z) | ~new(X, Y, Z)).\n"
        try:
            if not find_rules:
                raise CalledProcessError(1, "not testing")
            # print(inp)
            out = subprocess.check_output(
                [
                    "~/Downloads/vampire",
                    "-sa",
                    "fmb",
                    "/proc/self/fd/0",
                    "-t",
                    "1200",
                ],
                input=inp.encode(),
            ).decode()
            if "Termination reason: Refutation" in out:
                raise CalledProcessError(1, "proved valid")
            print("Rules are't preserved.")
            # print(out)
            old = re.findall(r"(?<!~)old\(([\w\'$]+),([\w\'$]+),([\w\'$]+)\)", out)
            aeqb = "b = a" in out
            new = re.findall(r"(?<!~)new\(([\w\'$]+),([\w\'$]+),([\w\'$]+)\)", out)
            # print(old)
            # print('new')
            # print(new)
            prb = find_problems(new, aeqb)
            # print(prb)
            assert prb is not None
            if "c" in prb:
                if len(prb) == 2:
                    assert prb[0] != prb[1]
                    if prb[0] == "c":
                        rule = Rule(old, ("a", "ba"[aeqb], prb[1]))
                    else:
                        rule = Rule(old, ("a", "ba"[aeqb], prb[0]))
                else:
                    rule = Rule(old + [("a", "ba"[aeqb], "c")], prb)
            else:
                rule = Rule(old, prb)
            rule = rule.minimize()
            rules.append(rule)
            if self_dual:  # equation is self dual
                dr = rule.dualize()
                if dr != rule:
                    rules.append(dr)
        except subprocess.CalledProcessError as e:
            print("Timed out (300s)")
            for i, rule in enumerate(rules):
                inp = default_rules
                for j, v in enumerate(rule.to_tptp_negated("new")):
                    inp += f"fof(preserve_{j}, negated_conjecture, {v}).\n"
                try:
                    out = subprocess.check_output(
                        [
                            "~/Downloads/vampire",
                            "--mode",
                            "casc",
                            "--cores",
                            "0",
                            "/proc/self/fd/0",
                            "-t",
                            "60",
                        ],
                        input=inp.encode(),
                    ).decode()
                    with open(f"data/forcing_rules/{eqid}_{i + 1}.proof", "w") as f:
                        f.write(inp)
                        f.write(out)
                except subprocess.CalledProcessError as e:
                    print(f"Couldn't prove rule {i + 1}")
                    print(e)
            return True
    return False


if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--prove", help="Produce proofs for existing rules", action="store_true"
    )
    parser.add_argument("--fresh", help="Don't use existing rules", action="store_true")
    args = parser.parse_args()
    timeout = 1 if args.prove else int(input())

    eqid = input()

    eq = eqs[int(eqid) - 1]
    print(eq)
    self_dual = int(eqid) == 1485  # TODO

    if not args.fresh:
        models = load_models(f"data/forcing_rules/{eqid}.models")
    if not args.fresh and rules is None:
        rules = load_file(f"data/forcing_rules/{eqid}.rules")
    if not args.fresh and rules is None:
        rules = load_file(f"data/forcing_rules/{eqid}.rules_wip")
    if rules is None:
        rules = [Rule([(0, 1, 2), (0, 1, 3)], (2, 3))]
        for r in rulify_eq(eq):
            rules.append(r)
            dr = r.dualize()
            if self_dual and dr not in rules:
                rules.append(dr)
    print("Loaded rules", rules)
    good = False
    try:
        good = main(timeout, not args.prove, self_dual)
    finally:
        print(rules)
        if good:
            with open(f"data/forcing_rules/{eqid}.rules", "w") as f:
                print(rules, file=f)
            os.remove(f"data/forcing_rules/{eqid}.rules_wip")
        else:
            with open(f"data/forcing_rules/{eqid}.rules_wip", "w") as f:
                print(rules, file=f)
