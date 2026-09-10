#!/usr/bin/env python3
"""Emit the machine-checked end-to-end certificate.

Reads the proven results from an entries file exported by `extract_implications`, together with
the Lean-checked duality tables, recomputes the graph, and writes the tables into
equational_theories/Generated/EndToEndCertificate/ as JSON plus a one-line Lean module per table
that loads it. See ../README.md for how to produce the entries file.

Everything emitted is untrusted: `checkCert` validates the certificate, and the fact tables
are proof-carrying so they cannot contain anything false.

Two constraints on the output:
  * RArray literals must be explicit .leaf/.branch trees -- `RArray.ofFn` is well-founded
    recursion and does not reduce in the kernel. The elaborators in
    equational_theories/EndToEnd/Load.lean build them directly as `Expr`s.
  * Duality is applied to the model witnesses only. The directly proven implications already
    generate the full positive graph, so `pos` needs no dual edges.
"""

import json
import os
import re
import sys
from collections import defaultdict, deque

N = 4694
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", ".."))
OUT = os.path.join(REPO, "equational_theories", "Generated", "EndToEndCertificate")
# The numeric tables live beside the modules that load them; `DATA_REL` is how those modules
# name the directory, since the elaborator resolves the path against its own source file.
DATA = os.path.join(OUT, "json")
DATA_REL = "json"

sys.setrecursionlimit(100000)


def load_duals():
    """The duality permutation, from the Lean-checked `duals a ↔ b` tables."""
    dual = {i: i for i in range(1, N + 1)}
    covered = set()
    for f in ("equational_theories/Duals/Basic.lean", "equational_theories/Duals/All.lean"):
        with open(os.path.join(REPO, f), encoding="utf-8") as fh:
            for line in fh:
                m = re.match(r"^duals\s+(\d+)\s+↔\s+(\d+)\s*$", line.strip())
                if m:
                    a, b = int(m.group(1)), int(m.group(2))
                    dual[a], dual[b] = b, a
                    covered.update((a, b))
    assert all(dual[dual[i]] == i for i in range(1, N + 1)), "dual is not an involution"
    uncovered = sorted(set(range(1, N + 1)) - covered)
    assert not uncovered, f"equations with no Lean-checked dual: {uncovered}"
    return dual


def scc(adj):
    """Iterative Tarjan. Returns (component id per vertex, count).

    Components come out in reverse topological order, so every condensation edge runs from a
    higher id to a lower one -- which is why the component id is itself a valid `rank`.
    """
    index, low, onstk, comp, stk = {}, {}, set(), {}, []
    counter = ncomp = 0
    for root in range(1, N + 1):
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter
                counter += 1
                stk.append(v)
                onstk.add(v)
            recurse = False
            nbrs = adj[v]
            for i in range(pi, len(nbrs)):
                w = nbrs[i]
                if w not in index:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                if w in onstk:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                while True:
                    w = stk.pop()
                    onstk.discard(w)
                    comp[w] = ncomp
                    if w == v:
                        break
                ncomp += 1
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
    return comp, ncomp


def build(entries_path):
    dual = load_duals()
    with open(entries_path, encoding="utf-8") as fh:
        entries = json.load(fh)
    num = lambda s: int(s[8:])
    core = lambda n: 1 <= n <= N
    def modname(e):
        # `extract_implications` reports whatever path it was handed, which is absolute when
        # it is run from the repo root. Keep only the part that is a module name.
        p = e["filename"]
        return p[p.rfind("equational_theories/"):].replace("/", ".")[:-len(".lean")]

    # 46 theorem names are declared in up to five `InvariantMetatheoremNonimplications`
    # modules each, so the extension holds several entries per constant; dedupe by name.
    # Conjectures are skipped outright: the certificate must never rest on one.
    impl, impl_mod = [], {}
    witnesses, seen = [], set()
    # Sorted, because the export's own order is however the modules happened to be traversed:
    # it decides `pos` indices and the greedy cover's tie-breaks, and a certificate that only
    # reproduces from one particular export is not reproducible at all.
    for e in sorted(entries, key=lambda e: (e["name"], e["filename"])):
        if not e["proven"] or e["name"] in seen:
            continue
        seen.add(e["name"])
        if "implication" in e["variant"]:
            i = e["variant"]["implication"]
            if not i.get("finite"):          # the general graph only
                a, b = num(i["lhs"]), num(i["rhs"])
                if core(a) and core(b):
                    impl.append((a, b))
                    impl_mod.setdefault((a, b), modname(e))
            continue
        if "facts" not in e["variant"]:
            continue
        fa = e["variant"]["facts"]
        s = sorted({num(x) for x in fa["satisfied"]})
        r = sorted({num(x) for x in fa["refuted"]})
        # A witness whose statement mentions a law outside 1..4694 is skipped rather than
        # truncated: `laws` cannot index those, so `factsProof` would build a statement over
        # a different law list than the one stored. Six witnesses (the SmallMagmas ones) are
        # affected and none is needed -- the cover assertion below would fire if one were.
        if s and r and all(core(a) for a in s) and all(core(b) for b in r):
            witnesses.append((e["name"], s, r, modname(e)))
    print(f"proven implications {len(impl)}, model witnesses {len(witnesses)}")

    # ---- base edges: proven implications, plus one `everything implies Law1` edge per class
    edges = [(a, b) for a, b in impl]              # (a, b) 1-based, index = pos index
    adj = defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
    # provisional SCC to find class representatives for the Law1 edges
    for a in range(1, N + 1):
        adj[a].append(1)
    comp, K = scc(adj)

    # No explicit `Equation1_maximal` edges are needed: every one of the other 1414 classes
    # already reaches Law1's class through the proven implications. Adding a star into that
    # class would also give `rout` a 1414-element row, which is the only thing that would
    # force a maxRecDepth bump on the tables.
    # rebuild adjacency from the real edge list
    adj = defaultdict(list)
    radj = defaultdict(list)
    for idx, (a, b) in enumerate(edges):
        adj[a].append(b)
        radj[b].append(a)
    comp, K = scc(adj)
    size = [0] * K
    for v in range(1, N + 1):
        size[comp[v]] += 1
    reps = {}
    for v in range(1, N + 1):
        reps.setdefault(comp[v], v)
    print(f"base edges {len(edges)}, classes {K}, largest {max(size)}")
    return dual, impl, witnesses, edges, comp, K, size, reps, impl_mod


def combine(chunks):
    """Balanced .branch tree over already-defined chunk arrays, preserving global indexing."""
    def go(lo, hi):
        if hi - lo == 1:
            return chunks[lo][0], chunks[lo][1]
        mid = (lo + hi) // 2
        ln, ls = go(lo, mid)
        rn, rs = go(mid, hi)
        return "(.branch %d %s %s)" % (ls, ln, rn), ls + rs
    return go(0, len(chunks))[0]


WRITTEN = set()


def out_path(mod):
    """Path of a generated module, recorded so `sweep_stale` can delete the rest."""
    WRITTEN.add(mod + ".lean")
    return os.path.join(OUT, mod + ".lean")


def sweep_stale():
    """Delete generated modules this run did not write.

    Shard counts move with the data, and an orphaned shard is invisible to `lake build` since
    nothing imports it: it would just sit in the tree looking current.
    """
    for f in sorted(os.listdir(OUT)):
        if f.endswith(".lean") and f not in WRITTEN:
            os.remove(os.path.join(OUT, f))
            print(f"removed stale {f}")


HEADER = ("/-! Generated by "
          "equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/\n\n")


def shard_doc(base, lo, hi, what, data=None):
    """Explain what a shard holds, and that RArray indices are relative."""
    where = (f"The data itself is in `{DATA_REL}/{data}.json`, shared by every shard; the\n"
             "number after the path is that file's FNV-1a hash, checked on every elaboration\n"
             "because Lake cannot track a file read during one.\n\n" if data else "")
    return (f"/-! `{base.lower()}` entries {lo}-{hi}, where an entry is {what}.\n\n" + where
            + "`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when\n"
            "`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`\n"
            "are left-subtree **sizes**, not indices, and every subtree -- including this\n"
            f"shard -- is indexed from 0. Add {lo} to get an index into `{base.lower()}`.\n-/\n\n")


def fnv1a(data):
    """FNV-1a, 64-bit, matching `EndToEnd.fnv1a`. Guards the data file against
    drifting out of step with the Lean module that names it; see Load.lean."""
    h = 0xcbf29ce484222325
    for b in data:
        h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h


# The `List Nat` tables need a recursion bump; the `Nat` ones need nothing. It is the *compiler*
# that wants it, not the elaborator or the kernel -- marking the definition `noncomputable`
# makes the limit vanish, at the cost of `#eval printResolution`. At the shard size below,
# 16,000 is not enough and 20,000 is.
LIST_OPTS = ["set_option maxRecDepth 20000"]

# Compiling a `List Nat` literal into runnable code is superlinear in its size, so the list
# tables are split. The budget is on the index count, not the row count: rows run from 0 to 91
# long. `Nat` tables need no splitting -- a `Nat` literal is one node however large.
LIST_SHARD = 6000


def shard_rows(rows, budget):
    """Split `rows` into runs of at most `budget` indices, keeping at least one row per run."""
    parts, cur, acc = [], [], 0
    for r in rows:
        if cur and acc + len(r) > budget:
            parts.append(cur); cur, acc = [], 0
        cur.append(r); acc += len(r)
    if cur:
        parts.append(cur)
    return parts


def table_doc(var, lo, hi, name, what, sharded):
    """Explain what a module holds and where its data really lives."""
    doc = (f"/-! `{var}` entries {lo}-{hi}.\n\nAn entry is {what}.\n\n"
           f"The data itself is in `{DATA_REL}/{name}.json`, beside this module. The number\n"
           "after the path is that file's FNV-1a hash, checked on every elaboration because\n"
           "Lake cannot track a file read during one. See `EndToEnd/Load.lean`.\n")
    if sharded:
        doc += ("\n`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when\n"
                "`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after\n"
                "`.branch` are left-subtree **sizes**, not indices, and every subtree --\n"
                f"including this shard -- is indexed from 0. Add {lo} to get an index into\n"
                f"`{var}`.\n")
    return doc + "-/\n\n"


# How each table is written out. `nat` and `natlist` are the values themselves; `bitset`
# stores set-bit positions, and `union` stores row indices into another bitset table whose
# union is the entry. The last two are encoding only: the tables they apply to are sparse or
# already determined, and the kernel re-derives what they mean from
# `checkFwd`/`checkRev`/`checkFmask` either way.
KIND_TY = {"nat": "Nat", "natlist": "(List Nat)", "bitset": "Nat", "union": "Nat"}
KIND_ELAB = {"nat": "loadNatTable%", "natlist": "loadNatListTable%",
             "bitset": "loadBitsetTable%", "union": "loadUnionTable%"}


def emit_json_table(name, rows, kind, what, src=None):
    """Write `json/<name>.json` and the Lean module(s) that load it.

    These tables carry no proofs, so a module is a single `load...%` call; the hash after the
    path is what tells Lean the file it reads is the one the module was generated against.

    One entry per line in the JSON, so `git diff` on a regenerated certificate is readable.
    """
    os.makedirs(DATA, exist_ok=True)
    body = ",\n".join(json.dumps(r, separators=(",", "")) for r in rows)
    blob = ("[\n" + body + "\n]\n").encode("utf-8")
    with open(os.path.join(DATA, f"{name}.json"), "wb") as fh:
        fh.write(blob)
    var, rel, h = "t" + name.lower(), f"{DATA_REL}/{name}.json", fnv1a(blob)
    of_list = kind == "natlist"
    ty, elab = KIND_TY[kind], KIND_ELAB[kind]
    # A `union` entry names rows of another table, so the module has to read that one too.
    tail = ""
    if kind == "union":
        with open(os.path.join(DATA, f"{src}.json"), "rb") as fh:
            tail = f'\n    "{DATA_REL}/{src}.json" {fnv1a(fh.read())}'
    parts = shard_rows(rows, LIST_SHARD) if of_list else [rows]

    def write(mod, defn, lo, hi, sharded):
        with open(out_path(mod), "w", encoding="utf-8") as fh:
            fh.write("import equational_theories.EndToEnd.Load\n\n" + HEADER)
            fh.write(table_doc(var, lo, hi, name, what, sharded))
            fh.write("namespace EndToEnd\n\n")
            if of_list:
                fh.write("".join(o + " in\n" for o in LIST_OPTS))
            fh.write(f"/-- {hi - lo + 1} entries, loaded from `{DATA_REL}/{name}.json`. -/\n")
            fh.write(f"def {defn} : RArray {ty} :=\n  {elab} \"{rel}\" {h}{tail}"
                     + (f"\n    entries {lo} to {hi + 1}\n\n" if sharded else "\n\n"))
            fh.write("end EndToEnd\n")

    if len(parts) == 1:
        write("T" + name, var, 0, len(rows) - 1, False)
    else:
        chunks, lo = [], 0
        for n, part in enumerate(parts):
            write(f"T{name}{n}", f"{var}{n}", lo, lo + len(part) - 1, True)
            chunks.append((f"{var}{n}", len(part)))
            lo += len(part)
        with open(out_path("T" + name), "w", encoding="utf-8") as fh:
            fh.write("".join(
                f"import equational_theories.Generated.EndToEndCertificate.T{name}{n}\n"
                for n in range(len(parts))) + "\n" + HEADER)
            fh.write("namespace EndToEnd\n\n")
            fh.write(f"/-- {len(rows)} entries, assembled from {len(parts)} shards. -/\n")
            fh.write(f"def {var} : RArray {ty} :=\n  " + combine(chunks) + "\n\n")
            fh.write("end EndToEnd\n")
    print(f"{name}: {len(rows)} entries in {len(parts)} module(s), "
          f"{len(blob)/1e6:.2f} MB of JSON")


# How many entries to a shard of each proof-carrying table. Nothing here is elaborated, so the
# trade is between the fixed cost of a module -- about a second of imports -- and the fact that
# a shard must import every theorem module its own entries cite. These values were measured.
POS_CHUNK, NEG_CHUNK, DUAL_CHUNK = 2000, 120, 2000

# As `LIST_OPTS`, and for the same reason: `neg` entries hold `List Nat` law lists.
FACT_OPTS = ["set_option maxRecDepth 20000"]

# What one entry of each table means, for the per-shard docstrings.
EQ = "the SCC of equation index i (0-based, so i is Law{i+1})"
INDEXED_BY = {
    "scc":   EQ,
    "rep":   "a representative equation index for SCC i",
    "reaches":  "a bitset of the SCCs reachable from SCC i",
    "reachedBy": "a bitset of the SCCs that reach SCC i",
    "fmask": "a bitset of the SCCs that model witness i refutes",
    "out":   "indices into `pos` of the cross-SCC edges out of SCC i",
    "rout":  "indices into `pos` of the cross-SCC edges into SCC i",
    "sccUp": "a chain from equation index i to its SCC representative",
    "sccDn": "a chain from the SCC representative to equation index i",
    "refuters": "indices into `neg` of the witnesses covering SCC i's non-implications",
}


def name_parts(lean_name):
    """A Lean name's components, respecting «...» quoting.

    These cannot be split on `.`: `ThreeC2.Fact2` really is namespaced, while
    `«Facts from FinitePoly x² + 3 * x % 4»` is one component that may contain almost anything.
    Lean's parser uses the guillemets to tell them apart; JSON has no such convention.
    """
    parts, cur, quoted = [], "", False
    for ch in lean_name:
        if ch == "«":
            quoted = True
        elif ch == "»":
            quoted = False
        elif ch == "." and not quoted:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return parts


def emit_json_facts(base, name, rows, elab, ty, chunk, what, opts=(), extra=None,
                    extra_imports=()):
    """Write `json/<name>.json` and the shard modules that load slices of it.

    `rows` is a list of `(json value, [modules])` pairs: the JSON says what the entry is, the
    modules are what has to be imported for the citation inside it to resolve. Sharding is no
    longer about `maxRecDepth` -- nothing here is elaborated -- but the shards still earn their
    keep, because each imports only the theorem modules its own entries cite.
    """
    os.makedirs(DATA, exist_ok=True)
    blob = ("[\n" + ",\n".join(json.dumps(v, separators=(", ", ": ")) for v, _ in rows)
            + "\n]\n").encode("utf-8")
    with open(os.path.join(DATA, f"{name}.json"), "wb") as fh:
        fh.write(blob)
    h, rel, var = fnv1a(blob), f"{DATA_REL}/{name}.json", base.lower()
    parts = [rows[i:i + chunk] for i in range(0, len(rows), chunk)]
    chunks, lo = [], 0
    for n, part in enumerate(parts):
        mods = sorted({"equational_theories.EndToEnd.Load"}
                      | {m for _, ms in part for m in ms})
        with open(out_path(f"{base}{n}"), "w", encoding="utf-8") as fh:
            fh.write("".join(f"import {i}\n" for i in mods) + "\n" + HEADER)
            fh.write(shard_doc(base, lo, lo + len(part) - 1, what, name))
            fh.write("namespace EndToEnd\n\n")
            fh.write("".join(o + " in\n" for o in opts))
            fh.write(f"def {var}{n} : RArray {ty} :=\n  {elab} \"{rel}\" {h}\n"
                     f"    entries {lo} to {lo + len(part)}\n\n")
            fh.write("end EndToEnd\n")
        chunks.append((f"{var}{n}", len(part)))
        lo += len(part)
    with open(out_path(base), "w", encoding="utf-8") as fh:
        fh.write("".join(
            f"import equational_theories.Generated.EndToEndCertificate.{base}{n}\n"
            for n in range(len(parts)))
            + "".join(f"import {i}\n" for i in extra_imports) + "\n" + HEADER)
        fh.write("namespace EndToEnd\n\n")
        fh.write(f"/-- {len(rows)} entries, assembled from {len(parts)} shards. -/\n")
        fh.write(f"def {var} : RArray {ty} :=\n  " + combine(chunks) + "\n\n")
        if extra:
            fh.write(extra + "\n")
        fh.write("end EndToEnd\n")
    print(f"{base}: {len(rows)} entries in {len(parts)} shards, {len(blob)/1e6:.2f} MB of JSON")


def emit_pos(impl, edges, impl_mod):
    rows = [([a - 1, b - 1, f"Law{a}_implies_Law{b}"], [impl_mod[(a, b)]]) for a, b in edges]
    emit_json_facts("Pos", "pos", rows, "loadPosTable%", "PosFact", POS_CHUNK,
                    "one proven implication with its proof", opts=FACT_OPTS)


def emit_dual_table(dual):
    """`dualtable`: one `IsDual` fact per law, replacing the per-witness Forall2 chains."""
    rows = [([n - 1, dual[n] - 1, f"dual_{n}"], ["equational_theories.Duals.All"])
            for n in range(1, N + 1)]
    # `dualtable_ok` rides along with the table it is about: each `DualFact` carries its own
    # proof, so no entry can be false, but that the table is *indexed by* the law it names is
    # what `dualIdx` and `negFact_dual_table` rely on, and only `checkDualTable` establishes it.
    ok = (f"/-- The duality table is indexed by the law it talks about. Kernel-checked. -/\n"
          f"theorem dualtable_ok : checkDualTable dualtable {N} = true := by decide!\n")
    emit_json_facts("DualTable", "dualtable", rows, "loadDualTable%", "DualFact", DUAL_CHUNK,
                    "the duality fact for law index i", opts=FACT_OPTS, extra=ok,
                    extra_imports=["equational_theories.DecideBang"])


def emit_all(entries_path):
    dual, impl, witnesses, edges, comp, K, size, reps, impl_mod = build(entries_path)
    emit_pos(impl, edges, impl_mod)
    emit_dual_table(dual)

    adj_e = defaultdict(list)   # equation -> [(edge index, target)]
    radj_e = defaultdict(list)  # equation -> [(edge index, source)]
    for k, (a, b) in enumerate(edges):
        adj_e[a].append((k, b))
        radj_e[b].append((k, a))

    # Tarjan emits components in reverse topological order (edges run high id -> low id),
    # so the component id itself is a valid rank, and K-1-id a valid reverse rank.
    for k, (a, b) in enumerate(edges):
        assert comp[a] >= comp[b], "condensation not in reverse topological order"

    # ---- out / rout: one representative base edge per (class, class) pair
    out = defaultdict(dict)
    rout = defaultdict(dict)
    for k, (a, b) in enumerate(edges):
        ca, cb = comp[a], comp[b]
        if ca != cb:
            out[ca].setdefault(cb, k)
            rout[cb].setdefault(ca, k)

    reaches = [0] * K
    for i in range(K):
        r = 1 << i
        for t in out[i]:
            r |= reaches[t]
        reaches[i] = r
    reachedBy = [0] * K
    for c in range(K - 1, -1, -1):
        r = 1 << c
        for s in rout[c]:
            r |= reachedBy[s]
        reachedBy[c] = r

    # ---- within-class chains to and from the representative
    members = defaultdict(list)
    for v in range(1, N + 1):
        members[comp[v]].append(v)
    sccUp = [None] * (N + 1)
    sccDn = [None] * (N + 1)
    for c, mem in members.items():
        rep, S = reps[c], set(mem)
        # rep -> e  (forward BFS from rep)
        par = {rep: []}
        q = deque([rep])
        while q:
            v = q.popleft()
            for k, w in adj_e[v]:
                if w in S and w not in par:
                    par[w] = par[v] + [k]
                    q.append(w)
        # e -> rep  (backward BFS from rep)
        par2 = {rep: []}
        q = deque([rep])
        while q:
            v = q.popleft()
            for k, w in radj_e[v]:
                if w in S and w not in par2:
                    par2[w] = [k] + par2[v]
                    q.append(w)
        assert len(par) == len(S) and len(par2) == len(S), f"class {c} not strongly connected"
        for e in mem:
            sccDn[e] = par[e]
            sccUp[e] = par2[e]

    # ---- model witnesses, with duals, then a greedy cover
    allw = []
    for name, s, r, mod in witnesses:
        allw.append((name, s, r, None, mod))
        ds = [dual[a] for a in s]
        dr = [dual[b] for b in r]
        if (sorted(ds), sorted(dr)) != (s, r):
            allw.append((name, ds, dr, (s, r), mod))
    T, F = [], []
    for _, s, r, _, _ in allw:
        t = 0
        for a in s:
            t |= reaches[comp[a]]
        f = 0
        for b in r:
            f |= reachedBy[comp[b]]
        T.append(t)
        F.append(f)
    cand = [[] for _ in range(K)]
    for k in range(len(allw)):
        t = T[k]
        while t:
            b = t & -t
            cand[b.bit_length() - 1].append(k)
            t ^= b
    allmask = (1 << K) - 1
    candset = [set(c) for c in cand]
    def cover(i, pool, prefer=frozenset()):
        """Greedy set cover of the SCCs `i` does not imply, drawn from `pool`.

        Returns `(witness, the bits it was picked for)` pairs. `prefer` is exhausted before
        anything else is looked at, which is what keeps the number of *distinct* witnesses
        down: reusing one already in the table is free, while a new one costs a whole `Facts`
        theorem's law lists -- and `neg` is by far the most expensive thing generated.
        """
        pref, chosen, need = pool & prefer, [], allmask & ~reaches[i]
        while need:
            best, bestc = -1, 0
            for tier in (pref, pool):
                for k in tier:
                    c = (F[k] & need).bit_count()
                    if c > bestc:
                        bestc, best = c, k
                if best >= 0:
                    break
            assert best >= 0, f"class {i} has uncoverable non-implications"
            chosen.append((best, F[best] & need))
            need &= ~F[best]
        return chosen

    def covered(i, pool):
        """Does `pool` still cover everything SCC `i` fails to imply? (`checkRefuters`.)"""
        m = reaches[i]
        for k in candset[i] & pool:
            m |= F[k]
        return m == allmask

    # Pass 1: cover every SCC, reusing a witness already in the table wherever one helps.
    taken = set()
    for i in range(K):
        taken.update(k for k, _ in cover(i, candset[i], taken))

    # Pass 2: a witness picked early can be made redundant by later, broader ones. Dropping
    # one can only affect the SCCs it was a candidate for, so re-check just those.
    inv = defaultdict(list)
    for i in range(K):
        for k in candset[i]:
            inv[k].append(i)
    W = set(taken)
    for k in sorted(taken, key=lambda k: len(inv[k])):
        W.discard(k)
        if not all(covered(i, W) for i in inv[k]):
            W.add(k)
    print(f"cover: {len(taken)} witnesses, {len(taken) - len(W)} of them redundant")

    # Pass 3: rebuild the per-SCC refuter lists from the witnesses that survived.
    refuters_raw = [[] for _ in range(K)]
    used = []
    for i in range(K):
        for k, _ in cover(i, candset[i] & W):
            refuters_raw[i].append(k)
            if k not in used:
                used.append(k)

    # Each witness carries every law its `Facts` theorem mentions, which is more than its role
    # in the cover needs: pruning would take these lists from 35,065 indices to about 26,000.
    # `factsProof` reads the full list off the cited theorem's type, so the pruned lists could
    # be stored and weakened to -- but the saving lands in `checkFmask`, and would be paid back
    # in the sublist proof each entry would then carry. Not attempted.
    mx = max(max(len(allw[k][1]), len(allw[k][2])) for k in used)
    print(f"witness lists: {sum(len(allw[k][1]) + len(allw[k][2]) for k in used)} indices, "
          f"longest {mx} laws")

    remap = {k: n for n, k in enumerate(used)}
    print(f"witnesses {len(allw)} -> {len(used)} used, sum|cover| {sum(len(c) for c in refuters_raw)}")

    # ---- emit neg
    rows = []
    for k in used:
        name, sat, ref, orig, mod = allw[k]
        entry = {"sat": [a - 1 for a in sat], "ref": [b - 1 for b in ref],
                 "thm": name_parts(name)}
        mods = [mod]
        if orig is not None:
            os_, or_ = orig
            entry["dualOf"] = {"sat": [a - 1 for a in os_], "ref": [b - 1 for b in or_]}
            mods.append("equational_theories.Generated.EndToEndCertificate.DualTable")
        rows.append((entry, mods))
    emit_json_facts("Neg", "neg", rows, "loadNegTable%", "NegFact", NEG_CHUNK,
                    "one model witness with its magma", opts=FACT_OPTS)

    # ---- emit the certificate tables
    def set_bits(x):
        out, i = [], 0
        while x:
            if x & 1:
                out.append(i)
            x >>= 1
            i += 1
        return out

    # `fmask k` is exactly the union of `reachedBy[scc b]` over the laws `k` refutes -- which
    # is what `checkFmask` verifies -- so name those rows rather than writing out the number.
    fmask_rows = [sorted({comp[b] for b in allw[k][2]}) for k in used]
    tbl = {
        "scc":   [comp[e + 1] for e in range(N)],
        "rep":   [reps[i] - 1 for i in range(K)],
    }
    bits = {
        "reaches":  [set_bits(x) for x in reaches],
        "reachedBy": [set_bits(x) for x in reachedBy],
    }
    lst = {
        "out":   [sorted(out[i].values()) for i in range(K)],
        "rout":  [sorted(rout[i].values()) for i in range(K)],
        "sccUp": [sccUp[e + 1] for e in range(N)],
        "sccDn": [sccDn[e + 1] for e in range(N)],
        "refuters": [[remap[k] for k in refuters_raw[i]] for i in range(K)],
    }
    for name, vals in tbl.items():
        emit_json_table(name, vals, "nat", INDEXED_BY[name])
    for name, vals in bits.items():
        emit_json_table(name, vals, "bitset", INDEXED_BY[name])
    emit_json_table("fmask", fmask_rows, "union", INDEXED_BY["fmask"], src="reachedBy")
    for name, vals in lst.items():
        emit_json_table(name, vals, "natlist", INDEXED_BY[name])
    with open(out_path("Data"), "w", encoding="utf-8") as fh:
        fh.write("".join(
            f"import equational_theories.Generated.EndToEndCertificate.T{n}\n"
            for n in list(tbl) + list(bits) + ["fmask"] + list(lst)) + "\n" + HEADER)
        fh.write("namespace EndToEnd\n\n")
        fields = "\n".join(f"  {f} := t{f.lower()}"
                           for f in list(tbl) + list(bits) + ["fmask"] + list(lst))
        # `rank` and `rrank` were never really tables. Tarjan numbers the SCCs in reverse
        # topological order, so the rank of SCC i *is* i; `checkFwd` still has to verify
        # that, so nothing is being assumed here that was not being checked before.
        fh.write(f"def cert : Certificate where\n"
                 f"  numEq := {N}\n"
                 f"  numSccs := {K}\n"
                 f"  numNeg := {len(used)}\n"
                 f"  rank := id\n"
                 f"  rrank := fun i => {K} - 1 - i\n"
                 + fields + "\n\nend EndToEnd\n")
    print(f"Data.lean: {os.path.getsize(os.path.join(OUT,'Data.lean'))/1e6:.2f} MB")
    sweep_stale()


USAGE = """usage: generate.py ENTRIES.json

ENTRIES.json is the proven-results export, which has to be made by hand:

    lake build equational_theories
    lake exe extract_implications raw --full-entries > ENTRIES.json

See equational_theories/Generated/EndToEndCertificate/README.md."""

if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(USAGE)
    emit_all(sys.argv[1])
