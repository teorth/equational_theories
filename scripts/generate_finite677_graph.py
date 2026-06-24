#!/usr/bin/env python3
"""
Generate the Finite677 implication mini-graph.

In this mini-graph every node represents an equation, and an edge EqA → EqB
means: any finite magma satisfying Equation677 and EqA also satisfies EqB.

Sources of implications:
  1. Regular implications EqA → EqB (finite or general) still hold when
     Eq677 + Finite are assumed, so they become edges EqA → EqB.
  2. Compound "Equation677&EqA" → EqB implications become EqA → EqB.
  3. Equation677 → EqC alone makes EqC "universal" (implied by everything).
  4. Unconditionals (hold in all magmas) are also universal.

Sources of refutations (non-edges):
  - Facts where Equation677 appears in satisfied: if the magma also satisfies EqA
    and refutes EqB, that witnesses EqA ⟹̸ EqB in the mini-graph.
  - Facts where only Equation677 is in satisfied (i.e. the "minimal" Eq677 magma)
    refute EqB: since every universal equation is implied by Eq677, the same magma
    witnesses that any universal equation fails to imply EqB.

Compound transitivity is handled automatically:
  - "Equation677&EqA → EqB" and "Equation677&EqB → EqC" become edges EqA→EqB and
    EqB→EqC in the mini-graph; the transitive closure then gives EqA→EqC.

Usage:
    lake exe extract_implications raw --proven --finite-only \\
      | python scripts/generate_finite677_graph.py [options]

Options:
    --format  {summary,csv,json}  Output format (default: summary)
    --focus   EQN                 Equation to focus on (default: Equation255)
    --extra                       Include equations above 4694 (extra/non-core)
    --close                       Compute transitive closure (requires scipy+numpy)
    --list-all                    In summary mode, list all known/unknown edges
    --most-wanted [K]             Print top-K most-valuable unknown edges
                                  (implies --close; default K=20)
    --trim                        Exclude nodes that already imply the focus equation
                                  from the "open" problem statistics and most-wanted
                                  ranking (implies --close)
"""

import argparse
import io
import json
import sys
from collections import defaultdict, deque

# Ensure stdout/stderr handle Unicode on Windows (cp1252 terminal would crash otherwise).
for _stream_attr in ("stdout", "stderr"):
    _s = getattr(sys, _stream_attr)
    if hasattr(_s, "reconfigure"):
        _s.reconfigure(encoding="utf-8", errors="replace")
    elif hasattr(_s, "buffer"):
        setattr(sys, _stream_attr, io.TextIOWrapper(_s.buffer, encoding="utf-8", errors="replace"))

EQ677 = "Equation677"
EQ255 = "Equation255"
MAX_CORE_EQ = 4694


# ── Equation helpers ──────────────────────────────────────────────────────────

def eq_num(eq_name: str) -> int:
    """Return the equation number for sorting; compound nodes sort by their first."""
    try:
        return int(eq_name.split("&")[0].replace("Equation", ""))
    except ValueError:
        return 0


def is_core_eq(eq: str) -> bool:
    """True iff eq is one of the 4694 core equations."""
    try:
        n = int(eq.replace("Equation", "").split("&")[0])
        return 1 <= n <= MAX_CORE_EQ
    except ValueError:
        return False


# ── Pre-filter to core equations ─────────────────────────────────────────────

def filter_core(data: dict) -> dict:
    """Remove any equation with number > MAX_CORE_EQ from all entries."""
    def lhs_ok(lhs: str) -> bool:
        return all(is_core_eq(e) for e in lhs.split("&"))

    return {
        "implications": [
            imp for imp in data.get("implications", [])
            if lhs_ok(imp["lhs"]) and is_core_eq(imp["rhs"])
        ],
        "facts": [
            f for f in data.get("facts", [])
            if all(is_core_eq(e) for e in f["satisfied"])
            and all(is_core_eq(e) for e in f["refuted"])
        ],
        "unconditionals": [
            e for e in data.get("unconditionals", []) if is_core_eq(e)
        ],
    }


# ── Build mini-graph from raw JSON ────────────────────────────────────────────

def build_finite677_graph(data: dict):
    """
    Parse the JSON output of `extract_implications raw` and build the
    Finite677 mini-graph.

    Returns
    -------
    known_implies     : set of (lhs, rhs) edges (lhs may be a &-compound)
    known_not_implies : set of (lhs, rhs) pairs refuted in this context
    universal         : set of equations implied by Equation677 alone
    """
    implications   = data.get("implications", [])
    facts          = data.get("facts", [])
    unconditionals = data.get("unconditionals", [])

    known_implies     = set()
    known_not_implies = set()
    universal         = set()

    for eq in unconditionals:
        universal.add(eq)

    for imp in implications:
        lhs = imp["lhs"]
        rhs = imp["rhs"]

        if "&" in lhs:
            parts = lhs.split("&")
            if EQ677 in parts:
                other = [p for p in parts if p != EQ677]
                if not other:
                    universal.add(rhs)
                elif len(other) == 1:
                    known_implies.add((other[0], rhs))
                else:
                    # Eq677 + two or more others: store as compound mini-graph node
                    compound = "&".join(sorted(other))
                    known_implies.add((compound, rhs))
            # compound without Eq677: irrelevant for this mini-graph
        elif lhs == EQ677:
            universal.add(rhs)
        else:
            # Regular implication: still valid when Eq677 + Finite are assumed
            known_implies.add((lhs, rhs))

    # Collect every equation refuted in ANY fact that includes Eq677 in satisfied.
    # Key insight: any such witness magma satisfies Eq677, hence also satisfies
    # every universal equation (Eq1, Eq614, …).  Therefore, any equation refuted
    # by that magma is also NOT implied by any universal equation in this context.
    all_677_refuted: set[str] = set()

    for fact in facts:
        satisfied = fact["satisfied"]
        refuted   = fact["refuted"]
        if EQ677 not in satisfied:
            continue
        other_sat = [eq for eq in satisfied if eq != EQ677]
        for ref in refuted:
            all_677_refuted.add(ref)
            if ref in universal:
                print(
                    f"Warning: contradiction – {EQ677} both implies and "
                    f"not-implies {ref}",
                    file=sys.stderr,
                )
        for sat in other_sat:
            for ref in refuted:
                known_not_implies.add((sat, ref))

    # Every equation refuted by some Eq677-satisfying magma cannot be implied
    # by any universal equation (the same magma is a witness for all of them).
    for x in universal:
        for y in all_677_refuted:
            if y not in universal:
                known_not_implies.add((x, y))

    return known_implies, known_not_implies, universal


def collect_nodes(known_implies, known_not_implies, universal):
    nodes = set()
    for lhs, rhs in known_implies:
        if "&" not in lhs:
            nodes.add(lhs)
        nodes.add(rhs)
    for lhs, rhs in known_not_implies:
        if "&" not in lhs:
            nodes.add(lhs)
        nodes.add(rhs)
    nodes.update(universal)
    nodes.discard(EQ677)
    return nodes


# ── Fast reachability via SCC condensation + dense Warshall ──────────────────

def compute_reachability(nodes_list, simple_edges):
    """
    Compute full pairwise reachability using SCC condensation + numpy.

    The condensed DAG is processed in reverse topological order so that each
    SCC's reachability row is built by OR-ing its children — O(n_comp² / 8)
    with numpy boolean arrays instead of O(n³).

    Returns
    -------
    reach    : np.ndarray shape (n, n), dtype bool
    node_idx : dict  node_name → index
    """
    try:
        import numpy as np
        from scipy.sparse import csr_matrix
        from scipy.sparse.csgraph import connected_components
    except ImportError as e:
        raise ImportError(
            "scipy and numpy are required for --close / --most-wanted / --trim.\n"
            "Install with:  pip install scipy numpy"
        ) from e

    import numpy as np

    n = len(nodes_list)
    if n == 0:
        return np.zeros((0, 0), dtype=bool), {}

    node_idx = {node: i for i, node in enumerate(nodes_list)}

    rows, cols = [], []
    for a, b in simple_edges:
        ai, bi = node_idx.get(a), node_idx.get(b)
        if ai is not None and bi is not None and ai != bi:
            rows.append(ai)
            cols.append(bi)

    if not rows:
        return np.eye(n, dtype=bool), node_idx

    adj = csr_matrix(
        (np.ones(len(rows), dtype=np.float32), (rows, cols)), shape=(n, n)
    )

    # ── SCC condensation ─────────────────────────────────────────────────────
    n_comp, labels = connected_components(adj, directed=True, connection="strong")

    # Condensed DAG edges (unique)
    comp_edge_set = set()
    for r, c in zip(rows, cols):
        cr, cc = labels[r], labels[c]
        if cr != cc:
            comp_edge_set.add((cr, cc))

    # Children list + in-degree for topological sort
    children  = defaultdict(list)
    in_deg    = defaultdict(int)
    for cr, cc in comp_edge_set:
        children[cr].append(cc)
        in_deg[cc] += 1

    # Kahn's algorithm
    topo = []
    q = deque(i for i in range(n_comp) if in_deg[i] == 0)
    in_deg_copy = defaultdict(int, in_deg)
    while q:
        v = q.popleft()
        topo.append(v)
        for u in children[v]:
            in_deg_copy[u] -= 1
            if in_deg_copy[u] == 0:
                q.append(u)

    # Dense boolean reachability on condensed DAG.
    # Process sources-last (reverse topo = sinks first) so children are ready.
    comp_reach = np.eye(n_comp, dtype=bool)
    for v in reversed(topo):
        for u in children[v]:
            comp_reach[v] |= comp_reach[u]

    # Expand back to original nodes via label broadcast
    reach = comp_reach[labels[:, np.newaxis], labels[np.newaxis, :]]
    return reach, node_idx


# ── Base-graph SCC count (before Finite677 additions) ─────────────────────────

def count_base_sccs(nodes_list, known_implies):
    """
    Count strongly-connected components using only regular (non-compound, non-677)
    implications — i.e. the general implication graph without the extra edges that
    the Finite677 context adds (no universal edges, no '&' compound edges).

    This is O(V+E) via scipy and is used to quantify how many additional equivalences
    the Finite677 context introduces on top of the original graph.
    """
    import numpy as np
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import connected_components

    n = len(nodes_list)
    base_idx = {node: i for i, node in enumerate(nodes_list)}

    rows, cols = [], []
    for a, b in known_implies:
        if "&" not in a and a in base_idx and b in base_idx:
            rows.append(base_idx[a])
            cols.append(base_idx[b])

    if not rows:
        return n  # no edges → every node is its own SCC

    mat = csr_matrix(
        (np.ones(len(rows), dtype=bool), (rows, cols)), shape=(n, n)
    )
    n_comp, _ = connected_components(mat, directed=True, connection="strong")
    return n_comp


# ── Canonicalization (collapse equivalent nodes) ─────────────────────────────

def canonicalize(nodes_list, reach, node_idx):
    """
    Collapse equivalent nodes (those that mutually imply each other) to a single
    canonical representative — the one with the smallest equation number.

    This is done *after* the full transitive closure so that equivalences induced
    by the Finite677 context (e.g. regular Eq6 ≡ Eq2 in the general graph) are
    captured automatically.

    Returns
    -------
    canon_nodes    : list of canonical node names, sorted by eq_num
    canon_reach    : (len(canon_nodes), len(canon_nodes)) bool ndarray
    canon_node_idx : dict  node_name → index in canon_nodes
    canonical_of   : dict  every_node → canonical_node_name
    """
    import numpy as np

    n = len(nodes_list)

    # equiv[i, j] = True iff i and j are in the same SCC (mutually reachable)
    equiv = reach & reach.T  # (n, n) bool, fast with numpy

    canonical_of: dict[str, str] = {}
    for i in range(n):
        node = nodes_list[i]
        if node in canonical_of:
            continue
        members_idx = np.where(equiv[i])[0]
        members = [nodes_list[j] for j in members_idx]
        rep = min(members, key=eq_num)
        for m in members:
            canonical_of[m] = rep

    # Indices of canonical reps in nodes_list (one per SCC)
    canon_nodes = sorted(
        {rep for rep in canonical_of.values()},
        key=eq_num,
    )
    canon_node_idx = {node: i for i, node in enumerate(canon_nodes)}

    # Restrict reach to the canonical rows/columns
    ci = np.array([node_idx[node] for node in canon_nodes], dtype=int)
    canon_reach = reach[np.ix_(ci, ci)]

    return canon_nodes, canon_reach, canon_node_idx, canonical_of


# ── Most-wanted analysis (fully numpy-vectorised) ─────────────────────────────

def most_wanted(
    nodes_list,
    reach,
    node_idx,
    known_not_implies,
    focus=EQ255,
    topk=20,
    trim=False,
    universal=None,
):
    """
    Rank unknown edges by how valuable proving them would be.

    Value of proving edge (A → B):
        anc_count_active[A] × desc_count[B]
    where anc_count_active[A] = number of "active" nodes that can reach A.

    Without --trim, all nodes are active.
    With --trim, only unsolved nodes (those that do NOT yet imply focus) are active.

    new_focus(A → B) = number of active unsolved nodes that would newly imply
    the focus equation if A → B were added (only nonzero when B already implies
    focus and A does not).

    Sorting: primary key = new_focus (desc), secondary = value (desc).

    Universal equations (implied by Equation677 alone) are excluded as LHS
    candidates: adding a universal equation as a hypothesis gives no new
    information beyond what Equation677 + Finite already provides.
    """
    import numpy as np

    n = len(nodes_list)
    if n == 0:
        return []

    fi = node_idx.get(focus)

    # ── Not-implies matrix ────────────────────────────────────────────────────
    not_impl = np.zeros((n, n), dtype=bool)
    for a, b in known_not_implies:
        ai, bi = node_idx.get(a), node_idx.get(b)
        if ai is not None and bi is not None:
            not_impl[ai, bi] = True

    # ── Unknown candidate mask ────────────────────────────────────────────────
    unknown = ~reach & ~not_impl
    np.fill_diagonal(unknown, False)

    # Universal equations as LHS add no new information (Eq677 already implies
    # them), so they are not useful hypotheses.
    if universal:
        univ_mask = np.array([nodes_list[i] in universal for i in range(n)], dtype=bool)
        unknown[univ_mask, :] = False

    # ── Active sources ────────────────────────────────────────────────────────
    has_focus  = reach[:, fi] if fi is not None else np.zeros(n, dtype=bool)
    not_focus  = ~has_focus

    if trim:
        # Solved (has_focus) nodes are not interesting as sources
        unknown[has_focus] = False
        active = not_focus
    else:
        active = np.ones(n, dtype=bool)

    # ── Ancestor / descendant counts ──────────────────────────────────────────
    # anc_count[i] = # active nodes that can reach i  (row-vector × reach matrix)
    anc_count  = active.astype(np.int32) @ reach.astype(np.int32)    # shape (n,)
    desc_count = reach.astype(np.int32).sum(axis=1)                   # shape (n,)

    # ── Value matrix ─────────────────────────────────────────────────────────
    value = np.outer(anc_count, desc_count).astype(np.int64)
    value[~unknown] = 0

    # ── new_focus matrix ─────────────────────────────────────────────────────
    # new_focus(i, j) = # (active & not_focus) nodes reaching i
    #                   when has_focus[j] and not_focus[i]
    if fi is not None:
        active_no_focus = (active & not_focus)
        # new_focus_per_src[i] = # active-unsolved nodes reaching i
        new_focus_per_src = (
            active_no_focus.astype(np.int32) @ reach.astype(np.int32)
        )  # shape (n,)
        # Broadcast: only relevant when j has focus and i does not
        new_focus_mat = np.outer(
            new_focus_per_src * not_focus.astype(np.int32),
            has_focus.astype(np.int32),
        ).astype(np.int64)
        new_focus_mat[~unknown] = 0
    else:
        new_focus_mat = np.zeros((n, n), dtype=np.int64)

    # ── Compound score for joint sort ────────────────────────────────────────
    # Primary: new_focus (higher = better). Secondary: value (higher = better).
    # Scale so that new_focus dominates.
    max_val = int(value.max()) + 1 if value.max() > 0 else 1
    score = new_focus_mat * max_val + value
    score[~unknown] = -1

    # ── Top-K via argpartition (O(n²) — much faster than full sort) ───────────
    flat  = score.ravel()
    n_unk = int(unknown.sum())
    if n_unk == 0:
        return []
    k = min(topk, n_unk)
    top_flat = np.argpartition(flat, -k)[-k:]
    top_flat = top_flat[np.argsort(flat[top_flat])[::-1]]

    results = []
    for fidx in top_flat:
        i, j = divmod(int(fidx), n)
        if not unknown[i, j]:
            continue
        v  = int(value[i, j])
        nf = int(new_focus_mat[i, j])
        if v == 0 and nf == 0:
            break
        results.append((nodes_list[i], nodes_list[j], v, nf))

    return results[:topk]


# ── Summary output ────────────────────────────────────────────────────────────

def print_summary(
    known_implies,
    known_not_implies,
    universal,
    all_nodes,
    focus,
    reach=None,
    node_idx=None,
    nodes_list=None,
    list_all=False,
    topk=0,
    trim=False,
    class_accounting=None,
):
    print(f"=== Finite677 Mini-Graph ===")
    print(f"  Base assumption : {EQ677} + Finite")
    print(f"  Distinct nodes  : {len(all_nodes)}")
    print(f"  Edges (raw)     : {len(known_implies)}")
    print(f"  Refutations     : {len(known_not_implies)}")

    # ── Focus section ──────────────────────────────────────────────────────
    print(f"\n--- Status of ? ⟹ {focus} (assuming {EQ677} + Finite) ---")

    if focus in universal:
        print(f"  {EQ677} alone implies {focus}!")

    if reach is not None:
        import numpy as np
        n  = len(nodes_list)
        fi = node_idx.get(focus)

        if fi is not None:
            imply_mask    = reach[:, fi]
            refuted_set   = {lhs for lhs, rhs in known_not_implies if rhs == focus}
            solved_set    = {nodes_list[i] for i in range(n) if imply_mask[i] and nodes_list[i] != focus}

            implies_focus     = sorted(solved_set, key=eq_num)
            not_implies_focus = sorted(refuted_set, key=eq_num)
            unknown_focus     = [
                nodes_list[i] for i in range(n)
                if not imply_mask[i]
                and nodes_list[i] not in refuted_set
                and nodes_list[i] != focus
            ]
            unknown_focus.sort(key=eq_num)

            if trim:
                open_nodes = unknown_focus
                print(f"  Solved (imply {focus})          : {len(implies_focus)}")
                print(f"  Refuted (can't imply {focus})   : {len(not_implies_focus)}")
                print(f"  Open (unknown, post-trim)       : {len(open_nodes)}")
            else:
                print(f"  Equations implying {focus}     : {len(implies_focus)}")
                print(f"  Equations not implying {focus} : {len(not_implies_focus)}")
                print(f"  Unknown                        : {len(unknown_focus)}")

            if list_all:
                if implies_focus:
                    print(f"\n  IMPLIES {focus}  ({len(implies_focus)}):")
                    for eq in implies_focus:
                        print(f"    {eq}")
                else:
                    print(f"\n  IMPLIES {focus}: (none known)")

                if not_implies_focus:
                    print(f"\n  DOES NOT IMPLY {focus}  ({len(not_implies_focus)}):")
                    for eq in not_implies_focus:
                        print(f"    {eq}")
                else:
                    print(f"\n  DOES NOT IMPLY {focus}: (none known)")

                label = "OPEN" if trim else "UNKNOWN"
                display_unknown = unknown_focus
                print(f"\n  {label}  ({len(display_unknown)}):")
                for eq in display_unknown:
                    print(f"    {eq}")
        else:
            print(f"  ({focus} not found in the mini-graph)")
    else:
        impl  = [(l, r) for l, r in known_implies    if r == focus and l != focus]
        notim = [(l, r) for l, r in known_not_implies if r == focus]
        print(f"  Direct implications to {focus} : {len(impl)}")
        print(f"  Direct refutations to {focus}  : {len(notim)}")
        print(f"  (run with --close for the full transitive picture)")

    # ── Equivalence-class accounting ────────────────────────────────────────
    if class_accounting is not None:
        ac = class_accounting
        n_eq   = ac["n_equations"]
        n_base = ac["n_base_sccs"]
        n_f677 = ac["n_finite677_classes"]
        merges = ac["n_finite677_merges"]
        univ_c = ac["univ_classes"]          # dict: canon_rep → [members]
        n_univ_orig = sum(len(v) for v in univ_c.values())  # total original eqs subsumed
        n_univ_cls  = len(univ_c)                            # canonical universal classes
        n_solved    = ac["n_solved"]
        M           = ac["M"]

        print(f"\n--- Equivalence-class accounting ---")
        print(f"  Equations in mini-graph (excl. {EQ677}) : {n_eq}")
        print(f"  Original graph SCCs (all {n_eq + 1} eqs,         : {n_base}")
        print(f"    incl. {EQ677} as its own class)")
        merge_word = "merge" if merges == 1 else "merges"
        print(f"  Finite677 canonical classes              : {n_f677}"
              f"  ({merges} additional {merge_word} from Finite677 context)")
        print()
        print(f"  Breakdown of the {n_f677} Finite677 classes:")

        # Universal
        univ_lines = []
        for canon in sorted(univ_c, key=eq_num):
            members = univ_c[canon]
            if len(members) == 1:
                univ_lines.append(f"    {canon}")
            else:
                others = [m for m in members if m != canon]
                univ_lines.append(
                    f"    {canon}  [+ {', '.join(others)}]"
                )
        print(
            f"    Universal (free given Eq677+Finite)   :"
            f" {n_univ_cls} class{'es' if n_univ_cls != 1 else ''}"
            f"  ({n_univ_orig} original equations)"
        )
        for line in univ_lines:
            print(line)

        print(f"    Solved (already → {focus})          :"
              f" {n_solved} class{'es' if n_solved != 1 else ''}")
        print(f"    {focus} itself (the target)               :  1 class")
        print(f"    ─────────────────────────────────────────────────────")
        print(f"    M = Open (unknown → {focus}?)         :"
              f" {M} classes")
        print()
        print(
            f"  Each open class is a distinct hypothesis to determine:\n"
            f"  \"does {EQ677} + EqX + Finite ⟹ {focus}?\""
        )

    # ── Most-wanted ────────────────────────────────────────────────────────
    if topk > 0 and reach is not None:
        mw = most_wanted(
            nodes_list, reach, node_idx, known_not_implies,
            focus=focus, topk=topk, trim=trim, universal=universal,
        )
        trim_tag = " [trim mode]" if trim else ""
        print(f"\n--- Most-wanted unknown implications (top {topk}){trim_tag} ---")
        hdr_focus = f"New→{focus}"
        print(f"  {'Edge':<42}  {'Value':>9}  {hdr_focus:>14}")
        print(f"  {'-'*42}  {'-'*9}  {'-'*14}")
        for a, b, value, new_focus in mw:
            edge_str = f"{a} → {b}"
            print(f"  {edge_str:<42}  {value:>9}  {new_focus:>14}")
        if not mw:
            print("  (no unknown edges with nonzero value)")


# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Generate the Finite677 implication mini-graph.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--format",
        choices=["summary", "csv", "json"],
        default="summary",
        help="Output format (default: summary)",
    )
    parser.add_argument(
        "--focus",
        default=EQ255,
        metavar="EQN",
        help=f"Equation to focus on (default: {EQ255})",
    )
    parser.add_argument(
        "--extra",
        action="store_true",
        help=f"Include equations above {MAX_CORE_EQ} (non-core); by default they are filtered out",
    )
    parser.add_argument(
        "--close",
        action="store_true",
        help="Compute transitive closure (requires scipy + numpy)",
    )
    parser.add_argument(
        "--list-all",
        action="store_true",
        help="In summary mode, list every known/refuted/unknown edge to the focus equation",
    )
    parser.add_argument(
        "--most-wanted",
        nargs="?",
        const=20,
        type=int,
        metavar="K",
        help="Print top-K most-valuable unknown edges (implies --close; default K=20)",
    )
    parser.add_argument(
        "--trim",
        action="store_true",
        help=(
            "Exclude nodes that already imply the focus equation from the 'open' "
            "statistics and most-wanted ranking (implies --close)"
        ),
    )
    args = parser.parse_args()

    if args.most_wanted is not None or args.trim:
        args.close = True

    data = json.load(sys.stdin)

    if not args.extra:
        data = filter_core(data)

    known_implies, known_not_implies, universal = build_finite677_graph(data)

    all_nodes  = collect_nodes(known_implies, known_not_implies, universal)
    nodes_list = sorted(all_nodes, key=eq_num)

    # ── Optional transitive closure ───────────────────────────────────────────
    reach    = None
    node_idx = None
    if args.close:
        simple_edges = [(a, b) for a, b in known_implies if "&" not in a]
        # Reflexive
        simple_edges += [(n, n) for n in nodes_list]
        # Universal equations are reachable from every node
        for node in nodes_list:
            for u in universal:
                if u in all_nodes:
                    simple_edges.append((node, u))

        print(
            f"Computing transitive closure over {len(nodes_list)} nodes, "
            f"{len(simple_edges)} edges …",
            file=sys.stderr,
        )
        reach, node_idx = compute_reachability(nodes_list, simple_edges)

        # ── Collapse equivalent nodes to canonical representatives ────────────
        # Two nodes are equivalent iff they mutually imply each other in the
        # Finite677 context.  We keep only the one with the smallest equation
        # number per equivalence class so that the analysis and output are
        # unambiguous and non-redundant.
        nodes_list_orig = list(nodes_list)   # save pre-canon list for accounting
        nodes_list, reach, node_idx, canonical_of = canonicalize(
            nodes_list, reach, node_idx
        )
        n_orig = len(all_nodes)
        n_canon = len(nodes_list)
        print(
            f"  Done. {n_orig} nodes → {n_canon} canonical representatives "
            f"({n_orig - n_canon} collapsed).",
            file=sys.stderr,
        )

        # Map known_not_implies to canonical space so the not-impl matrix is
        # complete (e.g. if (Eq2, EqB) is known-not, (Eq6, EqB) follows since
        # Eq6 ≡ Eq2; mapping both to Eq2 makes this automatic).
        known_not_implies = {
            (canonical_of.get(a, a), canonical_of.get(b, b))
            for a, b in known_not_implies
        }
        known_not_implies -= {(a, a) for a in nodes_list}  # drop self-loops

        # Also canonicalize the focus in case it has a smaller canonical rep
        args.focus = canonical_of.get(args.focus, args.focus)

        # Canonicalize the universal set (Equation1 and Equation614 are already
        # the smallest in their SCCs, but be robust in case that ever changes).
        universal = {canonical_of.get(eq, eq) for eq in universal}

        # ── Equivalence-class accounting ───────────────────────────────────
        # Count SCCs in the base (non-677) graph — fast O(V+E) via scipy.
        # Include Equation677 itself as a node (it was a separate SCC in the
        # full original graph; conditioning on it removes it as a node but its
        # SCC "merges" with the universal class it creates).
        n_base_sccs = count_base_sccs([EQ677] + nodes_list_orig, known_implies)

        # For each canonical universal representative, list its original members.
        univ_classes: dict[str, list[str]] = {}
        for eq, canon in canonical_of.items():
            if canon in universal:
                univ_classes.setdefault(canon, []).append(eq)
        for canon in univ_classes:
            univ_classes[canon] = sorted(univ_classes[canon], key=eq_num)

        # Solved count: canonical classes that imply focus (excluding focus itself).
        fi = node_idx.get(args.focus)
        if fi is not None:
            import numpy as np
            n_solved = int(reach[:, fi].sum())
            if args.focus in node_idx:
                n_solved -= 1   # don't count focus implying itself
        else:
            n_solved = 0

        n_univ_classes = len(univ_classes)
        has_focus = 1 if args.focus in node_idx else 0
        M_open = len(nodes_list) - n_univ_classes - n_solved - has_focus

        class_accounting = {
            "n_equations":         len(nodes_list_orig),
            "n_base_sccs":         n_base_sccs,
            "n_finite677_classes": len(nodes_list),
            "n_finite677_merges":  n_base_sccs - len(nodes_list),
            "univ_classes":        univ_classes,
            "n_solved":            n_solved,
            "has_focus":           bool(has_focus),
            "M":                   M_open,
        }
    else:
        class_accounting = None

    # ── Output ────────────────────────────────────────────────────────────────
    topk = args.most_wanted if args.most_wanted is not None else 0

    if args.format == "summary":
        print_summary(
            known_implies, known_not_implies, universal, all_nodes,
            focus=args.focus,
            reach=reach, node_idx=node_idx, nodes_list=nodes_list,
            list_all=args.list_all,
            topk=topk,
            trim=args.trim,
            class_accounting=class_accounting,
        )

    elif args.format == "csv":
        import csv
        writer = csv.writer(sys.stdout)
        writer.writerow(["lhs", "rhs", "status"])
        for eq in sorted(universal, key=eq_num):
            writer.writerow([EQ677, eq, "implies"])

        if reach is not None:
            n = len(nodes_list)
            for i in range(n):
                for j in range(n):
                    if i != j and reach[i, j]:
                        writer.writerow([nodes_list[i], nodes_list[j], "implies"])
        else:
            for lhs, rhs in sorted(known_implies, key=lambda x: (eq_num(x[0]), eq_num(x[1]))):
                if lhs != rhs:
                    writer.writerow([lhs, rhs, "implies"])

        for lhs, rhs in sorted(known_not_implies, key=lambda x: (eq_num(x[0]), eq_num(x[1]))):
            writer.writerow([lhs, rhs, "not_implies"])

    elif args.format == "json":
        if reach is not None:
            n = len(nodes_list)
            impl_list = [
                {"lhs": nodes_list[i], "rhs": nodes_list[j]}
                for i in range(n) for j in range(n)
                if i != j and reach[i, j]
            ]
        else:
            impl_list = [
                {"lhs": lhs, "rhs": rhs}
                for lhs, rhs in sorted(known_implies, key=lambda x: (eq_num(x[0]), eq_num(x[1])))
                if lhs != rhs
            ]
        notimpl_list = [
            {"lhs": lhs, "rhs": rhs}
            for lhs, rhs in sorted(known_not_implies, key=lambda x: (eq_num(x[0]), eq_num(x[1])))
        ]

        output = {
            "base": EQ677,
            "note": (
                f"Each edge (lhs → rhs) means: a finite magma satisfying "
                f"{EQ677} and lhs also satisfies rhs."
            ),
            "universal": sorted(list(universal), key=eq_num),
            "implications": impl_list,
            "non_implications": notimpl_list,
        }
        print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
