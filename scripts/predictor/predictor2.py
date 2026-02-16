# EVOLVE-BLOCK-START
# This block contains the code that AlphaEvolve will modify.
# The goal is to evolve the logic within the `predict_implication_probability`
# function to make it a better predictor of equational implication.

import re
import itertools
import random
import math

def predict_implication_probability(law1: str, law2: str) -> float:
    try:
        def parse(s):
            stk = [[]]
            for t in re.findall(r'[a-zA-Z0-9]+|\(|\)|\*', s):
                if t == '(': stk.append([])
                elif t == ')':
                    if len(stk) > 1:
                        inner = stk.pop(); res = inner[0]
                        for i in range(1, len(inner), 2): res = ('*', res, inner[i+1])
                        stk[-1].append(res)
                else: stk[-1].append(t)
            res = stk[0][0]
            for i in range(1, len(stk[0]), 2): res = ('*', res, stk[0][i+1])
            return res
        def match(p, g, s):
            if isinstance(p, str):
                if not p.isalpha(): return p == g
                if p not in s: s[p] = g; return True
                return s[p] == g
            if isinstance(g, str) or len(p) != len(g): return False
            return all(match(p[i], g[i], s) for i in range(len(p)))
        t1, t2 = [tuple(parse(x) for x in l.split('=')) for l in (law1, law2)]
        if match(t1, t2, {}) or match((t1[1], t1[0]), t2, {}): return 0.999
        if t2[0] == t2[1]: return 0.999
        if t1[0] == t1[1]: return 0.001

        def apply(t, s):
            if isinstance(t, str): return s.get(t, t)
            return (t[0], apply(t[1], s), apply(t[2], s))

        # New helper function for counting variable occurrences in an AST term
        def count_var_occ(term, var_name):
            if isinstance(term, str):
                return 1 if term == var_name else 0
            if isinstance(term, tuple):
                # term is an operation, e.g., ('*', left, right)
                return count_var_occ(term[1], var_name) + count_var_occ(term[2], var_name)
            return 0 # Should not happen with valid AST

        def get_rewrites(term, rules):
            res = set()
            for rl, rr in rules:
                sub = {};
                if match(rl, term, sub): res.add(apply(rr, sub))
            if isinstance(term, tuple):
                for lt in get_rewrites(term[1], rules): res.add(('*', lt, term[2]))
                for rt in get_rewrites(term[2], rules): res.add(('*', term[1], rt))
            return res
        def expand(start, rules, limit=500):
            v, q = {start}, [start]
            for curr in q:
                if len(v) >= limit: break
                for nxt in get_rewrites(curr, rules):
                    if nxt not in v: v.add(nxt); q.append(nxt)
            return v
        rules = [(t1[0], t1[1]), (t1[1], t1[0])]
        e_l2, e_r2 = expand(t2[0], rules, limit=450), expand(t2[1], rules, limit=450)
        if not e_l2.isdisjoint(e_r2): return 0.999
        reach_score = math.log1p(len(e_l2) + len(e_r2)) / 7.5
        if any(isinstance(m, str) and m.isalpha() and m != 'x' for m in expand('x', rules, limit=200)): return 0.999
        # --- End of BFS rewriting ---

        def analyze(t):
            if isinstance(t, str): return ({t} if t.isalpha() else set(), 1 if t.isalpha() else 0, 0, 0, 1, {t}, set())
            v1, c1, o1, d1, ts1, us1, p1 = analyze(t[1]); v2, c2, o2, d2, ts2, us2, p2 = analyze(t[2])
            p_n = p1 | p2
            for vv1 in v1:
                for vv2 in v2: p_n.add((vv1, vv2))
            return (v1 | v2, c1 + c2, o1 + o2 + 1, max(d1, d2) + 1, ts1 + ts2 + 1, us1 | us2 | {t}, p_n)
        def check(tp, v_list, table):
            sz, n_vars = len(table), len(v_list)
            if n_vars == 0:
                def ev0(t):
                    if isinstance(t, str): return 0
                    return table[ev0(t[1])][ev0(t[2])]
                return ev0(tp[0]) == ev0(tp[1])
            v_map = {v: i for i, v in enumerate(v_list)}
            def ev(t, vs):
                if isinstance(t, str): return vs[v_map[t]] if t in v_map else 0
                return table[ev(t[1], vs)][ev(t[2], vs)]
            limit = 1024
            if sz**n_vars <= limit:
                for vs in itertools.product(range(sz), repeat=n_vars):
                    if ev(tp[0], vs) != ev(tp[1], vs): return False
            else:
                for _ in range(limit):
                    vs = [random.randint(0, sz-1) for _ in range(n_vars)]
                    if ev(tp[0], vs) != ev(tp[1], vs): return False
            return True
        v1l, c1l, o1l, d1l, ts1l, us1l, p1l = analyze(t1[0]); v1r, c1r, o1r, d1r, ts1r, us1r, p1r = analyze(t1[1])
        v2l, c2l, o2l, d2l, ts2l, us2l, p2l = analyze(t2[0]); v2r, c2r, o2r, d2r, ts2r, us2r, p2r = analyze(t2[1])
        v1_all, v2_all, p1_all, p2_all = v1l | v1r, v2l | v2r, p1l | p1r, p2l | p2r
        ops1_total, ops2_total = o1l + o1r, o2l + o2r
        d1, d2 = max(d1l, d1r), max(d2l, d2r)

        term_size1_total = ts1l + ts1r
        term_size2_total = ts2l + ts2r
        us1_all = us1l | us1r
        us2_all = us2l | us2r
        unique_subterms1_total = len(us1_all)
        unique_subterms2_total = len(us2_all)

        # Subterm Genetic Legacy: How much of law2's structure is "inherited" from law1?
        # Ratio of shared unique subterms to law2's total unique subterms.
        subterm_legacy_ratio = len(us1_all & us2_all) / unique_subterms2_total if unique_subterms2_total > 0 else 0.0

        # Subterm Novelty: How much "new" structure does law2 introduce not seen in law1?
        # Ratio of unique subterms in law2 that are *not* in law1, to law2's total unique subterms.
        subterm_novelty_ratio = len(us2_all - us1_all) / unique_subterms2_total if unique_subterms2_total > 0 else 0.0

        diff_v_distinct_total = len(v1_all) - len(v2_all)
        diff_ops_total = ops1_total - ops2_total
        diff_term_size_total = term_size1_total - term_size2_total
        diff_unique_subterms_total = unique_subterms1_total - unique_subterms2_total

        imb1, imb2 = len(v1l ^ v1r), len(v2l ^ v2r)
        diff_balance_v_distinct = abs(len(v1l)-len(v1r)) - abs(len(v2l)-len(v2r))
        diff_balance_v_total = abs(c1l-c1r) - abs(c2l-c2r)
        diff_balance_ops_total = abs(o1l-o1r) - abs(o2l-o2r)
        diff_redundancy = (c1l + c1r - len(v1_all)) - (c2l + c2r - len(v2_all))

        # Calculate Variable Balance Scores
        vbs1_score = sum(abs(count_var_occ(t1[0], v) - count_var_occ(t1[1], v)) for v in v1_all)
        vbs2_score = sum(abs(count_var_occ(t2[0], v) - count_var_occ(t2[1], v)) for v in v2_all)

        # Optimized Linear Magma Counter-example Search (x*y = ax + by + c)
        def get_lin_poly(t):
            coeffs, k_terms = {}, []
            def wk(n, lc, rc):
                if isinstance(n, str):
                    if n.isalpha(): coeffs[n] = coeffs.get(n, []) + [(lc, rc)]
                else:
                    k_terms.append((lc, rc)); wk(n[1], lc+1, rc); wk(n[2], lc, rc+1)
            wk(t, 0, 0); return coeffs, k_terms
        p1l_poly, p1r_poly = get_lin_poly(t1[0]), get_lin_poly(t1[1])
        p2l_poly, p2r_poly = get_lin_poly(t2[0]), get_lin_poly(t2[1])
        def eval_poly(poly, a, b, p, ap, bp):
            cw, ck = {v: sum(ap[lc]*bp[rc] for lc, rc in ts)%p for v, ts in poly[0].items()}, sum(ap[lc]*bp[rc] for lc, rc in poly[1])%p
            return cw, ck
        for p_val in [2, 3, 5, 7, 11, 13, 17, 19, 23, 31]:
            ap, bp = [1]*12, [1]*12
            for a, b in itertools.product(range(p_val), repeat=2):
                for i in range(1, 12): ap[i], bp[i] = (ap[i-1]*a)%p_val, (bp[i-1]*b)%p_val
                c1l, k1l = eval_poly(p1l_poly, a, b, p_val, ap, bp); c1r, k1r = eval_poly(p1r_poly, a, b, p_val, ap, bp)
                if all(c1l.get(v, 0) == c1r.get(v, 0) for v in v1_all) and k1l == k1r:
                    c2l, k2l = eval_poly(p2l_poly, a, b, p_val, ap, bp); c2r, k2r = eval_poly(p2r_poly, a, b, p_val, ap, bp)
                    if not (all(c2l.get(v, 0) == c2r.get(v, 0) for v in v2_all) and k2l == k2r): return 0.001

        random.seed(42); sat1, n_samp = 0, 0
        v1_v, v2_v = sorted(list(v1_all)), sorted(list(v2_all))
        def get_magmas(t1_v):
            for i in range(16): yield [[(i>>(2*r+c))&1 for c in range(2)] for r in range(2)]
            yield [[(r ^ c) for c in range(4)] for r in range(4)] # XOR magma
            yield [[(r & c) for c in range(4)] for r in range(4)] # AND magma
            yield [[(r | c) for c in range(4)] for r in range(4)] # OR magma
            for n in [2, 3]:
                for a,b,k,q in itertools.product(range(n), repeat=4): yield [[(a*r+b*c+q*r*c+k)%n for c in range(n)] for r in range(n)]
            for op in [lambda x,y: x&y, lambda x,y: x|y, lambda x,y: x^y, lambda x,y: int(x and not y)]: yield [[op(r, c) for c in range(2)] for r in range(2)]
            yield [[max(r, c) for c in range(3)] for r in range(3)]
            yield [[min(r, c) for c in range(3)] for r in range(3)]
            for n in [2, 3, 4]:
                yield [[(r-c)%n for c in range(n)] for r in range(n)]
                yield [[(r*c)%n for c in range(n)] for r in range(n)]
                yield [[(r+1)%n for _ in range(n)] for r in range(n)]
                yield [[(c+1)%n for c in range(n)] for _ in range(n)]
                if n == 3: # Specialized Commutative Magmas
                    for v in itertools.product(range(3), repeat=6):
                        m = [[0]*3 for _ in range(3)]; i = 0
                        for r in range(3):
                            for c in range(r, 3): m[r][c] = m[c][r] = v[i]; i += 1
                        yield m
                yield [[(r*r+c)%n for c in range(n)] for r in range(n)]
                yield [[(r*c*c+1)%n for c in range(n)] for r in range(n)]
                yield [[(r+c+r*c)%n for c in range(n)] for r in range(n)]
                yield [[r for _ in range(n)] for r in range(n)]
                yield [[c for c in range(n)] for _ in range(n)]
            yield [[(r+1)%3 if r==c else r for c in range(3)] for r in range(3)] # Non-idempotent
            yield [[(r*r+c)%4 for c in range(4)] for r in range(4)]
            yield [[0,2,1],[2,1,0],[1,0,2]] # Steiner Triple System 3x3
            # S3 Cayley Table (Non-abelian group)
            yield [[0,1,2,3,4,5],[1,0,4,5,2,3],[2,5,0,4,3,1],[3,4,5,0,1,2],[4,3,1,2,5,0],[5,2,3,1,0,4]]
            # Non-associative loop of order 5
            yield [[0,1,2,3,4],[1,0,4,2,3],[2,3,0,4,1],[3,4,1,0,2],[4,2,3,1,0]]
            for sz in [2, 3, 4]:
                yield [[(r+c)%sz for c in range(sz)] for r in range(sz)]
                for _ in range(8): yield [[random.randint(0, sz-1) for _ in range(sz)] for _ in range(sz)]
            v_l = sorted(list(t1_v))
            v2_l_local = sorted(list(v2_all))
            if 0 < len(v_l) <= 4:
                v_m = {v: i for i, v in enumerate(v_l)}
                v2_m = {v: i for i, v in enumerate(v2_l_local)}
                def ev_h(n, vs, t, vm):
                    if isinstance(n, str): return vs[vm[n]] if n in vm else 0
                    return t[ev_h(n[1], vs, t, vm)][ev_h(n[2], vs, t, vm)]
                def sc(t):
                    sz, n_v = len(t), len(v_l)
                    limit, viol1 = 256, 0
                    if sz**n_v <= limit: viol1 = sum(ev_h(t1[0], vs, t, v_m) != ev_h(t1[1], vs, t, v_m) for vs in itertools.product(range(sz), repeat=n_v))
                    else: viol1 = sum(ev_h(t1[0], [random.randint(0, sz-1) for _ in range(n_v)], t, v_m) != ev_h(t1[1], [random.randint(0, sz-1) for _ in range(n_v)], t, v_m) for _ in range(limit))
                    if viol1 > 0: return 1000 + viol1
                    n_v2, viol2 = len(v2_l_local), 0
                    if sz**n_v2 <= limit: viol2 = sum(ev_h(t2[0], vs, t, v2_m) != ev_h(t2[1], vs, t, v2_m) for vs in itertools.product(range(sz), repeat=n_v2))
                    else: viol2 = sum(ev_h(t2[0], [random.randint(0, sz-1) for _ in range(n_v2)], t, v2_m) != ev_h(t2[1], [random.randint(0, sz-1) for _ in range(n_v2)], t, v2_m) for _ in range(limit))
                    return 0 if viol2 > 0 else 500
                for sz in [3, 4]:
                    restarts = 24 if sz == 3 else 12
                    steps = 100 if sz == 3 else 200
                    for _ in range(restarts):
                        tbl = [[random.randint(0, sz-1) for _ in range(sz)] for _ in range(sz)]
                        cur_s = sc(tbl)
                        if cur_s == 0:
                            yield tbl; continue
                        for _ in range(steps):
                            if cur_s == 0: break
                            r, c = random.randint(0, sz-1), random.randint(0, sz-1); old = tbl[r][c]
                            tbl[r][c] = random.randint(0, sz-1); new_s = sc(tbl)
                            if new_s <= cur_s: cur_s = new_s
                            else: tbl[r][c] = old
                        if cur_s <= 500: yield tbl
        r_sat, r_cnt = 0, 0
        v_l = sorted(list(v1_all | v2_all))
        for si in range(50):
            rng = random.Random(si + 1000)
            for mod in [2147483647, 2147483579, 2147483629]:
                p = [rng.randint(1, mod-1) for _ in range(5)]
                v_m = {v: rng.randint(0, mod-1) for v in v_l}
                for dual in [False, True]:
                    def ev_r(n):
                        if isinstance(n, str): return v_m.get(n, 17)
                        ln, rn = (ev_r(n[2]), ev_r(n[1])) if dual else (ev_r(n[1]), ev_r(n[2]))
                        return (ln * p[0] + rn * p[1] + ln * rn * p[2] + (ln**2) * p[3] + (rn**2) * p[4]) % mod
                    if ev_r(t1[0]) == ev_r(t1[1]):
                        r_cnt += 1
                        if ev_r(t2[0]) == ev_r(t2[1]): r_sat += 1
                        else: return 0.001
        r_sc = r_sat / r_cnt if r_cnt > 0 else 0.5

        for tbl in get_magmas(v1_all):
            tables = tbl if isinstance(tbl, (tuple, list)) and len(tbl) > 0 and isinstance(tbl[0], list) and isinstance(tbl[0][0], list) else [tbl]
            for table in tables:
                for tb in [table, [list(r) for r in zip(*table)]]:
                    n_samp += 1
                    if check(t1, v1_v, tb):
                        sat1 += 1
                        if not check(t2, v2_v, tb): return 0.001

        base = 0.999 if sat1 == 0 else (0.65 + 0.34 * (sat1 / float(n_samp)) if n_samp > 0 else 0.5)
        def get_p(t, v_a):
            def cnt(tr, v):
                if isinstance(tr, str): return 1 if tr == v else 0
                return cnt(tr[1], v) + cnt(tr[2], v)
            return sum(1 for v in v_a if (cnt(t[0], v) + cnt(t[1], v)) % 2 != 0)
        p1, p2, sh_rat = get_p(t1, v1_all), get_p(t2, v2_all), (len(v1_all & v2_all) / len(v1_all | v2_all) if (v1_all | v2_all) else 1.0)
        def m(p, t): return match(p, t, {}) or match((p[1], p[0]), t, {})
        p_a, p_c, p_i = (('*', ('*', 'a', 'b'), 'c'), ('*', 'a', ('*', 'b', 'c'))), (('*', 'a', 'b'), ('*', 'b', 'a')), (('*', 'a', 'a'), 'a')
        p_ld = (('*', 'a', ('*', 'b', 'c')), ('*', ('*', 'a', 'b'), ('*', 'a', 'c')))
        p_rd = (('*', ('*', 'a', 'b'), 'c'), ('*', ('*', 'a', 'c'), ('*', 'b', 'c')))
        p_lp, p_rp = (('*', 'a', 'b'), 'a'), (('*', 'a', 'b'), 'b')
        p_le = (('*', 'a', ('*', 'b', 'c')), ('*', 'b', ('*', 'a', 'c')))
        p_re = (('*', ('*', 'a', 'b'), 'c'), (('*', 'a', 'c'), 'b'))
        p_m, p_cn = (('*', ('*', 'a', 'b'), ('*', 'c', 'd')), ('*', ('*', 'a', 'c'), ('*', 'b', 'd'))), (('*', 'a', 'b'), 'c')
        p_f, p_la, p_ra = (('*', 'a', ('*', 'b', 'a')), ('*', ('*', 'a', 'b'), 'a')), (('*', 'a', ('*', 'a', 'b')), ('*', ('*', 'a', 'a'), 'b')), (('*', ('*', 'a', 'b'), 'b'), ('*', 'a', ('*', 'b', 'b')))
        p_inv, p_jo = (('*', 'a', ('*', 'b', 'a')), 'b'), (('*', ('*', 'a', 'b'), ('*', 'a', 'a')), ('*', 'a', ('*', 'b', ('*', 'a', 'a'))))
        p_mo, p_pa = (('*', ('*', 'z', 'x'), ('*', 'y', 'z')), ('*', ('*', 'z', ('*', 'x', 'y')), 'z')), (('*', ('*', 'a', 'a'), 'a'), ('*', 'a', ('*', 'a', 'a')))
        p_pm, p_rr, p_lr = (('*', ('*', 'a', 'b'), 'c'), ('*', ('*', 'c', 'b'), 'a')), (('*', ('*', 'a', 'b'), 'b'), 'a'), (('*', 'a', ('*', 'a', 'b')), 'b')
        p_abs1, p_abs2 = (('*', 'a', ('*', 'a', 'b')), 'a'), (('*', ('*', 'b', 'a'), 'b'), 'b')
        p_bol, p_circ = (('*', 'a', ('*', 'b', ('*', 'a', 'c'))), ('*', ('*', 'a', ('*', 'b', 'a')), 'c')), (('*', ('*', 'a', 'b'), 'c'), ('*', ('*', 'b', 'c'), 'a'))
        def ab(t): return any(isinstance(l, tuple) and (l[1] == r or l[2] == r) for l, r in [(t[0], t[1]), (t[1], t[0])] if isinstance(r, str) and r.isalpha())
        is_vci1, is_vci2 = (c1l == c1r), (c2l == c2r)
        is_a1, is_c1, is_i1, is_ab1, is_ld1, is_rd1, is_lp1, is_rp1, is_le1, is_re1, is_m1, is_cn1, is_f1, is_la1, is_ra1, is_inv1, is_jo1, is_mo1, is_pa1, is_pm1, is_rr1, is_lr1 = m(p_a, t1), m(p_c, t1), m(p_i, t1), ab(t1), m(p_ld, t1), m(p_rd, t1), m(p_lp, t1), m(p_rp, t1), m(p_le, t1), m(p_re, t1), m(p_m, t1), m(p_cn, t1), m(p_f, t1), m(p_la, t1), m(p_ra, t1), m(p_inv, t1), m(p_jo, t1), m(p_mo, t1), m(p_pa, t1), m(p_pm, t1), m(p_rr, t1), m(p_lr, t1)
        is_a2, is_c2, is_i2, is_ab2, is_ld2, is_rd2, is_lp2, is_rp2, is_le2, is_re2, is_m2, is_cn2, is_f2, is_la2, is_ra2, is_inv2, is_jo2, is_mo2, is_pa2, is_pm2, is_rr2, is_lr2 = m(p_a, t2), m(p_c, t2), m(p_i, t2), ab(t2), m(p_ld, t2), m(p_rd, t2), m(p_lp, t2), m(p_rp, t2), m(p_le, t2), m(p_re, t2), m(p_m, t2), m(p_cn, t2), m(p_f, t2), m(p_la, t2), m(p_ra, t2), m(p_inv, t2), m(p_jo, t2), m(p_mo, t2), m(p_pa, t2), m(p_pm, t2), m(p_rr, t2), m(p_lr, t2)
        is_abs1, is_bol1, is_circ1 = (m(p_abs1, t1) or m(p_abs2, t1)), m(p_bol, t1), m(p_circ, t1)
        is_abs2, is_bol2, is_circ2 = (m(p_abs1, t2) or m(p_abs2, t2)), m(p_bol, t2), m(p_circ, t2)
        def get_sym(t):
            def rev(x):
                if isinstance(x, str): return x
                return ('*', rev(x[2]), rev(x[1]))
            return match(t, (rev(t[0]), rev(t[1])), {})
        is_sym1, is_sym2 = get_sym(t1), get_sym(t2)
        is_lin1 = all(count_var_occ(t1[0], v) == 1 and count_var_occ(t1[1], v) == 1 for v in v1_all)
        is_lin2 = all(count_var_occ(t2[0], v) == 1 and count_var_occ(t2[1], v) == 1 for v in v2_all)
        def get_bias(t):
            def d(x):
                if isinstance(x, str): return (1, 0) if x=='x' else (0, 0)
                l, r = d(x[1]), d(x[2])
                return (l[0]+r[0], l[1]+r[1]+1)
            b1l, b1r = d(t[0]), d(t[1])
            return (b1l[0]-b1r[0])
        bias1, bias2 = get_bias(t1), get_bias(t2)

        # Neural Manifold Alignment Score (NMAS) logic
        def get_nmas(t1, t2, v_l):
            if not v_l: return 0.5
            n_trials, score = 15, 0.0
            for i in range(n_trials):
                rng = random.Random(i + 42)
                func_type = i % 3
                w1, w2, b = [rng.uniform(-1.5, 1.5) for _ in range(3)]
                def ev_n(n, vs):
                    if isinstance(n, str): return vs.get(n, 0.1)
                    l, r = ev_n(n[1], vs), ev_n(n[2], vs)
                    val = l * w1 + r * w2 + b
                    if func_type == 0: return math.tanh(val)
                    if func_type == 1: return math.sin(val)
                    return max(-1.0, min(1.0, val))
                v_vals = {v: rng.uniform(-1, 1) for v in v_l}
                res1 = abs(ev_n(t1[0], v_vals) - ev_n(t1[1], v_vals))
                res2 = abs(ev_n(t2[0], v_vals) - ev_n(t2[1], v_vals))
                if res1 < 1e-10 and res2 > 1e-3: return -1.0 # Signal counter-example found
                if res1 < 1e-6: score += (1.0 if res2 < 1e-4 else 0.0)
                else: score += max(0, 1.0 - (res2 / (res1 + 1e-7)))
            return score / n_trials
        nmas_val = get_nmas(t1, t2, sorted(list(v1_all | v2_all)))
        if nmas_val < 0: return 0.001

        def get_geo_chaos(t1, t2, v_l):
            if not v_l: return 0.5
            score = 0
            for i in range(12):
                rng = random.Random(i + 888)
                v_map = {v: [rng.uniform(-1, 1) for _ in range(3)] for v in v_l}
                params = [rng.uniform(-1, 1) for _ in range(6)]
                def op(l, r):
                    cp = [l[1]*r[2]-l[2]*r[1], l[2]*r[0]-l[0]*r[2], l[0]*r[1]-l[1]*r[0]]
                    return [params[0]*cp[j] + params[1]*l[j] + params[2]*r[j] + params[3]*l[j]*r[j] + params[4]*(l[j]**2) + params[5]*(r[j]**2) for j in range(3)]
                def ev(n):
                    if isinstance(n, str): return v_map.get(n, [0,0,0])
                    return op(ev(n[1]), ev(n[2]))
                l1, r1, l2, r2 = ev(t1[0]), ev(t1[1]), ev(t2[0]), ev(t2[1])
                d1, d2 = sum((l1[j]-r1[j])**2 for j in range(3)), sum((l2[j]-r2[j])**2 for j in range(3))
                if d1 < 1e-11 and d2 > 1e-3: return -1.0 # Signal counter-example found
                if d1 < 1e-6: score += (1.0 if d2 < 1e-4 else 0.0)
                else: score += max(0, 1.0 - math.sqrt(d2 / (d1 + 1e-9)))
            return score / 12
        geo_chaos_val = get_geo_chaos(t1, t2, sorted(list(v1_all | v2_all)))
        if geo_chaos_val < 0: return 0.001
        def get_tp(t1, t2, v_l):
            if not v_l: return 0.5
            sc, R, D, rng = 0, 2, 3, random.Random(42)
            cp = [[[rng.uniform(-1,1) for _ in range(D)] for _ in range(R)] for _ in range(3)]
            def op(u, v):
                res = [0.0]*D
                for r in range(R):
                    d1, d2 = sum(u[i]*cp[0][r][i] for i in range(D)), sum(v[i]*cp[1][r][i] for i in range(D))
                    for i in range(D): res[i] += d1*d2*cp[2][r][i]
                return res
            def ev(n, vm):
                if isinstance(n, str): return vm[n]
                return op(ev(n[1], vm), ev(n[2], vm))
            for i in range(10):
                vm = {v: [rng.uniform(-1,1) for _ in range(D)] for v in v_l}
                l1, r1, l2, r2 = ev(t1[0], vm), ev(t1[1], vm), ev(t2[0], vm), ev(t2[1], vm)
                d1, d2 = sum((l1[j]-r1[j])**2 for j in range(D)), sum((l2[j]-r2[j])**2 for j in range(D))
                if d1 < 1e-9 and d2 > 1e-4: return -1.0
                sc += 1.0 if d1 < 1e-7 else max(0, 1.0 - math.sqrt(d2/(d1+1e-9)))
            return sc / 10
        tp_val = get_tp(t1, t2, sorted(list(v1_all | v2_all)))
        if tp_val < 0: return 0.001

        # Tensor Fit Score: Optimize a tensor model for law1 and check law2's loss.
        def get_tensor_fit_score(t1, t2, v_l, n_restarts=3, n_steps=15, n_samples=4, n_perturbs=4):
            if not v_l: return 0.5
            R, D, final_score = 2, 2, 0.0
            rng = random.Random(1337) # Fixed seed for reproducibility
            for _ in range(n_restarts):
                params = [[[rng.uniform(-1, 1) for _ in range(D)] for _ in range(R)] for _ in range(3)]
                def op(u, v, p):
                    res = [0.0] * D
                    for r in range(R):
                        d1 = sum(u[i] * p[0][r][i] for i in range(D)); d2 = sum(v[i] * p[1][r][i] for i in range(D))
                        for i in range(D): res[i] += d1 * d2 * p[2][r][i]
                    return [math.tanh(x) for x in res] # Add non-linearity
                def evaluate_law_loss(t, vm, p):
                    def ev(n):
                        if isinstance(n, str): return vm.get(n, [0.1] * D)
                        return op(ev(n[1]), ev(n[2]), p)
                    l, r = ev(t[0]), ev(t[1])
                    return sum((l[j] - r[j])**2 for j in range(D))
                vms = [{v: [rng.uniform(-1, 1) for _ in range(D)] for v in v_l} for _ in range(n_samples)]
                def calculate_avg_loss(t, p): return sum(evaluate_law_loss(t, vm, p) for vm in vms) / n_samples
                best_params, best_loss1 = params, calculate_avg_loss(t1, params)
                for step in range(n_steps): # Simple hill-climbing optimization
                    if best_loss1 < 1e-12: break
                    candidates = [best_params]
                    for _ in range(n_perturbs):
                        scale = 0.5 * (1 - step/n_steps)
                        perturbed = [[[val + rng.uniform(-scale, scale) for val in vec] for vec in mat] for mat in best_params]
                        candidates.append(perturbed)
                    losses = [calculate_avg_loss(t1, p) for p in candidates]
                    min_loss_idx = min(range(len(losses)), key=losses.__getitem__)
                    if losses[min_loss_idx] < best_loss1:
                        best_loss1, best_params = losses[min_loss_idx], candidates[min_loss_idx]
                loss2 = calculate_avg_loss(t2, best_params)
                if best_loss1 < 1e-9 and loss2 > 1e-4: return -1.0 # Found counter-example
                ratio = loss2 / (best_loss1 + 1e-9)
                final_score += math.exp(-math.sqrt(ratio) * 0.15)
            return final_score / n_restarts if n_restarts > 0 else 0.5
        tensor_fit_val = get_tensor_fit_score(t1, t2, sorted(list(v1_all | v2_all)))
        if tensor_fit_val < 0: return 0.001

        def get_entanglement(t, vars):
            if not vars: return 0
            def paths(n, v, cur=""):
                if isinstance(n, str): return {cur} if n == v else set()
                return paths(n[1], v, cur+"L") | paths(n[2], v, cur+"R")
            e = 0
            for v in vars:
                p = paths(t[0], v) | paths(t[1], v)
                if len(p) > 1: e += 1
            return e / len(vars)
        ent1, ent2 = get_entanglement(t1, v1_all), get_entanglement(t2, v2_all)

        def get_vds(t, vars):
            def d(n, v, cur_d):
                if isinstance(n, str): return [cur_d] if n == v else []
                return d(n[1], v, cur_d+1) + d(n[2], v, cur_d+1)
            res = 0
            for v in vars:
                dl, dr = d(t[0], v, 0), d(t[1], v, 0)
                if not dl or not dr: res += 1.5
                else: res += abs(sum(dl)/len(dl) - sum(dr)/len(dr))
            return res / len(vars) if vars else 0
        vds1, vds2 = get_vds(t1, v1_all), get_vds(t2, v2_all)

        adj = diff_v_distinct_total*0.06 + diff_ops_total*0.02 + (d1-d2)*0.02 + diff_balance_v_distinct*-0.01 + diff_balance_v_total*-0.005 + diff_balance_ops_total*-0.005
        adj += (p1 - p2)*-0.01 + (sh_rat - 0.5)*0.15 + (imb1 - imb2)*0.04 + diff_redundancy*-0.02 + (len(p1_all)-len(p2_all))*0.01 + (vds1 - vds2) * -0.05
        adj += (is_a1-is_a2)*0.12 + (is_c1-is_c2)*0.12 + (is_i1-is_i2)*0.06 + (is_ab1-is_ab2)*0.10 + (is_m1-is_m2)*0.08 + (is_cn1-is_cn2)*0.18
        v_dens1, v_dens2 = (ops1_total / len(v1_all)) if v1_all else 0, (ops2_total / len(v2_all)) if v2_all else 0
        def get_par(t, v_l):
            res = 0
            for v in v_l:
                def walk(n):
                    if isinstance(n, str): return 1 if n == v else 0
                    return walk(n[1]) + walk(n[2])
                if walk(t[0]) % 2 == walk(t[1]) % 2: res += 1
            return res / len(v_l) if v_l else 1.0
        par1, par2 = get_par(t1, v1_all), get_par(t2, v2_all)
        adj += (is_ld1-is_ld2)*0.05 + (is_rd1-is_rd2)*0.05 + (is_lp1-is_lp2)*0.25 + (is_rp1-is_rp2)*0.25 + (is_le1-is_le2)*0.04 + (is_re1-is_re2)*0.04
        adj += (is_f1-is_f2)*0.04 + (is_la1-is_la2)*0.03 + (is_ra1-is_ra2)*0.03 + (is_lin1-is_lin2)*0.05 + (is_inv1-is_inv2)*0.10
        adj += diff_term_size_total * -0.012 + diff_unique_subterms_total * -0.025
        adj += subterm_legacy_ratio * 0.32 + subterm_novelty_ratio * -0.25 + (nmas_val - 0.5) * 0.48 + (geo_chaos_val - 0.5) * 0.18 + (tp_val - 0.5) * 0.18 + (tensor_fit_val - 0.75) * 0.45 + (ent1 - ent2) * 0.06 + (v_dens1 - v_dens2) * 0.06 + (par1 - par2) * 0.10
        def get_leaf_data(t):
            res = []
            def wk(n):
                if isinstance(n, str):
                    if n.isalpha(): res.append(n)
                else: wk(n[1]); wk(n[2])
            wk(t[0]); l_side = list(res); res = []
            wk(t[1]); r_side = list(res)
            def canonicalize(seq):
                m = {}; c = []
                for x in seq:
                    if x not in m: m[x] = len(m)
                    c.append(m[x])
                return tuple(c)
            return l_side, r_side, canonicalize(l_side), canonicalize(r_side)
        leaf1l, leaf1r, can1l, can1r = get_leaf_data(t1); leaf2l, leaf2r, can2l, can2r = get_leaf_data(t2)
        can_sim = 1.0 if (can1l == can2l and can1r == can2r) else 0.5 if (can1l == can2l or can1r == can2r) else 0.0
        l_sim = (len(set(leaf1l)&set(leaf2l))/len(set(leaf1l)|set(leaf2l)) if (set(leaf1l)|set(leaf2l)) else 1.0) + \
                (len(set(leaf1r)&set(leaf2r))/len(set(leaf1r)|set(leaf2r)) if (set(leaf1r)|set(leaf2r)) else 1.0)
        l_sim /= 2.0

        def get_srp_score(law_tuple, var_set, num_trials=50):
            if not var_set: return 1.0

            lhs, rhs = law_tuple
            total_overlap = 0.0

            # Cache original unique subterms (using analyze(term)[5]) for comparison
            us_lhs_orig = analyze(lhs)[5]
            us_rhs_orig = analyze(rhs)[5]

            # Convert var_set to a sorted list to ensure consistent ordering when creating var_map
            var_list = sorted(list(var_set))

            for _ in range(num_trials):
                # Generate a random permutation of variables from var_list
                perm = random.sample(var_list, k=len(var_list))
                # Create a mapping from original variables to their permuted counterparts
                var_map = {old_v: new_v for old_v, new_v in zip(var_list, perm)}

                # Apply the variable permutation to both sides of the law's AST
                lhs_permuted = apply(lhs, var_map)
                rhs_permuted = apply(rhs, var_map)

                # Analyze unique subterms of the permuted terms
                us_lhs_perm = analyze(lhs_permuted)[5]
                us_rhs_perm = analyze(rhs_permuted)[5]

                # Calculate a Jaccard-like index for subterm overlap between original and permuted terms.
                # This quantifies how much of the law's structure (its unique subterms) is preserved
                # after a random permutation of its variables.
                overlap_lhs = len(us_lhs_orig & us_lhs_perm) / len(us_lhs_orig | us_lhs_perm) if (us_lhs_orig | us_lhs_perm) else 1.0
                overlap_rhs = len(us_rhs_orig & us_rhs_perm) / len(us_rhs_orig | us_rhs_perm) if (us_rhs_orig | us_rhs_perm) else 1.0

                total_overlap += (overlap_lhs + overlap_rhs) / 2.0

            # The SRP score is the average overlap over all trials. Higher score means more resilience/symmetry.
            return total_overlap / num_trials if num_trials > 0 else 1.0

        # Calculate Structural Resilience to Permutation (SRP) for both laws
        srp1 = get_srp_score(t1, v1_all)
        srp2 = get_srp_score(t2, v2_all)

        def get_dp(t, v_a):
            ds = {v: [] for v in v_a}
            def wk(n, d):
                if isinstance(n, str): (ds[n].append(d) if n in ds else None)
                else: wk(n[1], d+1); wk(n[2], d+1)
            wk(t[0], 0); wk(t[1], 0)
            av = [sum(l)/len(l) for l in ds.values() if l]
            m = sum(av)/len(av) if av else 0
            std = (sum((x-m)**2 for x in av)/len(av))**0.5 if av else 0
            return m, std
        def get_internal_var_sub_similarity(law_tuple, var_set, num_trials=5):
            lhs, rhs = law_tuple

            # Get original unique subterms for the entire law
            original_us = analyze(lhs)[5] | analyze(rhs)[5]
            if not original_us: return 1.0 # Handle empty laws / no subterms

            # If there's only one unique variable, any substitution would be trivial or impossible to meaningfully compare.
            # Treat as maximally stable in this context.
            if len(var_set) < 2: return 1.0

            total_similarity = 0.0
            var_list = sorted(list(var_set)) # Consistent ordering

            # We perform a few trials of substitution
            for i in range(num_trials):
                # For each trial, pick a variable to substitute FROM and a variable to substitute TO
                v_orig_idx = (i * 13) % len(var_list) # pseudo-random selection
                v_orig = var_list[v_orig_idx]

                # Pick a target variable, potentially different from v_orig
                v_target_idx = ((i * 17) + 1) % len(var_list) # another pseudo-random selection
                v_target = var_list[v_target_idx]

                # Loop to find a distinct target variable if initial selection was the same
                while v_target == v_orig and len(var_list) > 1:
                    v_target_idx = (v_target_idx + 1) % len(var_list)
                    v_target = var_list[v_target_idx]

                # If after all attempts v_target is still v_orig, skip this trial.
                # This only happens if len(var_list) is 1, which should be caught by `len(var_set) < 2` earlier.
                if v_target == v_orig: continue

                # Create the substitution map
                var_map = {v_orig: v_target}

                # Apply the substitution to both sides of the law
                lhs_sub = apply(lhs, var_map)
                rhs_sub = apply(rhs, var_map)

                # Get unique subterms of the substituted law
                substituted_us = analyze(lhs_sub)[5] | analyze(rhs_sub)[5]

                # Calculate Jaccard similarity
                intersection = original_us & substituted_us
                union = original_us | substituted_us

                similarity = len(intersection) / len(union) if union else 1.0
                total_similarity += similarity

            return total_similarity / num_trials if num_trials > 0 else 1.0

        def get_v_fps(t, vars):
            res = []
            for v in vars:
                ps = []
                def find(n, p):
                    if isinstance(n, str):
                        if n == v: ps.append(p)
                    else: find(n[1], p+'L'); find(n[2], p+'R')
                find(t[0], ''); find(t[1], '')
                res.append(tuple(sorted(ps)))
            return sorted(res)

        # Calculate Internal Variable Substitution Similarity (IVSS) for both laws
        ivss1 = get_internal_var_sub_similarity(t1, v1_all)
        ivss2 = get_internal_var_sub_similarity(t2, v2_all)
        comp_rat = (ops2_total + 1) / (ops1_total + 1)
        v_fps1, v_fps2 = get_v_fps(t1, v1_all), get_v_fps(t2, v2_all)
        set_fps1, set_fps2 = set(v_fps1), set(v_fps2)
        v_fp_sim = len(set_fps1 & set_fps2) / len(set_fps1 | set_fps2) if (set_fps1 | set_fps2) else 1.0
        vdiv1, vdiv2 = (len(set_fps1) / len(v_fps1) if v_fps1 else 1.0), (len(set_fps2) / len(v_fps2) if v_fps2 else 1.0)

        def get_pdp_balance(t):
            def get_depths(n, current_depth=0):
                if isinstance(n, str):
                    return [current_depth] if n.isalpha() else []
                return get_depths(n[1], current_depth + 1) + get_depths(n[2], current_depth + 1)
            depths_l = sorted(get_depths(t[0]))
            depths_r = sorted(get_depths(t[1]))
            return depths_l == depths_r

        pdp_b1 = get_pdp_balance(t1)
        pdp_b2 = get_pdp_balance(t2)

        (m1, dp1), (m2, dp2) = get_dp(t1, v1_all), get_dp(t2, v2_all)
        v2_n = len(v2_all - v1_all); is_vk = (len(v1l - v1r) > 0) or (len(v1r - v1l) > 0)

        def get_side_switch(t):
            def walk(n, side):
                if isinstance(n, str): return {n: {side}} if side else {}
                l_v = walk(n[1], side if side else 'L'); r_v = walk(n[2], side if side else 'R')
                for k, v in r_v.items(): l_v[k] = l_v.get(k, set()) | v
                return l_v
            v_l, v_r = walk(t[0], None), walk(t[1], None)
            for v in (set(v_l.keys()) & set(v_r.keys())):
                if (('L' in v_l[v] and 'R' in v_r[v]) or ('R' in v_l[v] and 'L' in v_r[v])): return 1
            return 0
        sw1, sw2 = get_side_switch(t1), get_side_switch(t2)

        # Helper to canonicalize a single term based on its internal variables
        # E.g., 'x * (y * x)' would become ('*', 'v0', ('*', 'v1', 'v0'))
        def _canonicalize_single_term(term):
            var_map = {}
            next_idx = [0] # Use a list for mutable integer in closure, to generate unique variable names

            def _recursive_canonicalize(node):
                if isinstance(node, str):
                    if node.isalpha(): # It's a variable (e.g., 'x', 'y')
                        if node not in var_map:
                            var_map[node] = f'v{next_idx[0]}' # Assign a canonical name like 'v0', 'v1'
                            next_idx[0] += 1
                        return var_map[node]
                    return node # It's a non-alpha string (e.g., a constant '1'), keep as is

                # It's an operation tuple ('*', left, right)
                op = node[0] # The operator, usually '*'
                left_canon = _recursive_canonicalize(node[1])
                right_canon = _recursive_canonicalize(node[2])
                return (op, left_canon, right_canon)

            return _recursive_canonicalize(term)

        # Helper to get all unique canonical subterms of a given term
        # This function traverses the AST and canonicalizes each subterm independently
        def get_unique_canonical_subterms(term):
            canonical_subterms = set()

            def _traverse_and_collect(node):
                # Add the current node (canonicalized) to the set of unique subterms
                # Each subterm is canonicalized in its own context, ensuring structural equivalence
                canonical_subterms.add(_canonicalize_single_term(node))

                # If the current node is an operation (a tuple), recurse on its children
                if isinstance(node, tuple):
                    _traverse_and_collect(node[1])
                    _traverse_and_collect(node[2])
                # Base case: if it's a variable or constant (string), recursion stops here for children

            _traverse_and_collect(term)
            return canonical_subterms

        # Calculate canonical subterms for each side of both laws
        canon_us1l = get_unique_canonical_subterms(t1[0]) # Canonical subterms of law1's LHS
        canon_us1r = get_unique_canonical_subterms(t1[1]) # Canonical subterms of law1's RHS
        canon_us2l = get_unique_canonical_subterms(t2[0]) # Canonical subterms of law2's LHS
        canon_us2r = get_unique_canonical_subterms(t2[1]) # Canonical subterms of law2's RHS

        # Combine the canonical subterms for the entire law signature (union of LHS and RHS)
        canon_signature1 = canon_us1l | canon_us1r
        canon_signature2 = canon_us2l | canon_us2r

        # Calculate Jaccard similarity of the two law signatures
        # This metric quantifies the shared structural patterns between law1 and law2
        intersection_len = len(canon_signature1 & canon_signature2)
        union_len = len(canon_signature1 | canon_signature2)
        structural_signature_similarity = intersection_len / union_len if union_len > 0 else 0.0

        # Calculate canonical subterm legacy and novelty ratios.
        # Legacy: What proportion of law2's structural components are present in law1?
        # Novelty: What proportion of law2's structural components are new?
        canon_sig2_len = len(canon_signature2)
        canonical_legacy = intersection_len / canon_sig2_len if canon_sig2_len > 0 else 0.0
        canonical_novelty = len(canon_signature2 - canon_signature1) / canon_sig2_len if canon_sig2_len > 0 else 0.0

        is_sl1, is_sl2 = (is_a1 and is_c1 and is_i1), (is_a2 and is_c2 and is_i2)
        def get_vpc(t):
            ps = []
            def wk(n, p):
                if isinstance(n, str): ps.append(p)
                else: wk(n[1], p+1); wk(n[2], p+1)
            wk(t[0], 0); wk(t[1], 0); return sum(ps)/len(ps) if ps else 0
        vpc1, vpc2 = get_vpc(t1), get_vpc(t2)
        def get_chdc(t, v_l):
            if not v_l: return 0.5
            v_m, x = {}, 0.618
            for v in v_l:
                v_vec = []
                for _ in range(64): x = 3.92 * x * (1 - x); v_vec.append(1 if x > 0.5 else 0)
                v_m[v] = v_vec
            def ev(n):
                if isinstance(n, str): return v_m.get(n, [0]*64)
                l, r = ev(n[1]), ev(n[2]); return [l[i-1] ^ r[(i+1)%64] ^ (l[i] & r[i-2]) for i in range(64)]
            lv, rv = ev(t[0]), ev(t[1]); return sum(1 for i in range(64) if lv[i] == rv[i]) / 64
        def get_dom(t, v_all):
            if not v_all: return 0
            counts = [count_var_occ(t[0], v) + count_var_occ(t[1], v) for v in v_all]; tc = sum(counts)
            return max(counts) / tc if tc > 0 else 0
        chdc1, chdc2 = get_chdc(t1, v1_all), get_chdc(t2, v2_all); dom1, dom2 = get_dom(t1, v1_all), get_dom(t2, v2_all)
        adj += (is_sym1 - is_sym2) * 0.06 + (abs(bias1) - abs(bias2)) * -0.04 + structural_signature_similarity * 0.45 + canonical_legacy * 0.52 - canonical_novelty * 0.30
        adj += (is_jo1 - is_jo2) * 0.04 + (is_mo1 - is_mo2) * 0.04 + (is_vci1 - is_vci2) * 0.03 + (is_sl1 - is_sl2) * 0.05 + (is_pa1 - is_pa2) * 0.04
        adj += (is_abs1 - is_abs2) * 0.04 + (is_bol1 - is_bol2) * 0.03 + (is_circ1 - is_circ2) * 0.03
        adj += (srp1 - srp2) * 0.12 + (r_sc - 0.5) * 1.18 + (dp1 - dp2) * -0.05 + (m1 - m2) * -0.02 + (vpc1 - vpc2) * -0.03
        adj += (vbs1_score - vbs2_score) * -0.03 + ((vbs1_score == 0) - (vbs2_score == 0)) * -0.15 + (is_pm1 - is_pm2) * 0.05 + (is_rr1 - is_rr2) * 0.04 + (is_lr1 - is_lr2) * 0.04
        adj += (ivss2 - ivss1) * 0.24 + (sw1 - sw2) * 0.08 + (vdiv1 - vdiv2) * 0.05 + v_fp_sim * 0.15 + reach_score * 0.28
        adj += (chdc1 - chdc2) * 0.20 + (dom1 - dom2) * 0.04
        adj += (can_sim - 0.5) * 0.12 + (l_sim - 0.5) * 0.08
        # A balanced law (pdp_b1) is less likely to imply an unbalanced one (not pdp_b2).
        # An unbalanced law (not pdp_b1) is a strong constraint, and may imply a balanced one (pdp_b2).
        if pdp_b1 and not pdp_b2:
            adj -= 0.20
        elif not pdp_b1 and pdp_b2:
            adj += 0.05
        if v2_n > 0 and not is_vk: adj -= (0.35 + 0.15 * v2_n)
        res_p = base + adj
        if is_a1 and is_c1:
            if is_a2: res_p += 0.06
            if is_c2: res_p += 0.06
        if (is_lp1 or is_rp1) and not (is_lp2 or is_rp2): res_p += 0.08
        return max(0.001, min(0.999, res_p))
    except Exception as e: # Catch all exceptions for maximum robustness
        # Optional: Uncomment the following line for debugging purposes to see error details
        # print(f"Error in predict_implication_probability: {e}, Law1: '{law1}', Law2: '{law2}'")
        return 0.5
