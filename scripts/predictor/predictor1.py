import re
import random
import zlib
import math
from generated_triples import test_data
from typing import Any, Dict, List, Tuple, Optional

def predict_implication_probability(law1: str, law2: str) -> float:
    """
    Predicts the probability that law1 implies law2 in a magma using recursive
    substitution matching and universal law detection, augmented with structural
    feature analysis and a refined boolean algebra model checker.
    """
    def parse_term(s):
        s = s.replace(" ", "")
        # Remove outermost balanced parentheses if they enclose the entire term
        while s.startswith('(') and s.endswith(')'):
            depth, is_balanced = 0, True
            # Check up to len-2 to ensure inner part is not empty and fully enclosed
            for i in range(len(s) - 1):
                if s[i] == '(': depth += 1
                elif s[i] == ')': depth -= 1
                if depth == 0: # Found a matching outer parenthesis before the end
                    is_balanced = False
                    break
            if is_balanced: s = s[1:-1] # If balanced throughout, then outer parens are redundant
            else: break # Not fully enclosed by balanced parentheses

        # Find the main '*' operator at depth 0
        depth = 0
        for i in range(len(s) - 1, -1, -1): # Iterate from right to left to find outermost operator
            if s[i] == ')': depth += 1
            elif s[i] == '(': depth -= 1
            elif s[i] == '*' and depth == 0:
                return ['*', parse_term(s[:i]), parse_term(s[i+1:])]
        return s # Must be a variable

    def get_vars(tree):
        if isinstance(tree, str): return {tree}
        # Ensure it's a list and has the expected structure
        if isinstance(tree, list) and len(tree) == 3 and tree[0] == '*':
            return get_vars(tree[1]) | get_vars(tree[2])
        return set() # Fallback for unexpected tree structures

    def count_var_occurrences(tree):
        if isinstance(tree, str): return 1
        if isinstance(tree, list) and len(tree) == 3 and tree[0] == '*':
            return count_var_occurrences(tree[1]) + count_var_occurrences(tree[2])
        return 0 # Should not happen for well-formed terms

    def count_vars_per_side(tree):
        counts = {}
        def _walk(t):
            if isinstance(t, str):
                counts[t] = counts.get(t, 0) + 1
            elif isinstance(t, list) and len(t) == 3:
                _walk(t[1])
                _walk(t[2])
        _walk(tree)
        return counts

    # Helper to extract all unique subterms from a given tree, represented as strings
    def get_all_subterms_as_strings(tree):
        # We use string representation for subterms to allow them to be stored in sets
        # and compared for exact structural matches (variable names included).
        subterms = {str(tree)} # Add the root term itself
        if isinstance(tree, list) and len(tree) == 3 and tree[0] == '*':
            subterms.update(get_all_subterms_as_strings(tree[1]))
            subterms.update(get_all_subterms_as_strings(tree[2]))
        return subterms

    def get_depth(tree):
        if isinstance(tree, str): return 1
        if isinstance(tree, list) and len(tree) == 3 and tree[0] == '*':
            return 1 + max(get_depth(tree[1]), get_depth(tree[2]))
        return 0 # Should not happen for well-formed terms

    def substitute(t, m):
        if isinstance(t, str): return m.get(t, t)
        return ['*', substitute(t[1], m), substitute(t[2], m)]

    # Function for canonicalizing variable names in a tree
    # This assigns _v0, _v1, ... to variables based on their first appearance in a traversal.
    def get_canonical_tree(tree):
        var_map = {}
        next_var_idx = 0

        def _canonicalize_recursive(sub_tree):
            nonlocal next_var_idx
            if isinstance(sub_tree, str): # It's a variable
                if sub_tree not in var_map:
                    var_map[sub_tree] = f'_v{next_var_idx}'
                    next_var_idx += 1
                return var_map[sub_tree]
            elif isinstance(sub_tree, list) and len(sub_tree) == 3 and sub_tree[0] == '*':
                # Deep copy to avoid modifying original tree and ensure consistent canonicalization
                return ['*', _canonicalize_recursive(sub_tree[1]), _canonicalize_recursive(sub_tree[2])]
            return sub_tree # Should not happen for valid terms, but for robustness

        return _canonicalize_recursive(tree)

    # Function to convert a canonical tree to a string for hashing
    # This provides a unique string representation for a given structure.
    def tree_to_canonical_string(tree):
        if isinstance(tree, str):
            return tree
        elif isinstance(tree, list) and len(tree) == 3 and tree[0] == '*':
            # Parentheses are critical for preserving structure in string form
            return f"({tree_to_canonical_string(tree[1])} * {tree_to_canonical_string(tree[2])})"
        return str(tree) # Fallback for unexpected structures

    def apply_substitution_to_tree(tree, var_map):
        """Applies a substitution map to a tree, ensuring canonical variables for consistency."""
        # First, ensure the tree itself uses canonical variables
        canonical_tree = get_canonical_tree(tree)
        # Apply the substitution using the existing 'substitute' function
        substituted_tree = substitute(canonical_tree, var_map)
        return substituted_tree

    # Helper to get all unique canonical subterm hashes from a given tree
    # This helps identify structural components independent of specific variable names.
    def get_all_canonical_subterm_hashes(tree):
        canonical_tree = get_canonical_tree(tree) # Canonicalize the entire tree first
        subterm_hashes = set()

        def _get_hashes_recursive(sub_tree):
            if isinstance(sub_tree, str):
                subterm_hashes.add(hash(sub_tree)) # Hash of canonical variable name
            elif isinstance(sub_tree, list) and len(sub_tree) == 3 and sub_tree[0] == '*':
                current_subterm_str = tree_to_canonical_string(sub_tree)
                subterm_hashes.add(hash(current_subterm_str))
                _get_hashes_recursive(sub_tree[1])
                _get_hashes_recursive(sub_tree[2])
            # No explicit return value needed, as subterm_hashes is modified by side effect

        _get_hashes_recursive(canonical_tree)
        return subterm_hashes

    def get_spectral_signature(tree):
        """Calculates the eigenvalues of the graph Laplacian of a term tree."""
        try:
            import numpy as np
        except ImportError:
            return [] # Fallback if numpy is not available

        nodes, edges = [], []
        def build_graph(t, parent_idx=None):
            node_idx = len(nodes)
            nodes.append(str(t) if isinstance(t, str) else f'*_{node_idx}')
            if parent_idx is not None: edges.append((parent_idx, node_idx))
            if isinstance(t, list) and len(t) == 3:
                build_graph(t[1], node_idx); build_graph(t[2], node_idx)
        build_graph(tree)

        n = len(nodes)
        if n <= 1: return [0.0] * n

        adj = np.zeros((n, n), dtype=int)
        for i, j in edges: adj[i, j] = adj[j, i] = 1

        degrees = np.sum(adj, axis=1)
        laplacian = np.diag(degrees) - adj
        eigenvalues = np.linalg.eigvalsh(laplacian)
        return sorted(eigenvalues.tolist())

    def get_law_features(law_str):
        parts = law_str.split('=')
        L_str, R_str = parts[0].strip(), parts[1].strip()
        L_tree, R_tree = parse_term(L_str), parse_term(R_str)

        vars_L = get_vars(L_tree)
        vars_R = get_vars(R_tree)
        all_vars = vars_L | vars_R

        subterms_L = get_all_subterms_as_strings(L_tree)
        subterms_R = get_all_subterms_as_strings(R_tree)

        def get_all_paths(tree):
            paths = set()
            def _walk(t, p):
                if isinstance(t, str): paths.add(p)
                elif isinstance(t, list) and len(t) == 3:
                    _walk(t[1], p + 'L')
                    _walk(t[2], p + 'R')
            _walk(tree, '')
            return paths

        def get_path_moments(tree):
            depths = []
            def _walk(t, d):
                if isinstance(t, str): depths.append(d)
                elif isinstance(t, list) and len(t) == 3:
                    _walk(t[1], d + 1); _walk(t[2], d + 1)
            _walk(tree, 0)
            if not depths: return 0, 0, 0
            avg = sum(depths) / len(depths)
            var = sum((x - avg)**2 for x in depths) / len(depths)
            skew = sum((x - avg)**3 for x in depths) / len(depths)
            return avg, var, skew

        def get_torsion(t1, t2):
            def _seq(t):
                if isinstance(t, str): return [t]
                if isinstance(t, list) and len(t) == 3: return _seq(t[1]) + _seq(t[2])
                return []
            s1, s2 = _seq(t1), _seq(t2)
            if not s1 or not s2 or len(s1) != len(s2): return 0
            try: return sum(abs(i - s2.index(v)) for i, v in enumerate(s1) if v in s2)
            except: return 0

        def get_dipole(tree):
            d = [0]
            def _w(t, s):
                if isinstance(t, str): d[0] += s
                elif isinstance(t, list) and len(t) == 3: _w(t[1], s - 1); _w(t[2], s + 1)
            _w(tree, 0); return d[0]

        feats = {
            'L_tree': L_tree, 'R_tree': R_tree,
            'paths_L': get_all_paths(L_tree),
            'paths_R': get_all_paths(R_tree),
            'var_counts_L': count_vars_per_side(L_tree),
            'var_counts_R': count_vars_per_side(R_tree),
            'num_unique_vars': len(all_vars),
            'num_occ_L': count_var_occurrences(L_tree),
            'num_occ_R': count_var_occurrences(R_tree),
            'num_ops_L': L_str.count('*'),
            'num_ops_R': R_str.count('*'),
            'depth_L': get_depth(L_tree),
            'depth_R': get_depth(R_tree),
            'all_vars': all_vars,
            'subterms_L_str': subterms_L, # Store sets of string-represented subterms
            'subterms_R_str': subterms_R,
            'num_unique_subterms_L': len(subterms_L),
            'num_unique_subterms_R': len(subterms_R),
            'num_common_subterms_LR': len(subterms_L.intersection(subterms_R)),
            'canonical_L_tree_str': tree_to_canonical_string(get_canonical_tree(L_tree)),
            'canonical_R_tree_str': tree_to_canonical_string(get_canonical_tree(R_tree)),
            'canonical_subterm_hashes_L': get_all_canonical_subterm_hashes(L_tree),
            'canonical_subterm_hashes_R': get_all_canonical_subterm_hashes(R_tree),
        }

        # --- Transformation Resonance Vector (TRV) ---
        META_SUBSTITUTIONS = [
            {'_v0': parse_term('(_v0 * _v0)')}, {'_v0': parse_term('_v1'), '_v1': parse_term('_v0')},
            {'_v0': parse_term('(_v0 * _v1)')}, {'_v0': parse_term('(_v1 * _v0)')},
            {'_v0': parse_term('_v2')}, {'_v0': parse_term('((_v0 * _v0) * _v0)')},
        ]
        trv = []
        for sub_map in META_SUBSTITUTIONS:
            L_prime = apply_substitution_to_tree(L_tree, sub_map)
            R_prime = apply_substitution_to_tree(R_tree, sub_map)
            canon_L_prime = tree_to_canonical_string(get_canonical_tree(L_prime))
            canon_R_prime = tree_to_canonical_string(get_canonical_tree(R_prime))
            trv.append(1.0 if canon_L_prime == canon_R_prime else 0.0)
        feats['transformation_response_vector'] = trv

        # --- Spectral Signatures ---
        feats['spec_L'] = get_spectral_signature(L_tree)
        feats['spec_R'] = get_spectral_signature(R_tree)

        # --- Crazy Harmonic & Torsional Probes ---
        feats['moments_L'], feats['moments_R'] = get_path_moments(L_tree), get_path_moments(R_tree)
        feats['torsion'] = get_torsion(L_tree, R_tree)
        feats['dipole_L'], feats['dipole_R'] = get_dipole(L_tree), get_dipole(R_tree)

        return feats

    def get_acausal_info_dynamics(law1_str, law2_str):
        """
        Calculates the informational gradient between two laws using a Kolmogorov
        complexity proxy (zlib compression). A positive gradient from law1 to law2
        suggests that law2 contains less new information given law1, than law1
        contains new information given law2, which is a signature of implication.
        This is 'acausal' as it relies on the static information content rather
        than a deductive process.
        """
        c1_bytes = law1_str.encode('utf-8')
        c2_bytes = law2_str.encode('utf-8')

        c1 = len(zlib.compress(c1_bytes))
        c2 = len(zlib.compress(c2_bytes))
        if c1 == 0 or c2 == 0: return 0.0

        c12 = len(zlib.compress(c1_bytes + b' <=> ' + c2_bytes))

        c2_given_1 = c12 - c1
        c1_given_2 = c12 - c2

        norm_c2_given_1 = c2_given_1 / c2
        norm_c1_given_2 = c1_given_2 / c1

        info_gradient = norm_c1_given_2 - norm_c2_given_1
        return info_gradient

    def get_law_type(feats):
        # Categorizes a law based on how variables are handled across the equality.
        is_trivial = feats['canonical_L_tree_str'] == feats['canonical_R_tree_str']
        if is_trivial: return 'TRIVIAL'

        vars_L = get_vars(feats['L_tree'])
        vars_R = get_vars(feats['R_tree'])

        if vars_L == vars_R:
            if feats['var_counts_L'] == feats['var_counts_R']:
                return 'PERMUTATION'  # e.g., associativity, commutativity
            else:
                return 'IDENTIFICATION' # e.g., idempotence (x*x=x)
        elif vars_R.issubset(vars_L) and vars_L != vars_R:
            return 'PROJECTION_L' # e.g. x*y=x
        elif vars_L.issubset(vars_R) and vars_L != vars_R:
            return 'PROJECTION_R' # e.g. x = x*y, an expansion law
        else: # Overlapping or disjoint variable sets
            return 'DEGENERACY' # e.g. x*y = z*x or x*x = y*y, implies strong constraints

    def match(pattern, expr, mapping):
        if isinstance(pattern, str):
            if pattern in mapping: return mapping[pattern] == expr
            mapping[pattern] = expr
            return True
        if isinstance(expr, str) or pattern[0] != expr[0]: return False
        return match(pattern[1], expr[1], mapping) and match(pattern[2], expr[2], mapping)

    def is_sub(p_l, p_r, e_l, e_r):
        # Check if (p_l = p_r) can transform into (e_l = e_r)
        # Attempt 1: (p_l -> e_l) and (p_r -> e_r)
        m1 = {}
        if match(p_l, e_l, m1) and match(p_r, e_r, m1): return True
        # Attempt 2: (p_l -> e_r) and (p_r -> e_l) - for symmetric laws or implication across equality
        m2 = {}
        if match(p_l, e_r, m2) and match(p_r, e_l, m2): return True
        return False

    def flatten(tree):
        if isinstance(tree, str): return [tree]
        if isinstance(tree, list) and len(tree) == 3: return flatten(tree[1]) + flatten(tree[2])
        return []

    def get_leftmost(tree):
        while isinstance(tree, list): tree = tree[1]
        return tree

    def get_rightmost(tree):
        while isinstance(tree, list): tree = tree[2]
        return tree

    def get_rewrites(t, L1, R1, vL1, vR1, target_vars):
        res = []
        def _m(p, r, vs, tree):
            m_base = {}
            if match(p, tree, m_base):
                missing = [v for v in vs if v not in m_base]
                if not missing:
                    res.append(substitute(r, m_base))
                elif target_vars and len(missing) == 1:
                    for v_sub in target_vars:
                        m = m_base.copy(); m[missing[0]] = v_sub
                        res.append(substitute(r, m))
        _m(L1, R1, vR1, t); _m(R1, L1, vL1, t)
        if isinstance(t, list):
            for lr in get_rewrites(t[1], L1, R1, vL1, vR1, target_vars): res.append(['*', lr, t[2]])
            for rr in get_rewrites(t[2], L1, R1, vL1, vR1, target_vars): res.append(['*', t[1], rr])
        return res

    def can_prove(L1, R1, L2, R2, target_vars, max_s=400):
        vL1, vR1 = get_vars(L1), get_vars(R1)
        vL, vR = {str(L2): L2}, {str(R2): R2}
        qL, qR = [str(L2)], [str(R2)]
        for i in range(max_s):
            if i < len(qL):
                curr = vL[qL[i]]
                for nxt in get_rewrites(curr, L1, R1, vL1, vR1, target_vars):
                    s = str(nxt)
                    if s in vR: return True
                    if s not in vL: vL[s] = nxt; qL.append(s)
            if i < len(qR):
                curr = vR[qR[i]]
                for nxt in get_rewrites(curr, L1, R1, vL1, vR1, target_vars):
                    s = str(nxt)
                    if s in vL: return True
                    if s not in vR: vR[s] = nxt; qR.append(s)
        return False

    try:
        # Feature extraction
        law1_feats = get_law_features(law1)
        law2_feats = get_law_features(law2)

        tree1 = (law1_feats['L_tree'], law1_feats['R_tree'])
        tree2 = (law2_feats['L_tree'], law2_feats['R_tree'])

        # Pre-check: Direct structural implication using BFS rewriting
        target_vars = list(law2_feats['all_vars']) or ['x']
        if can_prove(tree1[0], tree1[1], tree2[0], tree2[1], target_vars):
            return 0.9999

        # New Pre-check: Direct structural specialization
        # If law1 directly specializes to law2 (via variable substitution)
        # This is a strong indicator of implication.
        if is_sub(tree1[0], tree1[1], tree2[0], tree2[1]):
            return 0.9999

        # Pre-check: Canonical structural identity of the laws
        # If law1 and law2 are structurally the same (ignoring variable names),
        # they imply each other perfectly. This is a very strong signal.
        canon_L1_str = law1_feats['canonical_L_tree_str']
        canon_R1_str = law1_feats['canonical_R_tree_str']
        canon_L2_str = law2_feats['canonical_L_tree_str']
        canon_R2_str = law2_feats['canonical_R_tree_str']

        if (canon_L1_str == canon_L2_str and canon_R1_str == canon_R2_str) or \
           (canon_L1_str == canon_R2_str and canon_R1_str == canon_L2_str):
            return 0.9999 # Structurally identical laws imply each other

        # New: Specific Logic for Associativity and Commutativity
        if (canon_L1_str == '(_v0 * (_v1 * _v2))' and canon_R1_str == '((_v0 * _v1) * _v2)') or \
           (canon_L1_str == '((_v0 * _v1) * _v2)' and canon_R1_str == '(_v0 * (_v1 * _v2))'):
            if flatten(tree2[0]) == flatten(tree2[1]): return 0.9999

        if (canon_L1_str == '(_v0 * _v1)' and canon_R1_str == '_v0') or \
           (canon_L1_str == '_v0' and canon_R1_str == '(_v0 * _v1)'):
            if get_leftmost(tree2[0]) == get_leftmost(tree2[1]): return 0.9999
        if (canon_L1_str == '(_v0 * _v1)' and canon_R1_str == '_v1') or \
           (canon_L1_str == '_v1' and canon_R1_str == '(_v0 * _v1)'):
            if get_rightmost(tree2[0]) == get_rightmost(tree2[1]): return 0.9999

        if (canon_L1_str == '(_v0 * _v1)' and canon_R1_str == '(_v1 * _v0)'):
            def is_shuffled(t1, t2):
                if t1 == t2: return True
                if isinstance(t1, list) and isinstance(t2, list):
                    return (is_shuffled(t1[1], t2[1]) and is_shuffled(t1[2], t2[2])) or \
                           (is_shuffled(t1[1], t2[2]) and is_shuffled(t1[2], t2[1]))
                return False
            if is_shuffled(tree2[0], tree2[1]): return 0.9999

        # Advanced Multi-Model Checker (Boolean + Affine Probes + Fixed Magmas)
        def holds_m(law, vars_list, m_type, params):
            L, R, n = law[0], law[1], 2
            if m_type in ('aff', 'quad'): n = params[3]
            elif m_type in ('fixed', 'rand'): n = params[1]
            elif m_type == 'explicit': n = params[0]
            if m_type == 'explicit':
                table = params[1]
            else:
                table = [0] * (n * n)
                for v1 in range(n):
                    for v2 in range(n):
                        if m_type == 'bool': val = (params[0] >> (v1 * 2 + v2)) & 1
                        elif m_type == 'aff': val = (params[0] * v1 + params[1] * v2 + params[2]) % n
                        elif m_type == 'quad': val = (params[0] * v1 + params[1] * v2 + params[2] * v1 * v2) % n
                        elif m_type == 'fixed':
                            if params[0] == 'max': val = max(v1, v2)
                            elif params[0] == 'min': val = min(v1, v2)
                            elif params[0] == 'first': val = v1
                            else: val = v2
                        else: val = ((v1 * 19 + v2 * 37 + params[0]) ^ (v1 * 7 + params[0])) % n
                        table[v1 * n + v2] = val
            def ev_m(t, e):
                if type(t) is str: return e[t]
                return table[ev_m(t[1], e) * n + ev_m(t[2], e)]
            num_vars = len(vars_list)
            if num_vars == 0: return ev_m(L, {}) == ev_m(R, {})
            total, limit = n ** num_vars, 512
            stride = (total // limit) + 1
            for i in range(min(total, limit)):
                m = i if total <= limit else (i * stride) % total
                env, temp = {}, m
                for v in vars_list:
                    env[v] = temp % n
                    temp //= n
                if ev_m(L, env) != ev_m(R, env): return False
            return True

        v1l, v2l = sorted(list(law1_feats['all_vars'])), sorted(list(law2_feats['all_vars']))
        models = [('bool', (i,)) for i in range(16)]
        for n in [3, 4, 5, 6]:
            models += [('aff', (a, b, c, n)) for a in range(n) for b in range(n) for c in range(n)]
        for n in [3, 4, 5]:
            models += [('quad', (a, b, c, n)) for a in range(n) for b in range(n) for c in range(1, n)]
        for n in [2, 3, 4, 5, 6]:
            for op in ['max', 'min', 'first', 'second']: models.append(('fixed', (op, n)))
        for n in [2, 3, 4, 5, 6]:
            models += [('rand', (s, n)) for s in range(25)]
        s3 = [0,1,2,3,4,5, 1,2,0,4,5,3, 2,0,1,5,3,4, 3,5,4,0,2,1, 4,3,5,1,0,2, 5,4,3,2,1,0]
        q8 = [0,1,2,3,4,5,6,7, 1,0,3,2,5,4,7,6, 2,3,1,0,6,7,5,4, 3,2,0,1,7,6,4,5, 4,5,7,6,1,0,2,3, 5,4,6,7,0,1,3,2, 6,7,4,5,3,2,1,0, 7,6,5,4,2,3,0,1]
        models += [('explicit', (6, s3)), ('explicit', (8, q8))]

        num_models_l1_holds = 0
        num_models_l2_holds = 0

        for m_type, m_params in models:
            l1_holds_in_m = holds_m(tree1, v1l, m_type, m_params)
            l2_holds_in_m = holds_m(tree2, v2l, m_type, m_params)

            if l1_holds_in_m:
                num_models_l1_holds += 1
                if not l2_holds_in_m:
                    return 0.0001

            if l2_holds_in_m:
                num_models_l2_holds += 1

        # --- Genetic Algorithm Counterexample Search ---
        # Evolve magmas that satisfy law1 and check if they also satisfy law2.
        # This searches for counterexamples in a different, more random space.
        def genetic_counterexample_search(tree1, vars1, tree2, vars2, magma_size=3, max_vars=4):
            if len(vars1) > max_vars or len(vars2) > max_vars: return 'INCONCLUSIVE'

            seed_str = str(tree1) + str(tree2)
            random.seed(hash(seed_str))

            POP_SIZE, GENS, MUT_RATE, CX_RATE, FIT_SAMPLES = 30, 25, 0.2, 0.7, 32

            def evaluate(term, env, table):
                if isinstance(term, str): return env[term]
                l = evaluate(term[1], env, table)
                r = evaluate(term[2], env, table)
                return table[l * magma_size + r]

            def check_law(law_tree, law_vars, table, num_samples=None):
                num_vars = len(law_vars)
                if num_vars == 0:
                    return 1.0 if evaluate(law_tree[0], {}, table) == evaluate(law_tree[1], {}, table) else 0.0

                total_assigns = magma_size ** num_vars
                to_check = range(total_assigns)
                if num_samples and total_assigns > num_samples:
                    to_check = random.sample(range(total_assigns), num_samples)

                holds = 0
                for i in to_check:
                    env, temp = {}, i
                    for v in law_vars:
                        env[v] = temp % magma_size
                        temp //= magma_size
                    if evaluate(law_tree[0], env, table) == evaluate(law_tree[1], env, table):
                        holds += 1
                return holds / len(to_check)

            pop = [[random.randint(0, magma_size - 1) for _ in range(magma_size**2)] for _ in range(POP_SIZE)]
            hof = [] # Hall of Fame for perfect models

            for _ in range(GENS):
                scores = [check_law(tree1, vars1, t, FIT_SAMPLES) for t in pop]
                for i, s in enumerate(scores):
                    if s == 1.0:
                        if check_law(tree1, vars1, pop[i]) == 1.0 and pop[i] not in hof:
                            hof.append(pop[i])
                if len(hof) >= 5: break

                # Tournament Selection
                new_pop = []
                for _ in range(POP_SIZE):
                    i1, i2 = random.sample(range(POP_SIZE), 2)
                    winner_idx = i1 if scores[i1] >= scores[i2] else i2
                    new_pop.append(list(pop[winner_idx]))
                pop = new_pop

                # Crossover and Mutation
                for i in range(0, POP_SIZE - 1, 2):
                    if random.random() < CX_RATE:
                        p1, p2 = pop[i], pop[i+1]
                        pt = random.randint(1, magma_size**2 - 1)
                        pop[i], pop[i+1] = p1[:pt] + p2[pt:], p2[:pt] + p1[pt:]

                for i in range(POP_SIZE):
                    if random.random() < MUT_RATE:
                        for _ in range(random.randint(1,3)): # Mutate 1 to 3 genes
                           idx_to_mut = random.randrange(magma_size**2)
                           pop[i][idx_to_mut] = random.randint(0, magma_size - 1)

            if not hof: return 'INCONCLUSIVE'

            for table in hof:
                if check_law(tree2, vars2, table) < 1.0: return 'COUNTEREXAMPLE_FOUND'

            return 'NO_COUNTEREXAMPLE_FOUND'

        ga_result = genetic_counterexample_search(tree1, v1l, tree2, v2l)
        if ga_result == 'COUNTEREXAMPLE_FOUND':
            return 0.0001

        total_models = len(models)

        # Probability Estimation based on model checking results
        if num_models_l1_holds == 0:
            # Law1 is contradictory in our model set, vacuously implies law2.
            prob = 0.999
        elif num_models_l2_holds == total_models:
            # Law2 is a tautology in our model set, implied by anything.
            prob = 0.999
        else:
            # No counter-example was found by fixed models or GA.
            # Confidence is based on number of models where law1 holds.
            # We use a Bayesian estimate with a Beta(1,1) prior.
            n = num_models_l1_holds

            # If GA search was successful and found no counterexamples, it's
            # strong evidence, equivalent to passing many more model checks.
            if ga_result == 'NO_COUNTEREXAMPLE_FOUND':
                n += 120 # Heuristic boost in confidence

            base_prob = (n + 1.0) / (n + 2.0)

            # --- Feature-based Adjustment ---
            # This section introduces heuristic adjustments to the base probability
            # based on structural features, inspired by 'tensor-like' analysis
            # of patterns and relationships within the algebraic expressions.
            adj_factor = 0.0

            # --- Acausal Information Dynamics Adjustment (Crazy Idea) ---
            # Compute informational gradient between canonical law representations.
            # A strong positive gradient is evidence for implication.
            canon_law1_str = f"{law1_feats['canonical_L_tree_str']} = {law1_feats['canonical_R_tree_str']}"
            canon_law2_str = f"{law2_feats['canonical_L_tree_str']} = {law2_feats['canonical_R_tree_str']}"
            info_gradient = get_acausal_info_dynamics(canon_law1_str, canon_law2_str)
            adj_factor += info_gradient * 0.1 # Weighting for the info gradient

            # 1. Variable Overlap Ratio between law1 and law2
            # High overlap might suggest a stronger relationship.
            all_vars_1 = law1_feats['all_vars']
            all_vars_2 = law2_feats['all_vars']
            if len(all_vars_1 | all_vars_2) > 0:
                var_overlap_ratio = len(all_vars_1.intersection(all_vars_2)) / len(all_vars_1 | all_vars_2)
                # Heuristic: 0.5 is neutral. Increased potential impact.
                var_overlap_adj = (var_overlap_ratio - 0.5) * 0.20
                adj_factor += var_overlap_adj
            else:
                var_overlap_ratio = 0.0

            complexity1 = (law1_feats['num_unique_vars'] + law1_feats['num_ops_L'] + law1_feats['num_ops_R'] +
                           law1_feats['depth_L'] + law1_feats['depth_R'])
            complexity2 = (law2_feats['num_unique_vars'] + law2_feats['num_ops_L'] + law2_feats['num_ops_R'] +
                           law2_feats['depth_L'] + law2_feats['depth_R'])
            adj_factor += min(0.2, max(-0.2, (complexity1 - complexity2) * 0.015))

            # --- Spectral and TRV Analysis Adjustment ---
            try:
                import numpy as np
                # Spectral Analysis
                spec1_L, spec1_R = np.array(law1_feats['spec_L']), np.array(law1_feats['spec_R'])
                spec2_L, spec2_R = np.array(law2_feats['spec_L']), np.array(law2_feats['spec_R'])

                def spectral_dist(s1, s2):
                    len1, len2 = len(s1), len(s2)
                    if len1 == 0 or len2 == 0: return 0.0
                    if len1 < len2: s1 = np.pad(s1, (0, len2 - len1))
                    if len2 < len1: s2 = np.pad(s2, (0, len1 - len2))
                    return np.linalg.norm(s1 - s2)

                imbalance1, imbalance2 = spectral_dist(spec1_L, spec1_R), spectral_dist(spec2_L, spec2_R)
                energy1 = max(np.max(spec1_L) if len(spec1_L)>0 else 0, np.max(spec1_R) if len(spec1_R)>0 else 0)
                energy2 = max(np.max(spec2_L) if len(spec2_L)>0 else 0, np.max(spec2_R) if len(spec2_R)>0 else 0)

                adj_factor += min(0.1, max(-0.1, (energy1 - energy2) * 0.05)) # Higher energy -> lower energy
                adj_factor += min(0.1, max(-0.1, (imbalance1 - imbalance2) * 0.05)) # Imbalanced -> balanced

                # Transformation Resonance Vector (TRV) Analysis
                trv1 = np.array(law1_feats.get('transformation_response_vector', []))
                trv2 = np.array(law2_feats.get('transformation_response_vector', []))
                if len(trv1) == len(trv2):
                     # A law with more symmetries (more 1s in TRV) is weaker.
                     # We expect a stronger law (fewer symmetries) to imply a weaker one.
                    adj_factor += (np.sum(trv2) - np.sum(trv1)) * 0.02
            except ImportError:
                pass # Fallback if numpy is not available

            subterms_law1_union = law1_feats['subterms_L_str'].union(law1_feats['subterms_R_str'])
            subterms_law2_union = law2_feats['subterms_L_str'].union(law2_feats['subterms_R_str'])
            subterm_coverage = 0.0
            if len(subterms_law2_union) > 0:
                subterm_coverage = len(subterms_law1_union.intersection(subterms_law2_union)) / len(subterms_law2_union)
                adj_factor += (subterm_coverage - 0.5) * 0.4

            adj_factor += (var_overlap_ratio * subterm_coverage) * 0.2
            if num_models_l1_holds > 0 and num_models_l1_holds == num_models_l2_holds:
                adj_factor += 0.15 # Strong similarity in model validity

            canon_subterms_law1_union = law1_feats['canonical_subterm_hashes_L'].union(law1_feats['canonical_subterm_hashes_R'])
            canon_subterms_law2_union = law2_feats['canonical_subterm_hashes_L'].union(law2_feats['canonical_subterm_hashes_R'])
            if len(canon_subterms_law2_union) > 0:
                canon_subterm_coverage = len(canon_subterms_law1_union.intersection(canon_subterms_law2_union)) / len(canon_subterms_law2_union)
                adj_factor += (canon_subterm_coverage - 0.5) * 0.4

            var_count_adj = min(0.1, max(-0.1, (law1_feats['num_unique_vars'] - law2_feats['num_unique_vars']) * 0.05))
            adj_factor += var_count_adj

            paths1, paths2 = law1_feats['paths_L'] | law1_feats['paths_R'], law2_feats['paths_L'] | law2_feats['paths_R']
            if paths2:
                adj_factor += (len(paths1.intersection(paths2)) / len(paths2) - 0.5) * 0.3

            # Structural op-density feature
            if law2_feats['num_ops_L'] + law2_feats['num_ops_R'] > law1_feats['num_ops_L'] + law1_feats['num_ops_R'] + 2:
                adj_factor -= 0.1

            # Harmonic Resonance and Torsional Flow Adjustments
            m1L, _, _ = law1_feats.get('moments_L', (0,0,0))
            m2L, _, _ = law2_feats.get('moments_L', (0,0,0))
            adj_factor += (m2L - m1L) * 0.012
            adj_factor += (law1_feats.get('torsion', 0) - law2_feats.get('torsion', 0)) * 0.004
            adj_factor += (abs(law1_feats.get('dipole_L', 0)) - abs(law2_feats.get('dipole_R', 0))) * 0.005

            prob = base_prob + adj_factor

            # --- Law Type Analysis ---
            # Introduce a powerful heuristic based on the structural type of the laws.
            # Certain types of laws (e.g., projections) are inherently stronger and more
            # likely to imply others.
            type1 = get_law_type(law1_feats)
            type2 = get_law_type(law2_feats)

            strength = {
                'PROJECTION_L': 5, 'DEGENERACY': 4, 'PROJECTION_R': 3,
                'IDENTIFICATION': 2, 'PERMUTATION': 1, 'TRIVIAL': 0
            }
            s1 = strength.get(type1, 2.5) # Default to mid-range
            s2 = strength.get(type2, 2.5)

            # A stronger law implying a weaker one is plausible. The reverse is not.
            type_adj = (s1 - s2) * 0.05
            if s1 < s2: # Heavier penalty for weak -> strong
                type_adj -= (s2 - s1) * 0.05

            # Specific high-impact adjustments for projections
            if type1 == 'PROJECTION_L' and type2 != 'TRIVIAL':
                type_adj += 0.1
            if type2 == 'PROJECTION_L' and type1 != 'PROJECTION_L':
                type_adj -= 0.15

            prob += type_adj

        # Ensure probability stays within valid bounds [0.0001, 0.9999]
        return max(0.0001, min(0.9999, prob))
    except Exception:
        # Fallback for any parsing or runtime errors, returning a neutral probability
        return 0.5

