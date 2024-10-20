from collections import Counter
from generate_eqs_list import count_vars

from forcer import *


def flatten_eq2(eq, ecache, preconds):
    if eq in ecache:
        return ecache[eq]
    if isinstance(eq, int):
        return eq
    l, r = eq
    l = flatten_eq2(l, ecache, preconds)
    r = flatten_eq2(r, ecache, preconds)
    tv = f't{len(preconds)}'
    preconds.append((l, r, tv))
    ecache[eq] = tv
    return tv


def rulify_eq2(eq):
    preconds = []
    ecache = {}
    l = flatten_eq2(eq[0], ecache, preconds)
    r = flatten_eq2(eq[1], ecache, preconds)
    return Rule(preconds, (l, r))

def natural_sort(l):
    convert = lambda text: int(text) if text.isdigit() else text.lower()
    alphanum_key = lambda key: [convert(c) for c in re.split('([0-9]+)', key)]
    return sorted(l, key=alphanum_key)

def proof_maker(proof, rule_id, lean_type, var_num, assump_count, def_types, types, do_clear = False):
    lean_proof = f'set_option linter.all false in\nset_option maxHeartbeats 4000000 in\ntheorem rule_{rule_id}_preserved'
    proof_steps = []
    my_reqs = []
    eq_name = {}
    clause_count = {}
    typeof = {}
    eq_use_cnt = Counter()
    for line in proof.split('\n'):
        if line.strip() == '' or line.startswith('%'):
            continue
        eqnum = line.split('.')[0]
        m = re.search(r'\[input (\w+)]', line)
        if m is not None:
            eq_name[eqnum] = m[1]
            continue
        m = re.search(r'\[(?:rectify|cnf transformation) (\d+)]', line)
        if m is not None:
            eq_name[eqnum] = eq_name[m[1]]
            continue
        eq_name[eqnum] = f'eq{eqnum}'
        m = re.match(r'\d+\. ([^[]+) \[([^\]]+)\]', line)
        statement, cproof = m[1], m[2]
        m = re.match(
            r'(?:(?:subsumption )?resolution|superposition|backward demodulation|forward demodulation) (\d+),(\d+)',
            cproof)
        if m is not None:
            eq_use_cnt[eq_name[m[1]]] += 1
            eq_use_cnt[eq_name[m[2]]] += 1
            continue
        m = re.match(
            r'(?:duplicate literal removal|equality resolution|trivial inequality removal|equality factoring) (\d+)',
            cproof)
        if m is not None:
            eq_use_cnt[eq_name[m[1]]] += 1
            continue
    for a, t in def_types:
        my_reqs.append(a)
        lean_proof += f' ({a} : {t})'
    for a, t in types:
        if a in eq_use_cnt:
            my_reqs.append(a)
            lean_proof += f' ({a} : {t})'
    lean_proof += f''' : {lean_type} := by
  by_contra! nh
  obtain ⟨{", ".join(f"sk{i}" for i in range(var_num))}, {", ".join(f"preserve_{i}" for i in range(assump_count))}⟩ := nh
  '''
    for line in proof.split('\n'):
        if line.strip() == '' or line.startswith('%'):
            continue
        if re.search(r'\[(?:rectify|cnf transformation|input) (\w+)]', line) is not None:
            continue
        eqnum = line.split('.')[0]
        m = re.match(r'\d+\. ([^[]+) \[([^\]]+)\]', line)
        if m is None:
            print(line)
        statement, proof = m[1], m[2]
        if statement == '$false':
            m = re.match(r'(?:subsumption )?resolution (\d+),(\d+)', proof)
            if m is not None:
                l, r = m[1], m[2]
                proof_steps.append(
                    f'subsumption {eq_name[r]} {eq_name[l]} -- {proof}')
                continue
            proof_steps.append(f'-- {proof}')
            continue

        clause_count[eqnum] = statement.count('|')
        lean_statement = statement

        old = ''
        while old != lean_statement:
            old = lean_statement
            lean_statement = re.sub(r'(\w+)\(([^,]+),([^,]+),([^,]+)\)', r'(\1 \2 \3 \4)', lean_statement, count=1)
        lean_statement = re.sub(r'\|', '∨', lean_statement)
        lean_statement = re.sub('!=', '≠', lean_statement)
        lean_statement = re.sub('~', '¬', lean_statement)
        lean_statement = re.sub(r'memold\((\w+)\)', r'memold \1', lean_statement)
        typeof[eqnum] = lean_statement
        variables = natural_sort({x for x in re.findall(r'[.\w]+', lean_statement) if x[0].isupper()})
        variables = f'({" ".join(variables)} : G) ' if variables else ''
        m = re.match(r'(?:subsumption )?resolution (\d+),(\d+)', proof)
        if m is not None:
            l, r = m[1], m[2]
            proof_steps.append(
                f'have eq{eqnum} {variables}: {lean_statement} := resolve {eq_name[l]} {eq_name[r]} -- {proof}')
            eq_use_cnt[eq_name[l]] -= 1
            eq_use_cnt[eq_name[r]] -= 1
            if do_clear and (eq_use_cnt[eq_name[l]] == 0 or eq_use_cnt[eq_name[r]] == 0):
                proof_steps.append(f'clear')
                if eq_use_cnt[eq_name[l]] == 0: proof_steps[-1] += f' {eq_name[l]}'
                if eq_use_cnt[eq_name[r]] == 0: proof_steps[-1] += f' {eq_name[r]}'
            continue
        m = re.match(r'superposition (\d+),(\d+)', proof)
        if m is not None:
            l, r = m[1], m[2]
            an = clause_count[eqnum] - clause_count[r] + 1
            if '∨' in typeof[r]:
                eqtype = typeof[r].split(' ∨')[0]
                if an > 1:
                    proof_steps.append(
                        f'have eq{eqnum} {variables}: {lean_statement} := Or.assoc{an} ({eq_name[r]}.imp_left (fun h : {eqtype} ↦ superpose h {eq_name[l]})) -- {proof}')
                else:
                    proof_steps.append(
                        f'have eq{eqnum} {variables}: {lean_statement} := {eq_name[r]}.imp_left (fun h : {eqtype} ↦ superpose h {eq_name[l]}) -- {proof}')
            else:
                proof_steps.append(
                    f'have eq{eqnum} {variables}: {lean_statement} := superpose {eq_name[r]} {eq_name[l]} -- {proof}')
            eq_use_cnt[eq_name[l]] -= 1
            eq_use_cnt[eq_name[r]] -= 1
            if do_clear and (eq_use_cnt[eq_name[l]] == 0 or eq_use_cnt[eq_name[r]] == 0):
                proof_steps.append(f'clear')
                if eq_use_cnt[eq_name[l]] == 0: proof_steps[-1] += f' {eq_name[l]}'
                if eq_use_cnt[eq_name[r]] == 0: proof_steps[-1] += f' {eq_name[r]}'
            continue
        m = re.match(r'(?:backward demodulation|forward demodulation) (\d+),(\d+)', proof)
        if m is not None:
            l, r = m[1], m[2]
            if variables == '':
                proof_steps.append(
                    f'have eq{eqnum} : {lean_statement} := Eq.mp (by simp only [{eq_name[r]}, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) {eq_name[l]} -- {proof}')
            else:
                proof_steps.append(
                    f'have eq{eqnum} : ∀ {variables}, {lean_statement} := Eq.mp (by simp only [{eq_name[r]}, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) {eq_name[l]} -- {proof}')
            eq_use_cnt[eq_name[l]] -= 1
            eq_use_cnt[eq_name[r]] -= 1
            if do_clear and (eq_use_cnt[eq_name[l]] == 0 or eq_use_cnt[eq_name[r]] == 0):
                proof_steps.append(f'clear')
                if eq_use_cnt[eq_name[l]] == 0: proof_steps[-1] += f' {eq_name[l]}'
                if eq_use_cnt[eq_name[r]] == 0: proof_steps[-1] += f' {eq_name[r]}'
            continue
        m = re.match(r'(?:duplicate literal removal|equality resolution|trivial inequality removal) (\d+)', proof)
        if m is not None:
            e = m[1]
            proof_steps.append(
                f'have eq{eqnum} {variables}: {lean_statement} := resolve {eq_name[e]} rfl -- {proof}')
            eq_use_cnt[eq_name[e]] -= 1
            if do_clear and eq_use_cnt[eq_name[e]] == 0: proof_steps.append(f'clear {eq_name[e]}')
            continue
        m = re.match(r'equality factoring (\d+)', proof)
        if m is not None:
            e = m[1]
            proof_steps.append(
                f'have eq{eqnum} {variables}: {lean_statement} := resolve {eq_name[e]} trans_resol -- {proof}')
            eq_use_cnt[eq_name[e]] -= 1
            if do_clear and eq_use_cnt[eq_name[e]] == 0: proof_steps.append(f'clear {eq_name[e]}')
            continue
        proof_steps.append(
            f'have eq{eqnum} {variables}: {lean_statement} := sorry -- {proof}')
        print('Not implemented', proof)
    return lean_proof + '\n  '.join(proof_steps), my_reqs


def main():
    eqid = input()
    eq = eqs[int(eqid) - 1]

    rules = load_file(f'data/forcing_rules/{eqid}.rules')
    for i, rule in enumerate(rulify_eq(eq)):
        rules[i + 1] = rule

    tptp = construct_tptp(rules)

    newline_two_spaces = '\n  '
    newline_four_spaces = '\n    '
    newline2 = '\n\n'

    #
    def_types = [('G', 'Type*'), ('a b c', 'G'), ('old', 'G → G → G → Prop'), ('new', 'G → G → G → Prop')]
    types = [('ac', 'a ≠ c'), ('bc', 'c ≠ b'), ('p3', '∀ X0, ¬ old a b X0'), ('p4XY', '∀ X1 X2, ¬ old X1 X2 c'),
                ('p4XZ', '∀ X1 X2, ¬ old X1 c X2'), ('p4YZ', '∀ X1 X2, ¬ old c X1 X2'), ('new_new', 'new a b c')]

    for i, x in enumerate(rules):
        types.append((f'old_{i}', x.to_lean('old')))
        types.append((f'prev_{i}', x.to_lean('new')))


    leandefs = []

    defs = [((), [('a', 'X'), ('b', 'Y'), ('c', 'Z')])] + [y for x in rules for y in
                                                                                    x.to_defs()]
    skolem_index = 0
    def_index = 0
    for i, (vars, d) in enumerate(defs):
        types.append((f'imp_new_{i+1}', f'∀ {" ".join(["X", "Y", "Z", *vars])}, {" ∨ ".join(lean_single_negated("old", x) for x in d)} ∨ new X Y Z'))
        skolemification = {}
        last_skolem = skolem_index
        for v in vars:
            skolemification[v] = f'sF{skolem_index}'
            def_types.append((f'sF{skolem_index}', 'G → G → G → G'))
            skolem_index += 1
        ld = f'let sP{def_index} (X Y Z) := '
        if vars:
            ld += '∃ ' + ' '.join(f'sF{i}' for i in range(last_skolem, skolem_index)) + ', '
        def_types.append((f'sP{def_index}', 'G → G → G → Prop'))
        thingy = ' ∧ '.join(lean_single('ps.R', [skolemification.get(x, x) for x in sk]) for sk in d)
        ld += thingy
        ld += newline_two_spaces
        if vars:
            ld += f'choose! {" ".join(f"sF{i}" for i in range(last_skolem, skolem_index))} hsP{def_index} using fun (X Y Z) (h : sP{def_index} X Y Z) ↦ h{newline_two_spaces}'
        else:
            ld += f'have hsP{def_index} (X Y Z) (h : sP{def_index} X Y Z) : {thingy} := h{newline_two_spaces}'
        ld += f'simp only [imp_and, imp_iff_not_or, forall_and] at hsP{def_index}{newline_two_spaces}'
        ld += f'obtain ⟨{", ".join(f"rule_def_{def_index}_{i}" for i in range(len(d)))}⟩ := hsP{def_index}{newline_two_spaces}'
        ld += f'simp_rw [or_comm] at {" ".join(f"rule_def_{def_index}_{i}" for i in range(len(d)))}'
        for i, x in enumerate(d):
            x = [f'({skolemification[y]} X Y Z)' if y in skolemification else y for y in x]
            types.append((f'rule_def_{def_index}_{i}', f'∀ (X Y Z : G), {lean_single("old", x)} ∨ ¬sP{def_index} X Y Z'))

        leandefs.append(ld)
        def_index += 1

    types.append(('new_imp', f'∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ {" ∨ ".join(f"sP{i} X Y Z" for i in range(len(leandefs)))}'))
    types.append(('imp_new_0', f'∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z'))

    # print(def_types)
    # print(types)

    leanproofs = []
    proof_reqs = {}

    for i, rule in enumerate(rules):
        inp = tptp
        for j in range(i):
            inp += f'fof(prev_{j}, axiom, {rules[j].to_tptp("new")}).'
        for j, v in enumerate(rule.to_tptp_negated('new')):
            inp += f'fof(preserve_{j}, negated_conjecture, {v}).\n'
        proof : str = subprocess.check_output(['/home/commandmaster/Downloads/vampire', '--proof_extra', 'full', '-av', 'off',
                                                   '--output_axiom_names', 'on',
                                                   '/proc/self/fd/0', '-t', '300'], input=inp.encode()).decode()
        lean_proof, my_reqs = proof_maker(proof, i, rule.to_lean('new'), rule.vars, len(rule.preconditions) + 1, def_types, types)
        proof_reqs[i] = my_reqs

        leanproofs.append(lean_proof)

    def_types.append(('memold', 'G → Prop'))
    types.extend([('old_mem1', '∀ (X Y Z), ¬old X Y Z ∨ memold X'),
                  ('old_mem2', '∀ (X Y Z), ¬old X Y Z ∨ memold Y'),
                  ('old_mem3', '∀ (X Y Z), ¬old X Y Z ∨ memold Z')])

    for memv in range(3):
        inp = tptp
        inp += f'fof(old_mem1, axiom, ! [X, Y, Z] : (~old(X, Y, Z) | memold(X))).\n'
        inp += f'fof(old_mem2, axiom, ! [X, Y, Z] : (~old(X, Y, Z) | memold(Y))).\n'
        inp += f'fof(old_mem3, axiom, ! [X, Y, Z] : (~old(X, Y, Z) | memold(Z))).\n'
        inp += f'fof(preserve_0, negated_conjecture, new(sk0, sk1, sk2)).\n'
        inp += f'fof(preserve_1, negated_conjecture, sk{memv} != a).\n'
        inp += f'fof(preserve_2, negated_conjecture, sk{memv} != b).\n'
        inp += f'fof(preserve_3, negated_conjecture, ~memold(sk{memv})).\n'
        inp += f'fof(preserve_4, negated_conjecture, sk{memv} != c).\n'
        # for j, v in enumerate(rule.to_tptp_negated('new')):
        #     inp += f'fof(preserve_{j}, negated_conjecture, {v}).\n'
        proof: str = subprocess.check_output(
            ['/home/commandmaster/Downloads/vampire', '--proof_extra', 'full', '-av', 'off',
             '--output_axiom_names', 'on',
             '/proc/self/fd/0', '-t', '60'], input=inp.encode()).decode()
        lean_proof, my_reqs = proof_maker(proof, f'finite_{memv}', f'∀ (X Y Z : G), ¬new X Y Z ∨ {"XYZ"[memv]} = a ∨ {"XYZ"[memv]} = b ∨ memold {"XYZ"[memv]} ∨ {"XYZ"[memv]} = c',
                                          3, 5, def_types, types)
        proof_reqs[f'finite_{memv}'] = my_reqs

        leanproofs.append(lean_proof)

    replacements = {'old': 'ps.R', 'memold': '(· ∈ ps.finsupp)', 'old_mem1': 'ps.mem_1', 'old_mem2': 'ps.mem_2',
                    'old_mem3': 'ps.mem_3'}
    for i in range(len(rules)):
        replacements[f'old_{i}'] = f'ps.rule_{i}'

    lean = f'''import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq{eqid}

{newline2.join(leanproofs)}

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  {newline_two_spaces.join(f"rule_{i} : {x.to_lean('R')}" for i, x in enumerate(rules))}
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp  

variable {{G : Type*}} (ps : PartialSolution G)

set_option linter.all false in
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ ps.R a b X0)
    (p4XY : ∀ X1 X2, ¬ ps.R X1 X2 c) (p4XZ : ∀ X1 X2, ¬ ps.R X1 c X2) (p4YZ : ∀ X1 X2, ¬ ps.R c X1 X2)
    : ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by classical
  {newline_two_spaces.join(leandefs)}

  let new (X Y Z) := ps.R X Y Z ∨ {" ∨ ".join(f"sP{i} X Y Z" for i in range(len(leandefs)))}
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  {newline_two_spaces.join(f"have imp_new_{i} (X Y Z) : _ → new X Y Z := " + "Or.inr ∘ " * i + "Or.inl" for i in range(len(leandefs)))}
  have imp_new_{len(leandefs)} (X Y Z) : _ → new X Y Z := {" ∘ ".join(["Or.inr"]*len(leandefs))}
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ {" ∨ ".join(f"sP{i} X Y Z" for i in range(len(leandefs)))} := id

  simp only [imp_iff_not_or] at imp_new_0
  {newline_two_spaces.join(f'simp only [not_and, not_exists, imp_iff_not_or, sP{i}, ← forall_or_right, or_assoc] at imp_new_{i+1}' for i in range(len(leandefs)))}
  simp only [imp_iff_not_or] at new_imp
  clear_value {" ".join(f"sP{i}" for i in range(len(leandefs)))} new

  {newline_two_spaces.join(f'have prev_{i} := rule_{i}_preserved ' + ' '.join(replacements.get(x, x) for x in proof_reqs[i]) for i in range(len(rules)))}

  exact ⟨{{
    R := new
    {newline_four_spaces.join(f'rule_{i} := prev_{i}' for i in range(len(rules)))}
    finsupp := ps.finsupp ∪ {{a, b, c}}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved {' '.join(replacements.get(x, x) for x in proof_reqs['finite_0'])}
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved {' '.join(replacements.get(x, x) for x in proof_reqs['finite_1'])}
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved {' '.join(replacements.get(x, x) for x in proof_reqs['finite_2'])}
  }}, by simp only [new_new, imp_iff_not_or, imp_new_0, implies_true, and_self]⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_not_mem_finset (ps.finsupp ∪ {{a, b}})).choose
    have hc : c ∉ _ := (Infinite.exists_not_mem_finset (ps.finsupp ∪ {{a, b}})).choose_spec
    (ps.adjoin a b c (by simp_all [eq_comm]) (by simp_all)
        (by simpa using h) (fun _ _ h ↦ by have := (ps.mem_3 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_2 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_1 _ _ _).neg_resolve_left h; simp_all)).choose

lemma PartialSolution.addArbitrary_covers [Infinite G] (a b : G) :
    ∃ c, (ps.addArbitrary a b).R a b c := by
  unfold addArbitrary
  split
  · assumption
  · generalize_proofs h1 h2 h3
    exact ⟨h1.choose, (h3 h2).choose_spec.1⟩

lemma PartialSolution.addArbitrary_contains [Infinite G] (a b : G) :
    ∀ x y z, ps.R x y z → (ps.addArbitrary a b).R x y z := by
  unfold addArbitrary
  split
  · simp
  · generalize_proofs v1 v2 v3
    exact (v3 v2).choose_spec.2

variable (ps : PartialSolution ℕ)

include ps in
noncomputable def PartialSolution.complSeq : ℕ → PartialSolution ℕ
| 0 => ps
| n+1 => (complSeq n).addArbitrary n.unpair.1 n.unpair.2

lemma PartialSolution.complSeq_exists (a b : ℕ) : ∃ c, (complSeq ps (Nat.pair a b + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_covers

lemma PartialSolution.complSeq_mono_add_one (i : ℕ) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps (i + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_contains
  exact h

lemma PartialSolution.complSeq_mono (i j : ℕ) (hij : i ≤ j) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps j).R a b c := by
  induction hij
  · exact h
  · apply ps.complSeq_mono_add_one
    assumption

lemma PartialSolution.complSeq_exists_of_lt (a b i : ℕ) (h : Nat.pair a b < i) :
    ∃ c, (complSeq ps i).R a b c := by
  obtain ⟨c, hc⟩ := ps.complSeq_exists a b
  use c
  apply complSeq_mono _ _ _ _ _ _ _ hc
  omega

noncomputable def PartialSolution.compl (a b c : ℕ) : Prop :=
  (ps.complSeq (Nat.pair a b + 1)).R a b c

theorem PartialSolution.compl_rule0 (a b c d : ℕ)
    (h : ps.compl a b c) (h2 : ps.compl a b d) : c = d := by
  unfold compl at *
  have := (ps.complSeq (Nat.pair a b + 1)).rule_0 a b c d
  simp_all

theorem PartialSolution.compl_exists (a b : ℕ) : ∃ c, ps.compl a b c :=
  complSeq_exists ..

lemma PartialSolution.complSeq_of_compl_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) (h : ps.compl a b c) : (ps.complSeq i).R a b c :=
  PartialSolution.complSeq_mono _ _ _ (by omega) _ _ _ h

lemma PartialSolution.complSeq_iff_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) : ps.compl a b c ↔ (ps.complSeq i).R a b c := by
  constructor
  · intro
    apply PartialSolution.complSeq_of_compl_of_lt <;> assumption
  · intro h
    have ⟨c', hc⟩ := ps.compl_exists a b
    convert hc
    have := ps.complSeq_of_compl_of_lt a b i habi c' hc
    have := (ps.complSeq i).rule_0 a b c c'
    simp_all

theorem PartialSolution.compl_rule1 ({' '.join(f'X{i}' for i in range(rules[1].vars))} : ℕ) :
    {rules[1].to_lean_no_binders('ps.compl')} := by
  let i := 1 + {rules[1].to_lean_max()}
  repeat rw [PartialSolution.complSeq_iff_of_lt _ _ _ i]
  apply PartialSolution.rule_1
  all_goals omega

noncomputable def PartialSolution.complFun (a b : ℕ) : ℕ := (ps.compl_exists a b).choose

theorem PartialSolution.complFun_eq_iff (a b c : ℕ) : ps.complFun a b = c ↔ ps.compl a b c := by
  constructor
  · rintro rfl
    exact (ps.compl_exists a b).choose_spec
  · intro h
    have : ps.compl a b (ps.complFun a b) := (ps.compl_exists a b).choose_spec
    exact ps.compl_rule0 a b _ _ this h

lemma PartialSolution.of_R (a b c : ℕ) (h : ps.R a b c) : ps.complFun a b = c := by
  rw [PartialSolution.complFun_eq_iff]
  apply PartialSolution.complSeq_mono _ 0 _ (by simp) _ _ _ h

noncomputable def PartialSolution.toMagma : Magma ℕ where
  op := ps.complFun

theorem PartialSolution.toMagma_equation{eqid} :
    letI := ps.toMagma
    Equation{eqid} ℕ := by
  simp only [Equation{eqid}, PartialSolution.toMagma]
  intro {' '.join(f'X{i}' for i in range(count_vars(eq)))}
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 {rules[1].to_fun_app('ps.complFun')}

'''

    with open('unknowns.json', 'r') as fs:
        data = json.load(fs)

    # print(tptp)

    for rel in data:
        if rel['lhs'] == f'Equation{eqid}':
            rhs_id = rel['rhs'][len('Equation'):]
            rhs = eqs[int(rhs_id) - 1]
            inp = f''
            for i, rule in enumerate(rules):
                inp += f'fof(old_{i}, axiom, {rule.to_tptp("old")}).\n'
            ort = rulify_eq2(rhs)
            inp += f'fof(test, conjecture, {ort.to_tptp("old")}).\n'
            print(rules, inp)
            out = subprocess.check_output(['/home/commandmaster/Downloads/vampire', '-sa', 'fmb',
                                           '/proc/self/fd/0', '-t', '30'], input=inp.encode()).decode()
            old = re.findall(r'(?<!~)old\(([\w\'$]+),([\w\'$]+),([\w\'$]+)\)', out)
            old = [[int(x.split('_')[-1][:-1]) for x in y] for y in old]
            print(old)
            print(out)
            mp = {}
            vars = set()
            for a, b, c in old:
                mp[(a, b)] = c
                vars.update((a, b, c))
            enda = None
            for assignment in itertools.product(vars, repeat=ort.vars):
                if ort.precond(assignment, mp):
                    v = ort.conc(assignment, mp)
                    if v is not None and not (len(v) == 2 and v[0] == v[1]):
                        enda = [assignment[ort.varmap[i]] for i in range(count_vars(rhs))]
                        print(v, enda, assignment)
                        break

            lean += f'''
set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter{rhs_id} : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({{{", ".join(f'{tuple(x)}' for x in old)}}} : Finset _)
  {newline_two_spaces.join(f'rule_{i} := by simp only [← imp_iff_not_or]; aesop' for i in range(len(rules)))}
  finsupp := {vars}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation{eqid}_not_implies_Equation{rhs_id} : ∃ (G : Type) (_ : Magma G), Equation{eqid} G ∧ ¬Equation{rhs_id} G := by
  use ℕ, PartialSolution.counter{rhs_id}.toMagma, PartialSolution.counter{rhs_id}.toMagma_equation{eqid}
  simp only [not_forall, PartialSolution.toMagma]
  use {", ".join(map(str,enda))}
  repeat (first | {' | '.join(f'rw [PartialSolution.counter{rhs_id}.of_R {a} {b} {c}]' for a, b, c in old)})
  all_goals simp [PartialSolution.counter{rhs_id}]

'''

    lean += f'end Eq{eqid}'

    # print(lean)

    with open(f'equational_theories/Generated/Greedy/Eq{eqid}.lean', 'w') as f:
        f.write(lean)


if __name__ == '__main__':
    main()