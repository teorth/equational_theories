import equational_theories.EndToEnd.Certificate
import Mathlib.Data.Nat.Bitwise

/-!
# Correctness of the decision procedure

`resolveImplication_correct` says that whatever `resolveImplication` returns passes the
corresponding checker from `Basic.lean`, whose soundness then gives the mathematical fact.

The proof never enumerates pairs of SCCs. Both walks are justified by induction on the
rank carried in the certificate, and the existentials on the negative side are extracted
from the refuters identity by induction on short lists, so everything stays linear in the size
of the certificate.
-/

namespace EndToEnd

variable {C : Certificate} {pos : RArray PosFact} {neg : RArray NegFact} {i j c e : Nat}

/-- Extract a per-index fact from a `List.range` check. -/
theorem of_range_all {n : Nat} {f : Nat → Bool} (h : (List.range n).all f = true)
    {i : Nat} (hi : i < n) : f i = true := by
  simpa using (List.all_eq_true.mp h) i (by simpa using hi)

/-- Testing one bit of a fold of `|||`s. -/
theorem testBit_foldl_or (f : Nat → Nat) (j : Nat) :
    ∀ (l : List Nat) (a : Nat),
      (l.foldl (fun acc k => acc ||| f k) a).testBit j
        = (a.testBit j || l.any (fun k => (f k).testBit j)) := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons k ks ih =>
      intro a
      simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or]
      cases a.testBit j <;> cases (f k).testBit j <;> simp

theorem testBit_one_shiftLeft (n i : Nat) : (1 <<< n).testBit i = decide (n = i) := by
  rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow ..

/-- Per-edge facts recorded by the forward check, for any out-edge of `i`. -/
theorem fwd_edge (h : checkFwd C pos i = true) {k} (hk : k ∈ C.out.get i) :
    srcScc C pos k = i ∧ tgtScc C pos k < C.numSccs ∧
    (pos.get k).hyp < C.numEq ∧ (pos.get k).conc < C.numEq ∧
    C.rank (tgtScc C pos k) < C.rank i := by
  simp only [checkFwd, Bool.and_eq_true] at h
  have he := (List.all_eq_true.mp h.1.1) k hk
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at he
  exact ⟨he.1.1.1.1, he.1.1.1.2, he.1.1.2, he.1.2, he.2⟩

/-- A bit set in `reaches i` other than `i` itself must come from some out-edge. -/
theorem fwd_exists (h : checkFwd C pos i = true)
    (hj : (C.reaches.get i).testBit j = true) (hne : i ≠ j) :
    ∃ k ∈ C.out.get i, (C.reaches.get (tgtScc C pos k)).testBit j = true := by
  simp only [checkFwd, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2, Nat.testBit_or, testBit_one_shiftLeft, testBit_foldl_or] at hj
  simp only [Nat.zero_testBit, Bool.false_or, decide_eq_true_eq, Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · exact absurd hj hne
  · exact List.any_eq_true.mp hj

/-- Per-edge facts recorded by the reverse check, for any in-edge of `c`. -/
theorem rev_edge (h : checkRev C pos c = true) {k} (hk : k ∈ C.rout.get c) :
    tgtScc C pos k = c ∧ srcScc C pos k < C.numSccs ∧
    (pos.get k).hyp < C.numEq ∧ (pos.get k).conc < C.numEq ∧
    C.rrank (srcScc C pos k) < C.rrank c := by
  simp only [checkRev, Bool.and_eq_true] at h
  have he := (List.all_eq_true.mp h.1.1) k hk
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at he
  exact ⟨he.1.1.1.1, he.1.1.1.2, he.1.1.2, he.1.2, he.2⟩

/-- A bit set in `reachedBy c` other than `c` itself must come from some in-edge. -/
theorem rev_exists (h : checkRev C pos c = true)
    (hj : (C.reachedBy.get c).testBit j = true) (hne : c ≠ j) :
    ∃ k ∈ C.rout.get c, (C.reachedBy.get (srcScc C pos k)).testBit j = true := by
  simp only [checkRev, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2, Nat.testBit_or, testBit_one_shiftLeft, testBit_foldl_or] at hj
  simp only [Nat.zero_testBit, Bool.false_or, decide_eq_true_eq, Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · exact absurd hj hne
  · exact List.any_eq_true.mp hj

/-- The forward rank is bounded by the number of SCCs, so `numSccs` is enough fuel. -/
theorem fwd_rank_lt (h : checkFwd C pos i = true) : C.rank i < C.numSccs := by
  simp only [checkFwd, Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1.2

/-- Likewise for the reverse rank. -/
theorem rev_rank_lt (h : checkRev C pos c = true) : C.rrank c < C.numSccs := by
  simp only [checkRev, Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1.2

/-- The facts `checkCert` establishes, in usable per-index form. -/
structure Valid (C : Certificate) (pos : RArray PosFact) (neg : RArray NegFact) : Prop where
  clsLt : ∀ e, e < C.numEq → C.scc.get e < C.numSccs
  scc : ∀ e, e < C.numEq → checkScc C pos e = true
  fmaskOk : ∀ k, k < C.numNeg → checkFmask C neg k = true
  fwd : ∀ i, i < C.numSccs → checkFwd C pos i = true
  rev : ∀ i, i < C.numSccs → checkRev C pos i = true
  refutersOk : ∀ i, i < C.numSccs → checkRefuters C neg i = true

theorem valid_of_checkCert (h : checkCert C pos neg = true) : Valid C pos neg := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, fun k hk => of_range_all h2 hk,
          fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := of_range_all h1 he
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1
  · have := of_range_all h1 he
    simp only [Bool.and_eq_true] at this
    exact this.2
  · have := of_range_all h3 hi
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  · have := of_range_all h3 hi
    simp only [Bool.and_eq_true] at this
    exact this.1.2
  · have := of_range_all h3 hi
    simp only [Bool.and_eq_true] at this
    exact this.2

/-- `sccUp e` really is a chain from `e` to its representative. -/
theorem sccUp_ok (V : Valid C pos neg) (he : e < C.numEq) :
    checkChain pos e (C.rep.get (C.scc.get e)) (C.sccUp.get e) = true := by
  have := V.scc e he
  simp only [checkScc, Bool.and_eq_true] at this
  exact this.1

/-- `sccDn e` really is a chain from its representative to `e`. -/
theorem sccDn_ok (V : Valid C pos neg) (he : e < C.numEq) :
    checkChain pos (C.rep.get (C.scc.get e)) e (C.sccDn.get e) = true := by
  have := V.scc e he
  simp only [checkScc, Bool.and_eq_true] at this
  exact this.2

/-- The forward walk really produces a chain between the two representatives.

Induction on `fuel`, with the certificate's `rank` supplying the decreasing measure: the
fixpoint identity guarantees an out-edge whose target still reaches `j`, and the rank check
guarantees that edge strictly descends. -/
theorem walkFwd_correct (V : Valid C pos neg) :
    ∀ (fuel i j : Nat), i < C.numSccs → C.rank i ≤ fuel →
      (C.reaches.get i).testBit j = true →
      checkChain pos (C.rep.get i) (C.rep.get j) (walkFwd C pos fuel i j) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro i j hi hr hj
      by_cases hij : i = j
      · subst hij; simp [walkFwd, checkChain]
      · exfalso
        obtain ⟨k, hk, _⟩ := fwd_exists (V.fwd i hi) hj hij
        obtain ⟨_, _, _, _, hrank⟩ := fwd_edge (V.fwd i hi) hk
        omega
  | succ fuel ih =>
      intro i j hi hr hj
      simp only [walkFwd]
      by_cases hij : i = j
      · subst hij; simp [checkChain]
      · rw [if_neg (by simpa using hij)]
        obtain ⟨k0, hk0, hb0⟩ := fwd_exists (V.fwd i hi) hj hij
        cases hfind : (C.out.get i).find?
            (fun k => Nat.testBit (C.reaches.get (tgtScc C pos k)) j) with
        | none =>
            exact absurd hb0 (by simpa using List.find?_eq_none.mp hfind k0 hk0)
        | some k =>
            have hmem : k ∈ C.out.get i := List.mem_of_find?_eq_some hfind
            have hbk : (C.reaches.get (tgtScc C pos k)).testBit j = true := by
              simpa using List.find?_some hfind
            obtain ⟨hsrc, htlt, ha, hb, hrank⟩ := fwd_edge (V.fwd i hi) hmem
            refine checkChain_append pos _ _ (pos.get k).hyp _ _ ?_ ?_
            · have h := sccDn_ok V ha
              rwa [show C.scc.get (pos.get k).hyp = i from hsrc] at h
            · simp only [checkChain, Bool.and_eq_true, beq_self_eq_true, true_and]
              refine checkChain_append pos _ _ (C.rep.get (tgtScc C pos k)) _ _ ?_ ?_
              · exact sccUp_ok V hb
              · exact ih _ _ htlt (by omega) hbk

/-- The reverse walk produces a chain from `rep j` to `rep c`, emitted in forward order. -/
theorem walkRev_correct (V : Valid C pos neg) :
    ∀ (fuel c j : Nat), c < C.numSccs → C.rrank c ≤ fuel →
      (C.reachedBy.get c).testBit j = true →
      checkChain pos (C.rep.get j) (C.rep.get c) (walkRev C pos fuel c j) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro c j hc hr hj
      by_cases hcj : c = j
      · subst hcj; simp [walkRev, checkChain]
      · exfalso
        obtain ⟨k, hk, _⟩ := rev_exists (V.rev c hc) hj hcj
        obtain ⟨_, _, _, _, hrank⟩ := rev_edge (V.rev c hc) hk
        omega
  | succ fuel ih =>
      intro c j hc hr hj
      simp only [walkRev]
      by_cases hcj : c = j
      · subst hcj; simp [checkChain]
      · rw [if_neg (by simpa using hcj)]
        obtain ⟨k0, hk0, hb0⟩ := rev_exists (V.rev c hc) hj hcj
        cases hfind : (C.rout.get c).find?
            (fun k => Nat.testBit (C.reachedBy.get (srcScc C pos k)) j) with
        | none =>
            exact absurd hb0 (by simpa using List.find?_eq_none.mp hfind k0 hk0)
        | some k =>
            have hmem : k ∈ C.rout.get c := List.mem_of_find?_eq_some hfind
            have hbk : (C.reachedBy.get (srcScc C pos k)).testBit j = true := by
              simpa using List.find?_some hfind
            obtain ⟨htgt, hslt, ha, hb, hrank⟩ := rev_edge (V.rev c hc) hmem
            refine checkChain_append pos _ _ (C.rep.get (srcScc C pos k)) _ _ ?_ ?_
            · exact ih _ _ hslt (by omega) hbk
            · refine checkChain_append pos _ _ (pos.get k).hyp _ _ (sccDn_ok V ha) ?_
              simp only [checkChain, Bool.and_eq_true, beq_self_eq_true, true_and]
              have h := sccUp_ok V hb
              rwa [show C.scc.get (pos.get k).conc = c from htgt] at h

theorem testBit_fullMask (hj : j < C.numSccs) : (fullMask C).testBit j = true := by
  simp only [fullMask, Nat.one_shiftLeft]
  rw [Nat.testBit_two_pow_sub_one]
  simpa using hj

/-- Everything SCC `i` fails to imply is refuted by one of `refuters i`. -/
theorem refuters_exists (V : Valid C pos neg) (hi : i < C.numSccs) (hj : j < C.numSccs)
    (hnot : (C.reaches.get i).testBit j = false) :
    ∃ k ∈ C.refuters.get i, (C.fmask.get k).testBit j = true := by
  have hc := V.refutersOk i hi
  simp only [checkRefuters, Bool.and_eq_true, beq_iff_eq] at hc
  have hb := congrArg (fun x => Nat.testBit x j) hc.2
  simp only [Nat.testBit_or, testBit_foldl_or, hnot, testBit_fullMask hj,
    Nat.zero_testBit, Bool.false_or] at hb
  exact List.any_eq_true.mp hb

/-- **Correctness of the decision procedure.**

Whatever `resolveImplication` returns passes the corresponding checker, so by
`checkChain_sound` / `checkRefutation_sound` the corresponding mathematical fact holds.
Note the return type is a `Sum`, so totality is part of the type: there is no separate
"a witness exists" obligation. -/
theorem resolveImplication_correct (V : Valid C pos neg) (n m : Nat)
    (hn : n < C.numEq) (hm : m < C.numEq) :
    match resolveImplication C pos neg n m with
    | .inl c => checkChain pos n m c = true
    | .inr r => checkRefutation pos neg n m r = true := by
  have hi : C.scc.get n < C.numSccs := V.clsLt n hn
  have hj : C.scc.get m < C.numSccs := V.clsLt m hm
  simp only [resolveImplication]
  by_cases hbit : (C.reaches.get (C.scc.get n)).testBit (C.scc.get m) = true
  · rw [if_pos hbit]
    refine checkChain_append pos _ _ (C.rep.get (C.scc.get n)) _ _ (sccUp_ok V hn) ?_
    refine checkChain_append pos _ _ (C.rep.get (C.scc.get m)) _ _ ?_ (sccDn_ok V hm)
    exact walkFwd_correct V _ _ _ hi (Nat.le_of_lt (fwd_rank_lt (V.fwd _ hi))) hbit
  · rw [if_neg hbit]
    have hfalse : (C.reaches.get (C.scc.get n)).testBit (C.scc.get m) = false := by
      simpa using hbit
    obtain ⟨k0, hk0, hfm0⟩ := refuters_exists V hi hj hfalse
    cases hfind : (C.refuters.get (C.scc.get n)).find?
        (fun k => Nat.testBit (C.fmask.get k) (C.scc.get m)) with
    | none => exact absurd hfm0 (by simpa using List.find?_eq_none.mp hfind k0 hk0)
    | some k =>
        dsimp only
        have hmem : k ∈ C.refuters.get (C.scc.get n) := List.mem_of_find?_eq_some hfind
        have hfmk : (C.fmask.get k).testBit (C.scc.get m) = true := by
          simpa using List.find?_some hfind
        have hcov := V.refutersOk _ hi
        simp only [checkRefuters, Bool.and_eq_true] at hcov
        have hke := (List.all_eq_true.mp hcov.1) k hmem
        simp only [Bool.and_eq_true, Nat.blt_eq] at hke
        obtain ⟨hklt, hsat⟩ := hke
        have hfm := V.fmaskOk k hklt
        simp only [checkFmask, Bool.and_eq_true, beq_iff_eq] at hfm
        obtain ⟨⟨hSlt, hRlt⟩, hfmeq⟩ := hfm
        -- some satisfied law of the witness implies SCC n
        obtain ⟨a0, ha0mem, ha0⟩ := List.any_eq_true.mp hsat
        obtain ⟨a, hfa⟩ : ∃ a, (neg.get k).satisfies.find?
            (fun a => Nat.testBit (C.reaches.get (C.scc.get a)) (C.scc.get n)) = some a := by
          cases h : (neg.get k).satisfies.find?
              (fun a => Nat.testBit (C.reaches.get (C.scc.get a)) (C.scc.get n)) with
          | none => exact absurd ha0 (by simpa using List.find?_eq_none.mp h a0 ha0mem)
          | some a => exact ⟨a, rfl⟩
        -- some refuted law of the witness is implied by SCC m
        have hRany : ((neg.get k).refutes.any
            (fun b => Nat.testBit (C.reachedBy.get (C.scc.get b)) (C.scc.get m))) = true := by
          rw [hfmeq, testBit_foldl_or] at hfmk
          simpa using hfmk
        obtain ⟨b0, hb0mem, hb0⟩ := List.any_eq_true.mp hRany
        obtain ⟨b, hfb⟩ : ∃ b, (neg.get k).refutes.find?
            (fun b => Nat.testBit (C.reachedBy.get (C.scc.get b)) (C.scc.get m)) = some b := by
          cases h : (neg.get k).refutes.find?
              (fun b => Nat.testBit (C.reachedBy.get (C.scc.get b)) (C.scc.get m)) with
          | none => exact absurd hb0 (by simpa using List.find?_eq_none.mp h b0 hb0mem)
          | some b => exact ⟨b, rfl⟩
        rw [hfa, hfb]
        have hameme : a ∈ (neg.get k).satisfies := List.mem_of_find?_eq_some hfa
        have hbmeme : b ∈ (neg.get k).refutes := List.mem_of_find?_eq_some hfb
        have hab : (C.reaches.get (C.scc.get a)).testBit (C.scc.get n) = true := by
          simpa using List.find?_some hfa
        have hbb : (C.reachedBy.get (C.scc.get b)).testBit (C.scc.get m) = true := by
          simpa using List.find?_some hfb
        have halt : a < C.numEq := by
          have := (List.all_eq_true.mp hSlt) a hameme
          simpa [Nat.blt_eq] using this
        have hblt : b < C.numEq := by
          have := (List.all_eq_true.mp hRlt) b hbmeme
          simpa [Nat.blt_eq] using this
        have hia : C.scc.get a < C.numSccs := V.clsLt a halt
        have hib : C.scc.get b < C.numSccs := V.clsLt b hblt
        simp only [checkRefutation, Bool.and_eq_true]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · exact List.elem_eq_true_of_mem hameme
        · exact List.elem_eq_true_of_mem hbmeme
        · -- a ⟹ rep (scc a) ⟹ rep (scc n) ⟹ n
          refine checkChain_append pos _ _ (C.rep.get (C.scc.get a)) _ _
            (sccUp_ok V halt) ?_
          refine checkChain_append pos _ _ (C.rep.get (C.scc.get n)) _ _ ?_
            (sccDn_ok V hn)
          exact walkFwd_correct V _ _ _ hia
            (Nat.le_of_lt (fwd_rank_lt (V.fwd _ hia))) hab
        · -- m ⟹ rep (scc m) ⟹ rep (scc b) ⟹ b
          refine checkChain_append pos _ _ (C.rep.get (C.scc.get m)) _ _
            (sccUp_ok V hm) ?_
          refine checkChain_append pos _ _ (C.rep.get (C.scc.get b)) _ _ ?_
            (sccDn_ok V hblt)
          exact walkRev_correct V _ _ _ hib
            (Nat.le_of_lt (rev_rank_lt (V.rev _ hib))) hbb

end EndToEnd
