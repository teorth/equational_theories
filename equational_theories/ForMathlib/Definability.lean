import Mathlib.ModelTheory.Definability
import Mathlib.Data.Rel
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin

--The notion of term-definable expressions in FO logic, as well other useful lemmas about
--FO logic

section TermDef

namespace FirstOrder
namespace Language

variable {L L' : Language} {α M : Type*}

section Definability
--Notions of "substituting" one expression in another that are useful for definability of sets.

/-- Given a term in language L, and a set of formulas that define L in terms of another language L'
on a structure M, this produces a term in L' that will evaluate to the same value on that structure.
It comes with a type `β` of extra variables to use, and a list of side conditions that must be
fulfilled. This proof of that this evaluation is correct is `Term.subst_definitions_eq`. -/
def Term.subst_definitions
    (t : L.Term α) (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    : (c : ℕ) × (L'.Term (α ⊕ Fin c)) × List (L'.Formula (α ⊕ Fin c)) :=
  match t with
  | var a => ⟨0, var (Sum.inl a), []⟩
  | @func _ _ n f args =>
      --Map all subexpressions
      let subExprs := fun i ↦ subst_definitions (args i) Fs
      --The side-type is the union of all the subexpression side-types, plus one new symbol
      let cTot := ∑ i, (subExprs i).1
      --The function that will re-map the subexpressions to the new side-type α ⊕ β
      let remapper {i} : (α ⊕ Fin (subExprs i).1) → (α ⊕ Fin _) :=
        Sum.map id fun βi ↦ finSumFinEquiv <| Sum.inl <| finSigmaFinEquiv ⟨i,βi⟩
      --We represent the output of the function with the new symbol
      let thisVar := var <| Sum.inr <| finSumFinEquiv <| Sum.inr 0
      --We have our own side condition to express that we're the output of this function
      let thisCond : L'.Formula (α ⊕ Fin (cTot + 1)) :=
        (Fs f).subst <| (Option.elim · thisVar (fun i ↦ (subExprs i).2.1.relabel remapper))
      --And we add all of the subexpressions' side conditions,
      --appropriately re-indexed to use the new side-type β
      let subConds := (List.finRange n).flatMap fun i ↦
        (subExprs i).2.2.map (fun f ↦ f.relabel remapper)
      ⟨cTot + 1, thisVar, thisCond :: subConds⟩

/-- Given a bounded formula in language L, and a set of formulas that define L in terms of another
language L' on a structure M, this produces a term in L' that will evaluate to the same value on
that structure. This proof of this evaluation is `BoundedFormula.subst_definitions_eq`. -/
def BoundedFormula.subst_definitions {k : ℕ} (f : L.BoundedFormula α k)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.BoundedFormula α k) :=
  match f with
  | falsum => falsum
  | equal t₁ t₂ =>
    let t₁s := t₁.subst_definitions Fs
    let t₂s := t₂.subst_definitions Fs
    let relabel₁ := Sum.elim Sum.inl fun j ↦ Sum.inr <| finSumFinEquiv <| Sum.inl j
    let relabel₂ := Sum.elim Sum.inl fun j ↦ Sum.inr <| finSumFinEquiv <| Sum.inr j
    let t₁r := t₁s.2.1.relabel relabel₁
    let t₂r := t₂s.2.1.relabel relabel₂
    let feq := equal t₁r t₂r
    let sideConds₁ := t₁s.2.2.map (relabel relabel₁)
    let sideConds₂ := t₂s.2.2.map (relabel relabel₂)
    let fullConds := (sideConds₁ ++ sideConds₂).foldr BoundedFormula.imp feq
    BoundedFormula.relabel id fullConds.alls
  | imp f₁ f₂ =>
      imp (f₁.subst_definitions Fs Rs) (f₂.subst_definitions Fs Rs)
  | all f =>
      all (f.subst_definitions Fs Rs)
  | rel R ts =>
    let tss := fun i ↦ (ts i).subst_definitions Fs
    let relabels := fun i ↦ Sum.elim Sum.inl fun j ↦ Sum.inr <| finSigmaFinEquiv ⟨i,j⟩
    let tsr : (i : Fin _) → L'.Term ((α ⊕ Fin k) ⊕ Fin (∑ i, (tss i).1)) :=
      fun i ↦ (tss i).2.1.relabel (relabels i)
    let newRel := ((Rs R).subst tsr).relabel id
    let sideConds := fun i ↦ (tss i).2.2.map (relabel (relabels i))
    let fullConds := (List.ofFn sideConds).flatten.foldr BoundedFormula.imp newRel
    BoundedFormula.relabel id fullConds.alls

/-- See `BoundedFormula.subst_definitions`, but this is specialized to `Formula`. -/
def Formula.subst_definitions (f : L.Formula α)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Option (Fin n)))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.Formula α) :=
  BoundedFormula.subst_definitions f Fs Rs

end Definability

variable [inst : L.Structure M] [inst' : L'.Structure M]
variable {Fs : ∀ {n}, L.Functions n → L'.Formula (Option (Fin n))}

namespace Term

variable (t : L.Term α) {sideVals : Fin (t.subst_definitions Fs).1 → M} (v : α → M)

set_option backward.isDefEq.respectTransparency false in
/-- `Term.subst_definitions` agrees with the original formula once realized, assuming all the side
conditions are met. -/
theorem subst_definitions_eq
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (hSideVals : ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v sideVals)) :
    (t.subst_definitions Fs).2.1.realize (Sum.elim v sideVals) = t.realize v := by
  induction t
  · simp [subst_definitions]
  next f args ih =>
    simp only [subst_definitions, Fin.isValue, finSumFinEquiv_apply_right,
      finSumFinEquiv_apply_left, List.mem_cons, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and, forall_eq_or_imp, forall_exists_index, and_imp] at hSideVals
    --Break the "hSideVals" hypothesis list into the hypothesis on the function output,
    -- and the hypotheses on the function inputs
    replace ⟨hOutput, hSideVals⟩ := hSideVals
    simp only [Formula.Realize, Fin.isValue, BoundedFormula.realize_subst] at hOutput

    --We use hFs to simplify the function output condition
    replace hFs := funext_iff.mp (hFs f)
    simp only [Function.tupleGraph, realize_function_term] at hFs
    rw [← Formula.Realize.eq_def, hFs] at hOutput; clear hFs

    --This gives us the left hand side of the goal
    simp only [setOf, Option.elim_none, Fin.isValue, realize_var, Sum.elim_inr] at hOutput
    simp only [subst_definitions, finSumFinEquiv_apply_right, realize_func, realize_var,
      Sum.elim_inr]
    rw [← hOutput]; clear hOutput

    --Congruence inward + reduce
    congr! with i
    simp only [Function.comp_apply, Option.elim_some, realize_relabel]

    --Apply the inductive hypothesis, with the appropriate arguments plugged in
    replace ih : ∀ (i : Fin _), _ := fun i ↦ ih i
      (fun s hs ↦ by  simpa only [FirstOrder.Language.Formula.realize_relabel, Sum.elim_comp_map]
          using hSideVals (s.relabel <| Sum.map id fun βi ↦
            finSumFinEquiv <| Sum.inl <| finSigmaFinEquiv ⟨i,βi⟩) i s hs rfl)
    simp_rw [← ih]; clear ih
    congr 1
    funext sum
    cases sum <;> simp [finSumFinEquiv_apply_left]

variable (Fs) in
/-- The extra side-values produced by `Term.subst_definitions`. -/
def subst_definitions_extraVals (t : L.Term α) : Fin (t.subst_definitions Fs).1 → M :=
  match t with
  | var a => by
    rw [subst_definitions]
    exact default
  | func f args => fun a ↦
      (finSumFinEquiv.symm a).rec (fun a₁ ↦
        (finSigmaFinEquiv.symm a₁).rec fun ai aj ↦
        (args ai).subst_definitions_extraVals aj
      ) (fun _ ↦ (func f args).realize v)

set_option backward.isDefEq.respectTransparency false in
/-- The side conditions produced by subst_definitions always have a satisfying assignment, which
 is the extra side-values. -/
theorem subst_definitions_extraVals_spec
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (v : α → M) :
    ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v (t.subst_definitions_extraVals Fs v))
    := by
  induction t
  next =>
    simp [subst_definitions_extraVals, subst_definitions]
  next f args ih =>
    simp only [subst_definitions, Fin.isValue, finSumFinEquiv_apply_right,
        finSumFinEquiv_apply_left, List.mem_cons, List.mem_flatMap, List.mem_finRange,
        List.mem_map, true_and, forall_eq_or_imp, forall_exists_index, and_imp]
    constructor
    · have hFs' := congrFun (hFs f)
      simp only [Function.tupleGraph, realize_function_term, Formula.Realize] at hFs'
      simp only [Formula.Realize, BoundedFormula.realize_subst, hFs', setOf, Sum.elim_inr,
        realize_var, Fin.isValue, Option.elim_none]
      unfold Function.comp
      simp only [subst_definitions_extraVals,  ← fun x ↦ (args x).subst_definitions_eq v hFs (ih x),
        realize_func, Fin.isValue, Option.elim_some, realize_relabel, finSumFinEquiv_symm_apply_natAdd]
      congr! with x
      funext sum
      cases sum
      · rfl
      · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          finSumFinEquiv_symm_apply_castAdd]
        rw [Equiv.leftInverse_symm finSigmaFinEquiv]
    · rintro a i b hb rfl
      simp only [subst_definitions_extraVals, Formula.realize_relabel]
      convert ih i b hb
      funext sum
      cases sum
      · rfl
      · simp only [realize_func, Function.comp_apply, Sum.map_inr, Sum.elim_inr,
          finSumFinEquiv_symm_apply_castAdd]
        rw [Equiv.leftInverse_symm finSigmaFinEquiv]

/-- `Term.subst_definitions_extraVals` bundled with their defining property
  `Term.subst_definitions_extraVals_spec`. -/
def subst_definitions_extraVals_X
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·)) :
    { xs : Fin (t.subst_definitions Fs).1 → M //
      ∀ s ∈ (t.subst_definitions Fs).2.2, s.Realize (Sum.elim v xs)} :=
  ⟨t.subst_definitions_extraVals Fs v, t.subst_definitions_extraVals_spec hFs v⟩

end Term

variable {Rs : ∀ {n}, L.Relations n → L'.Formula (Fin n)}

namespace BoundedFormula

set_option backward.isDefEq.respectTransparency false in
/-- `BoundedFormula.subst_definitions` agrees with the original formula once realized. -/
theorem subst_definitions_eq {k : ℕ} (f : L.BoundedFormula α k)
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (hRs : ∀ {n} g, (@Rs n g).Realize = Structure.RelMap (M := M) g) :
    ∀ vL vR, (f.subst_definitions Fs Rs).Realize (M := M) vL vR ↔ f.Realize vL vR := by
  induction f
  next =>
    simp [Realize, subst_definitions]
  next n t₁ t₂ =>
    simp only [subst_definitions, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Nat.add_zero, realize_relabel, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Realize]
    intro vL vR
    rw [show (vR ∘ @Fin.natAdd 0 n) = default from Unique.eq_default _]
    rw [← Formula.Realize, realize_alls]
    simp_rw [realize_foldr_imp]
    simp_rw [BoundedFormula.Realize]
    constructor
    · intro h
      have ⟨xs₁, hxs₁⟩ := t₁.subst_definitions_extraVals_X (Sum.elim vL vR) hFs
      have ⟨xs₂, hxs₂⟩ := t₂.subst_definitions_extraVals_X (Sum.elim vL vR) hFs
      have ht₁ := t₁.subst_definitions_eq (Sum.elim vL vR) hFs hxs₁
      have ht₂ := t₂.subst_definitions_eq (Sum.elim vL vR) hFs hxs₂
      rw [← ht₁, ← ht₂]
      clear ht₁ ht₂
      replace h := h (Fin.appendEquiv _ _ ⟨xs₁,xs₂⟩) (by
        intro i hi
        simp only [List.mem_append, List.mem_map] at hi
        rcases hi with (⟨w,hiw,rfl⟩|⟨w,hiw,rfl⟩) <;> {
          try have := hxs₁ w hiw
          try have := hxs₂ w hiw
          rw [Formula.Realize] at this
          rw [realize_relabel]
          convert this
          funext sum
          cases sum <;> simp})
      convert h using 1 <;> {
        rw [Term.realize_relabel]
        congr
        funext sum
        cases sum <;> simp}
    · intro h xs is
      have ht₁ := t₁.subst_definitions_eq _ hFs (by
        simp_rw [List.mem_append, List.mem_map] at is
        intro s hs
        replace is := is (.relabel (n := _ + _) _ s) (.inl ⟨s, ⟨hs, rfl⟩⟩)
        rw [realize_relabel] at is
        rw [Formula.Realize]
        convert is
        funext sum
        cases sum <;> rfl)
      have ht₂ := t₂.subst_definitions_eq _ hFs (by
        simp_rw [List.mem_append, List.mem_map] at is
        intro s hs
        replace is := is (.relabel (n := _ + _) _ s) (.inr ⟨s, ⟨hs, rfl⟩⟩)
        rw [realize_relabel] at is
        rw [Formula.Realize]
        convert is
        funext sum
        cases sum <;> rfl)
      rw [← ht₁, ← ht₂] at h
      simp_rw [Term.realize_relabel]
      convert h
      <;> funext s
      <;> cases s
      <;> rfl
  next n m R ts =>
    intro vL vR
    simp only [subst_definitions, Nat.add_zero, realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
      Function.comp_id, Realize]
    rw [show (vR ∘ @Fin.natAdd 0 n) = default from Unique.eq_default _,
      ← Formula.Realize, realize_alls]
    simp_rw [realize_foldr_imp]
    constructor
    · intro h
      rw [← hRs R]
      let xs : Fin (∑ i : Fin m, ((ts i).subst_definitions fun {n} ↦ Fs).fst) → M :=
        fun ij ↦ let ⟨i,j⟩ := finSigmaFinEquiv.symm ij;
          ((ts i).subst_definitions_extraVals_X (Sum.elim vL vR) hFs).1 j
      let hxs := fun i ↦ ((ts i).subst_definitions_extraVals_X (Sum.elim vL vR) hFs).2
      replace h := h xs (by
        intro i hi
        simp only [List.mem_flatten] at hi
        rcases hi with ⟨w,hiw,hiw₂⟩
        rw [List.mem_ofFn] at hiw
        obtain ⟨j,rfl⟩ := hiw
        rw [List.mem_map] at hiw₂
        obtain ⟨a,ha₁,rfl⟩ := hiw₂
        have := hxs j a ha₁
        rw [Formula.Realize] at this
        rw [realize_relabel]
        suffices hxs_at_j : ∀ jj, xs (finSigmaFinEquiv ⟨j, jj⟩) =
            ((ts j).subst_definitions_extraVals_X (Sum.elim vL vR) hFs).1 jj by
          convert this
          funext sum
          rcases sum with sl | sr
          · rfl
          · exact hxs_at_j sr
        intro jj
        show (let ⟨i, jjj⟩ := finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨j, jj⟩);
            ((ts i).subst_definitions_extraVals_X (Sum.elim vL vR) hFs).1 jjj) =
            ((ts j).subst_definitions_extraVals_X (Sum.elim vL vR) hFs).1 jj
        rw [finSigmaFinEquiv.symm_apply_apply])
      simp only [realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        realize_subst, Term.realize_relabel, xs] at h
      rw [Formula.Realize]
      convert h with i
      have := (ts i).subst_definitions_eq (Sum.elim vL vR) hFs
        (sideVals := xs ∘ fun j ↦ (finSigmaFinEquiv ⟨i, j⟩)) (by
        unfold xs
        convert hxs i
        funext v
        rw [Function.comp_apply, Equiv.leftInverse_symm])
      convert this.symm
      funext sum
      cases sum <;> rfl

    · intro h xs is
      simp only [realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        realize_subst, Term.realize_relabel]
      rw [← hRs R, Formula.Realize] at h
      rw [show (xs ∘ @Fin.natAdd 0 (∑ i : Fin m, _)) = default from Unique.eq_default _]
      convert h with i
      have hti := (ts i).subst_definitions_eq (Sum.elim vL vR) hFs (by
          simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and, List.mem_map,
            forall_exists_index, and_imp] at is
          intro s hs
          replace is := is (.relabel (k := 0) _ s) i s hs rfl
          rw [realize_relabel] at is
          rw [Formula.Realize]
          convert is
          funext sum
          cases sum <;> rfl)
      convert hti
      funext sum
      cases sum <;> rfl
  next ih₁ ih₂ =>
    simp [subst_definitions, ih₁, ih₂]
  next ih =>
    simp [subst_definitions, ih]

end BoundedFormula

namespace Formula

/-- `Formula.subst_definitions` agrees with the original formula once realized. -/
theorem subst_definitions_eq (f : L.Formula α)
    (hFs : ∀ {n} g, ((@Fs n g).Realize : Set (_ → M)) = Function.tupleGraph (g.term.realize ·))
    (hRs : ∀ {n} g, (@Rs n g).Realize = Structure.RelMap (M := M) g) :
    (f.subst_definitions Fs Rs).Realize (M := M) = f.Realize := by
  apply funext
  simpa [Realize] using BoundedFormula.subst_definitions_eq f hFs hRs

end Formula

end Language
end FirstOrder

namespace Set
universe u v w u₁

variable {M : Type w} (A B : Set M) (L L' : FirstOrder.Language.{u, v})
variable [inst : L.Structure M] [inst' : L'.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

/-- Definable is transitive. Given a structure S on L and T on L', if:
  * the arityGraph of f is Definable in a structure S on L,
  * the realizations of all L.Functions have arityGraph that's Definable on S,
  * the realizations of all L.Relations are Definable on S,
then the arityGraph of f is Definable on T, as well.
-/
theorem Definable.trans {f : (β → M) → M} (h₁ : A.Definable L f.tupleGraph)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.Definable L' (fun v ↦ g.term.realize v).tupleGraph)
    (h₃ : ∀ {n} (g : L[[A]].Relations n), A.Definable L' (Structure.RelMap g))
    : A.Definable L' f.tupleGraph :=
  h₁.elim fun φ₁ hφ₁ ↦
    ⟨_, hφ₁.trans (φ₁.subst_definitions_eq
      (fun g ↦ (h₂ g).choose_spec.symm) (fun g ↦ (h₃ g).choose_spec.symm)).symm⟩

end Set
end TermDef
