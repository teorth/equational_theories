import Mathlib.ModelTheory.Definability
import Mathlib.Data.Rel
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin

--The notion of term-definable expressions in FO logic, as well other useful lemmas about
--FO logic

section TermDef
namespace Function

variable {α M : Type*} {k : ℕ}

/-- The higher-arity graph of a function. Generalizes Function.graph. -/
def arityGraph (f : (α → M) → M) : Set ((α ⊕ Unit) → M) :=
  { v | f (v ∘ Sum.inl) = v (Sum.inr ()) }

end Function

namespace FirstOrder
namespace Language
namespace LEquiv

variable {L L' : Language}
variable {M α β γ: Type*}

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]

theorem onTerm_symm (φ : L ≃ᴸ L') : (φ.onTerm.symm : L'.Term α ≃ L.Term α) =  φ.symm.onTerm :=
  rfl

end LEquiv

section Syntax

variable {L L' : Language} {α : Type*}

/-- The representation of a function symbol as a term on the appropriate Fin. -/
def Functions.term {n : ℕ} (f : L.Functions n) : L.Term (Fin n) :=
  func f Term.var

/-- Substitutes the functions in a given term with expressions. -/
@[simp]
def Term.substFunc : L.Term α → (∀ {n : ℕ}, L.Functions n → L'.Term (Fin n)) → L'.Term α
  | var a, _ => var a
  | func f ts, tf => (tf f).subst fun i ↦ (ts i).substFunc tf

end Syntax

section Semantics
variable {L L' : Language} {M α : Type*} [L.Structure M]

@[simp]
theorem realize_functions {n : ℕ} {f : L.Functions n} {v : Fin n → M} :
    f.term.realize v = Structure.funMap f v := by
  rfl

--Don't really have this statement written correctly, but ideally it should be the correct thing that
--would close out the last few lines of the proof of TermDefinable.trans
-- @[simp]
-- theorem Term.realize_substFunc {t : L.Term α} {tf : ∀ {n : ℕ}, L.Functions n → L.Term (Fin n)} {v : α → M} :
--     False := sorry
--   --   (t.substFunc tf).realize v = t.realize fun a => (tf a).realize v := by
--   -- induction t with
--   -- | var => rfl
--   -- | func _ _ ih => simp [ih]

end Semantics

namespace Term
variable {L L' : Language} {α M : Type*}

/-- Given a term in language L, and a set of formulas that define L in terms of another language L'
on a structure M, this produces a term in L' that will evaluate to the same value on that structure. It
comes with a type `β` of extra variables to use, and a list of side conditions that must be fulfilled.
-/
def subst_definitions (t : L.Term α) (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Fin n ⊕ Unit))
    : (β : Type) × (L'.Term (α ⊕ β)) × List (L'.Formula (α ⊕ β)) :=
  match t with
  | var a => ⟨Empty, var (Sum.inl a), []⟩
  | @func _ _ n f args =>
      --Map all subexpressions
      let subExprs := fun i ↦ subst_definitions (args i) Fs
      --The function that will re-map the subexpressions to the new side-type α ⊕ β
      let remapper {i} : (α ⊕ (subExprs i).1) → _ := (Sum.map id fun βi ↦ Sum.inl ⟨i,βi⟩)
      --The side-type is the union of all the subexpression side-types, plus one new symbol
      let β := ((i:Fin _) × (subExprs i).1) ⊕ Unit
      --We represent the output of the function with the new symbol
      let thisVar := var (Sum.inr (Sum.inr ()))
      --We have our own side condition to express that we're the output of this function
      let thisCond : L'.Formula (α ⊕ β) :=
        (Fs f).subst (Sum.elim (fun i ↦ (subExprs i).2.1.relabel remapper) (fun () ↦ thisVar))
      --And we add all of the subexpressions' side conditions,
      --appropriately re-indexed to use the new side-type β
      let subConds := (List.finRange n).flatMap fun i ↦
        (subExprs i).2.2.map (Formula.relabel remapper)
      ⟨β, thisVar, thisCond :: subConds⟩

--Gives a witness to the finiteness of the side-type, the first part β of the tuple that
--subst_definitions returns, in the form of a
private def Fin_subst_definitions_sidetype (f : L.Term α)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Fin n ⊕ Unit)) :
    (c : ℕ) × ((f.subst_definitions Fs).1 ≃ Fin c) := by
  sorry

end Term

/-- Equivalence between `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. Compare with finPiFinEquiv. -/
def _root_.finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  sorry

namespace BoundedFormula

variable {L L' : Language} {α M : Type*}

def subst_definitions {k : ℕ} (f : L.BoundedFormula α k)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Fin n ⊕ Unit))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.BoundedFormula α k) :=
  match f with
  | falsum => falsum
  | equal t₁ t₂ =>
    let t₁s := t₁.subst_definitions Fs
    let t₂s := t₂.subst_definitions Fs
    let ec₁ := (t₁.Fin_subst_definitions_sidetype Fs).2
    let ec₂ := (t₂.Fin_subst_definitions_sidetype Fs).2
    let relabel₁ := Sum.elim Sum.inl fun j ↦ Sum.inr $ finSumFinEquiv $ Sum.inl $ ec₁ j
    let relabel₂ := Sum.elim Sum.inl fun j ↦ Sum.inr $ finSumFinEquiv $ Sum.inr $ ec₂ j
    let t₁r := t₁s.2.1.relabel relabel₁
    let t₂r := t₂s.2.1.relabel relabel₂
    let feq := equal t₁r t₂r
    let sideConds₁ := t₁s.2.2.map (relabel relabel₁)
    let sideConds₂ := t₂s.2.2.map (relabel relabel₂)
    let fullConds := (sideConds₁ ++ sideConds₂).foldl BoundedFormula.imp feq
    BoundedFormula.relabel id fullConds.alls
  | imp f₁ f₂ =>
      imp (f₁.subst_definitions Fs Rs) (f₂.subst_definitions Fs Rs)
  | all f =>
      all (f.subst_definitions Fs Rs)
  | rel R ts =>
    let tss := fun i ↦ (ts i).subst_definitions Fs
    let cs := fun i ↦ ((ts i).Fin_subst_definitions_sidetype Fs).1
    let ecs := fun i ↦ ((ts i).Fin_subst_definitions_sidetype Fs).2
    let relabels := fun i ↦ Sum.elim Sum.inl fun j ↦ Sum.inr $ finSigmaFinEquiv ⟨i,ecs i j⟩
    let tsr : (i : Fin _) → L'.Term ((α ⊕ Fin k) ⊕ Fin (∑ i, cs i)) :=
      fun i ↦ (tss i).2.1.relabel (relabels i)
    let newRel := ((Rs R).subst tsr).relabel id
    let sideConds := fun i ↦ (tss i).2.2.map (relabel (relabels i))
    let fullConds := (List.ofFn sideConds).flatten.foldl BoundedFormula.imp newRel
    BoundedFormula.relabel id fullConds.alls

end BoundedFormula

namespace Formula

variable {L L' : Language} {α M : Type*}

/-- Given a formula in language L, and a set of formulas that define L in terms of another language L'
on a structure M, this produces a formula in L' that will evaluate to the same value on that structure.
-/
def subst_definitions (f : L.Formula α)
    (Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Fin n ⊕ Unit))
    (Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n))
    : (L'.Formula α) :=
  BoundedFormula.subst_definitions f Fs Rs

/-- `subst_definitions` agrees with the original formula once realized. -/
theorem subst_definitions_eq (f : L.Formula α) [inst : L.Structure M] [inst' : L'.Structure M]
  {Fs : ∀ {n} (_ : L.Functions n), L'.Formula (Fin n ⊕ Unit)}
  (hFs : ∀ {n} (g : L.Functions n),
    (Function.arityGraph fun v ↦ g.term.realize v) = ((Fs g).Realize : Set (_ → M)))
  {Rs : ∀ {n} (_ : L.Relations n), L'.Formula (Fin n)}
  (hRs : ∀ {n} (g : L.Relations n), inst.RelMap g = (Rs g).Realize)
  : ∀ v, (f.subst_definitions Fs Rs).Realize (M := M) v = f.Realize v := by
    sorry

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
theorem Definable.trans {f : (β → M) → M} (h₁ : A.Definable L f.arityGraph)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.Definable L' (fun v ↦ g.term.realize v).arityGraph)
    (h₃ : ∀ {n} (g : L[[A]].Relations n), A.Definable L' (RelMap g))
    : A.Definable L' f.arityGraph :=
  h₁.elim fun φ₁ hφ₁ ↦
    ⟨_, hφ₁.trans $ funext fun v ↦ (φ₁.subst_definitions_eq
      (fun g ↦ (h₂ g).choose_spec) (fun g ↦ (h₃ g).choose_spec) v).symm⟩

/-- A function from a Cartesian power of a structure to that structure is term-definable over
  a set `A` when the value of the function is given by a term with constants `A`. -/
def TermDefinable (f : (α → M) → M) : Prop :=
  ∃ φ : L[[A]].Term α, f = φ.realize

/-- Every TermDefinable function has a graph that is definable. -/
theorem TermDefinable.Definable {f : (α → M) → M} (h : A.TermDefinable L f) :
    A.Definable L f.arityGraph := by
  obtain ⟨φ,rfl⟩ := h
  use (φ.relabel Sum.inl).equal (Term.var (Sum.inr ()))
  ext v
  simp [Function.arityGraph]

variable {L L'} {A B} {f : (α → M) → M}

theorem TermDefinable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.TermDefinable L f)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.TermDefinable L' f := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onTerm ψ, ?_⟩
  ext x
  simp only [mem_setOf_eq, LHom.realize_onTerm]

theorem empty_termDefinable_iff :
    (∅ : Set M).TermDefinable L f ↔ ∃ φ : L.Term α, f = φ.realize := by
  rw [TermDefinable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp

-- theorem termDefinable_iff_empty_termDefinable_with_params :
--     A.TermDefinable L f ↔ (∅ : Set M).TermDefinable (L[[A]]) f := by
--   have := (LEquiv.addEmptyConstants (L[[A]]) (∅ : Set M)).onTerm (α := α)
--   sorry

-- theorem TermDefinable.mono {f : (α → M) → M} (h : A.TermDefinable L f) (hAB : A ⊆ B) :
--     B.TermDefinable L f := by
--   rw [termDefinable_iff_empty_termDefinable_with_params] at *
--   exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

/-- TermDefinable is transitive. If f is TermDefinable in a structure S on L, and all of the functions'
  realizations on S are TermDefinable on a structure T on L', then f is TermDefinable on T in L'.
-/
theorem TermDefinable.trans {f : (β → M) → M} (h₁ : A.TermDefinable L f)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.TermDefinable L' g.term.realize)
    : A.TermDefinable L' f := by
  obtain ⟨x,rfl⟩ := h₁
  use x.substFunc (fun {n} (g : L[[A]].Functions n) ↦ Classical.choose (h₂ g))
  have hc : ∀ {n} (g : L[[A]].Functions n), _ := fun {n} g ↦ congrFun (Classical.choose_spec (h₂ g))
  funext v
  induction x
  next x₀ =>
    simp
  next n f ts ih =>
    simp [← ih, ← hc]

variable (L)

/-- A function from a structure to irself is term-definable over a set `A` when the
  value of the function is given by a term with constants `A`. Like `TermDefinable`
  but specialized for unary functions in order to write `M → M` instead of `(Unit → M) → M`.-/
def TermDefinable₁ (f : M → M) : Prop :=
  ∃ φ : L[[A]].Term Unit, f = φ.realize ∘ Function.const _

/-- `TermDefinable₁` is equivalent to `TermDefinable` on the `Unit` index type. -/
theorem TermDefinable₁_iff_TermDefinable (f : M → M) : A.TermDefinable₁ L f ↔
    A.TermDefinable L (fun v ↦ f (v ())) := by
  dsimp [TermDefinable, TermDefinable₁]
  constructor <;> intro h <;> obtain ⟨φ,hφ⟩ := h <;> use φ
  · subst hφ
    funext v
    rw [Function.comp_apply, ← eq_const_of_subsingleton]
  · funext v
    rw [Function.comp_apply, ← congrFun hφ (Function.const Unit v)]
    rfl

/-- `id` is `TermDefinable₁` -/
theorem TermDefinable₁_id : A.TermDefinable₁ L (id : M → M) :=
  ⟨Term.var (), rfl⟩

/-- `TermDefinable₁` functions are closed under composition. -/
theorem TermDefinable₁_comp {f g : M → M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g) :
    A.TermDefinable₁ L (f ∘ g) := by
  obtain ⟨fφ,rfl⟩ := hf
  obtain ⟨gφ,rfl⟩ := hg
  use fφ.subst (fun (_:Unit) ↦ gφ)
  funext m
  simp [Function.const_def]

end Set
end TermDef
