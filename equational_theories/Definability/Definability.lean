import equational_theories.MagmaLaw
import equational_theories.Preorder
import Mathlib.ModelTheory.Definability
import Mathlib.Data.Rel

--The notion of term-definable expressions in FO logic. Could go in Mathlib
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

-- @[simp]
-- theorem Term.realize_substFunc {t : L.Term α} {tf : ∀ {n : ℕ}, L.Functions n → L.Term (Fin n)} {v : α → M} :
--     False := sorry
--   --   (t.substFunc tf).realize v = t.realize fun a => (tf a).realize v := by
--   -- induction t with
--   -- | var => rfl
--   -- | func _ _ ih => simp [ih]

end Semantics

end Language
end FirstOrder

namespace Set
universe u v w u₁

variable {M : Type w} (A B : Set M) (L L' : FirstOrder.Language.{u, v}) [inst : L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

/-- Definable is transitive. Given a structure S on L and T on L', if:
  * the arityGraph of f is Definable in a structure S on L,
  * the realizations of all L.Functions have arityGraph that's Definable on S,
  * the realizations of all L.Relations are Definable on S,
then the arityGraph of f is Definable on T, as well.
-/
theorem Definable.trans {f : (β → M) → M} [inst₂ : L'.Structure M] (h₁ : A.Definable L f.arityGraph)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.Definable L' (fun v ↦ g.term.realize v).arityGraph)
    (h₃ : ∀ {n} (g : L[[A]].Relations n), A.Definable L' (RelMap g))
    : A.Definable L' f.arityGraph := by
  sorry

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
--   -- have := (LEquiv.addEmptyConstants (L[[A]]) (∅ : Set M))--.onTerm (α := α)
--   sorry

-- theorem TermDefinable.mono {f : (α → M) → M} (h : A.TermDefinable L f) (hAB : A ⊆ B) :
--     B.TermDefinable L f := by
--   rw [termDefinable_iff_empty_termDefinable_with_params] at *
--   exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

/-- TermDefinable is transitive. If f is TermDefinable in a structure S on L, and all of the functions'
  realizations on S are TermDefinable on a structure T on L', then f is TermDefinable on T in L'.
-/
theorem TermDefinable.trans {f : (β → M) → M} [inst₂ : L'.Structure M] (h₁ : A.TermDefinable L f)
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

/-- `IsTermDefinable₁` is equivalent to `IsTermDefinable` on the `Unit` index type. -/
theorem isTermDefinable₁_iff_isTermDefinable (f : M → M) : A.TermDefinable₁ L f ↔
    A.TermDefinable L (fun v ↦ f (v ())) := by
  dsimp [TermDefinable, TermDefinable₁]
  constructor <;> intro h <;> obtain ⟨φ,hφ⟩ := h <;> use φ
  · subst hφ
    funext v
    rw [Function.comp_apply, ← eq_const_of_subsingleton]
  · funext v
    rw [Function.comp_apply, ← congrFun hφ (Function.const Unit v)]
    rfl

/-- `id` is `IsTermDefinable₁` -/
theorem isTermDefinable₁_id : A.TermDefinable₁ L (id : M → M) :=
  ⟨Term.var (), rfl⟩

/-- `IsTermDefinable₁` functions are closed under composition. -/
theorem IsTermDefinable₁_comp {f g : M → M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g) :
    A.TermDefinable₁ L (f ∘ g) := by
  obtain ⟨fφ,rfl⟩ := hf
  obtain ⟨gφ,rfl⟩ := hg
  use fφ.subst (fun (_:Unit) ↦ gφ)
  funext m
  simp [Function.const_def]

end Set
end TermDef


section definitions
open FirstOrder

variable {G β : Type*}

/-- The First Order language of expressions in Magmas: just a single binary operation
(represented here as the constant Unit.unit), and no relations.
-/
def MagmaLanguage : Language where
  Functions n := if n = 2 then Unit else Empty
  Relations _ := Empty

instance instMagmaLanguageUniq : Unique (MagmaLanguage.Functions 2) := by
  simpa [MagmaLanguage] using PUnit.unique

/-- Helper method to turn a 'normal' function that combines pairs into the correctly typed generic
  operation on MagmaLanguage functions. -/
def MagmaLanguage.onFunctions {motive : ℕ → Sort*} (f : motive 2) :
    ∀ {n}, MagmaLanguage.Functions n → motive n :=
  fun {n} f0 ↦
    if hn : n = 2 then
      hn ▸ f
    else
      isEmptyElim (show Empty by simpa [MagmaLanguage, hn] using f0)

/-- Like `MagmaLanguage.onFunctions` but for when the language has constants added. -/
def MagmaLanguage.onFunctions' {motive : ℕ → Sort*} {S : Type} (f : motive 2) (g : S → motive 0) :
    ∀ {n}, (MagmaLanguage[[S]]).Functions n → motive n :=
  fun {n} f0 ↦
    if hn : n = 2 then
      hn ▸ f
    else if hn₂ : n = 0 then
      (hn₂ ▸ f0).elim (isEmptyElim ∘ (by simpa [MagmaLanguage] using ·)) (hn₂ ▸ g)
    else
      isEmptyElim (show _ by
        simp [MagmaLanguage, hn, hn₂, Language.withConstants, Language.sum] at f0
        exact f0.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
      )

namespace Magma

/-- The magma operation, as (Fin 2 → G) → G. -/
def FinArityOp (M : Magma G) : (Fin 2 → G) → G :=
  fun v ↦ M.op (v 0) (v 1)

/-- The graph of a magma operation, as a set of Fin 2 ⊕ Unit → G (which is equivalent to G × G × G). -/
def Graph (M : Magma G) : Set (Fin 2 ⊕ Unit → G) :=
  M.FinArityOp.arityGraph

/-- Magma.FOStructure gives the MagmaLanguage structure that corresponds to the Magma. -/
def FOStructure (M : Magma G) : MagmaLanguage.Structure G where
  funMap :=
    @MagmaLanguage.onFunctions _ M.FinArityOp
  RelMap a :=
    isEmptyElim (show Empty from a)

theorem FOStructure_funMap {M : Magma G} (f : MagmaLanguage.Functions 2) :
    M.FOStructure.funMap f = M.FinArityOp := by
  rfl

/-- Like `FOStructure_funMap` but with empty constants set -/
theorem FOStructure_funMap' {M : Magma G} (f : MagmaLanguage[[(∅:Set _)]].Functions 2) :
    (@FirstOrder.Language.withConstantsStructure MagmaLanguage G M.FOStructure (∅:Set _)
      (FirstOrder.Language.paramsStructure G ∅)).funMap
    f = M.FinArityOp := by
  rcases f with f|f
  · exact rfl
  · exact isEmptyElim f


end Magma
namespace Law.MagmaLaw

/-- A MagmaLaw L is definable on a given Magma ⟨M,◇⟩ if it possible to define an
operation □ on M in first-order logic, in the language given by just ◇, such that
the new magma ⟨M,□⟩ obeys the MagmaLaw L.
-/
def DefinableOnMagma (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    -- obeying the law L,
    @satisfies _ G M' L ∧
    -- with a graph definable in the FOStructure of M.
    (@Set.Definable _ ∅ MagmaLanguage M.FOStructure _ M'.Graph)
    -- These explicit @'s are needed because of instance disambiguation.

/-- A MagmaLaw L is definable from another law L' if L is DefinableOn every magma obeying L'. -/
def DefinableFrom (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' → DefinableOnMagma L M

/-- A MagmaLaw L is term-definable on a given Magma ⟨M,◇⟩ if it possible to define an
operation □ on M as just an expression in terms of ◇, such that
the new magma ⟨M,□⟩ obeys the MagmaLaw L.
-/
def TermDefinableOnMagma (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    -- obeying the law L,
    @satisfies _ G M' L ∧
    -- with a graph equal to some formula in M.
    (@Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ M'.FinArityOp)

/-- A MagmaLaw L is term-definable from another law L' if L is DefinableOn every magma obeying L'. -/
def TermDefinableFrom (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' → TermDefinableOnMagma L M

/-- A MagmaLaw L is structural on a given Magma ⟨M,◇⟩ there is a Magma ⟨M,□⟩ obeying L, so that ◇
and □ are first-order definable in terms of each other. This doesn't necessarily imply that □ is
uniquely determined, but it means that □ can hold all of the information of the magma. -/
def StructuralOnMagma (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    -- obeying the law L,
    @satisfies _ G M' L ∧
    -- with a graph definable in the FOStructure of M,
    (@Set.Definable _ ∅ MagmaLanguage M.FOStructure _ M'.Graph) ∧
    -- and vice versa
    (@Set.Definable _ ∅ MagmaLanguage M'.FOStructure _ M.Graph)

/-- A MagmaLaw L is structural from another law L' if L is StructuralOn every magma obeying L'. -/
def StructuralFrom (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' → StructuralOnMagma L M

/-- A MagmaLaw L is term structural on a given Magma ⟨M,◇⟩ there is a Magma ⟨M,□⟩ obeying L, so that
◇ and □ are term-definable in terms of each other. This doesn't necessarily imply that □ is
uniquely determined, but it means that □ can hold all of the information of the magma. -/
def TermStructuralOnMagma (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    @satisfies _ G M' L ∧
    (@Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ M'.FinArityOp) ∧
    (@Set.TermDefinable _ ∅ MagmaLanguage M'.FOStructure _ M.FinArityOp)

/-- A MagmaLaw L is term-structural from another law L' if L is TermStructuralOn every
magma obeying L'. -/
def TermStructuralFrom (L L' : Law.MagmaLaw β) : Prop :=
  ∀ {G : Type} (M : Magma G), satisfies G L' → TermStructuralOnMagma L M

end Law.MagmaLaw
end definitions

section basic_properties
open FirstOrder FirstOrder.Language

section hierarchy
--The various five relations form a sort of hierarchy:
-- "implies" is the standard equational_theories notion that one equation implies another for the same op.
-- "implies" is stronger than termStructural, which is stronger than structural, which is stronger than
-- definable. termStructural is also stronger than termDefinable, which is stronger than definable.
variable {β : Type*} {L' L : Law.MagmaLaw β}

/-- If law L implies L', then L' is term-structural from L: just take the same operation. -/
theorem termStructural_of_implies (h : L.implies L') : L'.TermStructuralFrom L := by
  intro G M hGL
  use M
  constructor
  · exact h hGL
  · constructor <;> {
      use Term.func (l := 2) (Sum.inl ()) Term.var
      rfl
    }

/-- If law L' is term-structural from L, then L' is structural from L. -/
theorem structural_of_termStructural (h : L'.TermStructuralFrom L) : L'.StructuralFrom L := by
  intro G M hGL
  obtain ⟨M',h2,h3,h4⟩ := h M hGL
  use M', h2
  constructor
  · exact h3.Definable (inst := M.FOStructure)
  · exact h4.Definable (inst := M'.FOStructure)

/-- If law L' is term-structural from L, then L' is term-definable from L. -/
theorem termDefinable_of_termStructural (h : L'.TermStructuralFrom L) : L'.TermDefinableFrom L := by
  intro G M hGL
  obtain ⟨M',h2,h3,_⟩ := h M hGL
  use M', h2

/-- If law L' is structural from L, then L' is definable from L. -/
theorem definable_of_structural (h : L'.StructuralFrom L) : L'.DefinableFrom L := by
  intro G M hGL
  obtain ⟨M',h2,h3,_⟩ := h M hGL
  use M', h2

/-- If law L' is term-definable from L, then L' is definable from L. -/
theorem definable_of_termDefinable (h : L'.TermDefinableFrom L) : L'.DefinableFrom L := by
  intro G M hGL
  obtain ⟨M',h2,h3⟩ := h M hGL
  use M', h2
  exact h3.Definable (inst := M.FOStructure)

end hierarchy

section preorder
--Each of these five relations yield a preorder on `MagmaLaw`s. The one for `implies` is the one given
--in Preorder.lean. Here we give the other four by showing reflexivity and transitivity.

variable {β : Type*} {L₁ L₂ L₃ : Law.MagmaLaw β}

theorem TermDefinable.trans_aux {G : Type} {M M₂ M₃ : Magma G}
    (h₁ : (∅:Set _).TermDefinable MagmaLanguage (inst := M.FOStructure) M₂.FinArityOp)
    (h₂ : (∅:Set _).TermDefinable MagmaLanguage (inst := M₂.FOStructure) M₃.FinArityOp) :
    (∅:Set _).TermDefinable MagmaLanguage (inst := M.FOStructure) M₃.FinArityOp := by
  apply h₂.trans (inst := M₂.FOStructure) (inst₂ := M.FOStructure)
  intro n f
  by_cases hn : n = 2
  · subst hn
    simp
    eta_reduce
    convert h₁
    rw [Magma.FOStructure_funMap']
  by_cases hn₂ : n = 0
  · subst hn₂
    simp [MagmaLanguage, Language.withConstants, Language.sum] at f
    exact (isEmptyElim f)
  · exact isEmptyElim (show _ by
      simp [MagmaLanguage, hn, hn₂, Language.withConstants, Language.sum] at f
      exact f.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
    )

theorem TermDefinable.trans (h₁₂ : L₂.TermDefinableFrom L₁) (h₂₃ : L₃.TermDefinableFrom L₂) :
    L₃.TermDefinableFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB⟩ := h₂₃ M₂ hGL₂
  use M₃, hGL₃
  exact trans_aux hA hB

theorem TermStructural.trans (h₁₂ : L₂.TermStructuralFrom L₁) (h₂₃ : L₃.TermStructuralFrom L₂) :
    L₃.TermStructuralFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA1,hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB1,hB2⟩ := h₂₃ M₂ hGL₂
  use M₃, hGL₃
  constructor
  · exact TermDefinable.trans_aux hA1 hB1
  · exact TermDefinable.trans_aux hB2 hA2

theorem Definable.trans_aux {G : Type} {M M₂ M₃ : Magma G}
    (h₁ : @Set.Definable _ (∅:Set _) MagmaLanguage M.FOStructure _ M₂.FinArityOp.arityGraph)
    (h₂ : @Set.Definable _ (∅:Set _) MagmaLanguage M₂.FOStructure _ M₃.FinArityOp.arityGraph) :
    @Set.Definable _ (∅:Set _) MagmaLanguage M.FOStructure _ M₃.FinArityOp.arityGraph := by
  apply h₂.trans (inst := M₂.FOStructure) (inst₂ := M.FOStructure); swap
  · simp [MagmaLanguage, Language.withConstants]
  intro n f
  by_cases hn : n = 2
  · subst hn
    simp
    eta_reduce
    convert h₁
    rw [Magma.FOStructure_funMap']
  by_cases hn₂ : n = 0
  · subst hn₂
    simp [MagmaLanguage, Language.withConstants, Language.sum] at f
    exact (isEmptyElim f)
  · exact isEmptyElim (show _ by
      simp [MagmaLanguage, hn, hn₂, Language.withConstants, Language.sum] at f
      exact f.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
    )

theorem Definable.trans (h₁₂ : L₂.DefinableFrom L₁) (h₂₃ : L₃.DefinableFrom L₂) :
    L₃.DefinableFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB⟩ := h₂₃ M₂ hGL₂
  use M₃, hGL₃
  exact trans_aux hA hB

theorem Structural.trans (h₁₂ : L₂.StructuralFrom L₁) (h₂₃ : L₃.StructuralFrom L₂) :
    L₃.StructuralFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA1,hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB1,hB2⟩ := h₂₃ M₂ hGL₂
  use M₃, hGL₃
  constructor
  · exact Definable.trans_aux hA1 hB1
  · exact Definable.trans_aux hB2 hA2

@[simp]
theorem TermStructural.refl : L₁.TermStructuralFrom L₁ :=
  termStructural_of_implies id

@[simp]
theorem TermDefinable.refl : L₁.TermDefinableFrom L₁ :=
  termDefinable_of_termStructural TermStructural.refl

@[simp]
theorem Structural.refl : L₁.StructuralFrom L₁ :=
  structural_of_termStructural TermStructural.refl

@[simp]
theorem Definable.refl : L₁.DefinableFrom L₁ :=
  definable_of_structural Structural.refl

attribute [-instance] Law.MagmaLaw.instPreorder

--We make preorder as scoped instances so they don't all collide

namespace TermDefinablePreorder
scoped instance : Preorder (Law.MagmaLaw β) where
  le l₁ l₂ := l₂.TermDefinableFrom l₁
  le_refl := fun _ ↦ TermDefinable.refl
  le_trans := fun _ _ _ ↦ TermDefinable.trans
end TermDefinablePreorder

namespace TermStructuralPreorder
scoped instance : Preorder (Law.MagmaLaw β) where
  le l₁ l₂ := l₂.TermStructuralFrom l₁
  le_refl := fun _ ↦ TermStructural.refl
  le_trans := fun _ _ _ ↦ TermStructural.trans
end TermStructuralPreorder

namespace StructuralPreorder
scoped instance : Preorder (Law.MagmaLaw β) where
  le l₁ l₂ := l₂.StructuralFrom l₁
  le_refl := fun _ ↦ Structural.refl
  le_trans := fun _ _ _ ↦ Structural.trans
end StructuralPreorder

namespace DefinablePreorder
scoped instance : Preorder (Law.MagmaLaw β) where
  le l₁ l₂ := l₂.DefinableFrom l₁
  le_refl := fun _ ↦ Definable.refl
  le_trans := fun _ _ _ ↦ Definable.trans
end DefinablePreorder

end preorder

end basic_properties
