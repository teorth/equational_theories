import equational_theories.ForMathlib.Definability
import equational_theories.MagmaLaw
import equational_theories.Preorder

/-!
While the main purpose of the Equational Theories project is exploring which magma equations directly
imply each other, another interesting question is which equations simply imply the *existence* of
another. The example prompting this is that any magma satisfying equation 543,
  `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`,
automatically has an abelian group structure given by `x+y := x ◇ ((y ◇ y) ◇ y)`. In this case,
the `◇` operation is subtraction in the group. This was proved by Tarski.

There are a few distinct ways one can look to generalize this, depending on what precisely one counts
as "having the structure". These each induce a preorder, which include the "implies" preorder as a
subset (because you can just take the same operation again, and it now obeys the implied equation).
-/

section definitions
open FirstOrder

variable {G β : Type*}

/-- The First Order language of expressions in Magmas: just a single binary operation
(represented here as the constant Unit.unit), and no relations.
-/
def MagmaLanguage : Language where
  Functions n := if n = 2 then Unit else Empty
  Relations _ := Empty

open FirstOrder.Language in
/-- Convert a `FreeMagma` expression to a `Term` in the FO language of magmas. -/
def FreeMagma.toTerm {α} : FreeMagma α → MagmaLanguage.Term α
  | .Leaf a => var a
  | .Fork m1 m2 => Functions.apply₂ () m1.toTerm m2.toTerm

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

@[simp]
theorem FOStructure_funMap {M : Magma G} (f : MagmaLanguage.Functions 2) :
    M.FOStructure.funMap f = M.FinArityOp := by
  rfl

/-- Like `FOStructure_funMap` but with empty constants set -/
@[simp]
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
  obtain ⟨M', h2, h3⟩ := h M hGL
  exact ⟨M', h2, h3.Definable (inst := M.FOStructure)⟩

end hierarchy

section preorder
--Each of these five relations yield a preorder on `MagmaLaw`s. The one for `implies` is the one given
--in Preorder.lean. Here we give the other four by showing reflexivity and transitivity.

variable {β : Type*} {L₁ L₂ L₃ : Law.MagmaLaw β}

theorem TermDefinable.trans_aux {G : Type} {M M₂ M₃ : Magma G}
    (h₁ : (∅:Set _).TermDefinable MagmaLanguage (inst := M.FOStructure) M₂.FinArityOp)
    (h₂ : (∅:Set _).TermDefinable MagmaLanguage (inst := M₂.FOStructure) M₃.FinArityOp) :
    (∅:Set _).TermDefinable MagmaLanguage (inst := M.FOStructure) M₃.FinArityOp := by
  apply h₂.trans (inst := M₂.FOStructure) (inst' := M.FOStructure)
  intro n f
  by_cases hn : n = 2
  · subst hn
    simp only [realize_functions, Magma.FOStructure_funMap']
    exact h₁
  by_cases hn₂ : n = 0
  · subst hn₂
    simp only [withConstants, Language.sum, MagmaLanguage, constantsOn_Functions, constantsOnFunc,
      constantsOn_Relations, OfNat.zero_ne_ofNat, ↓reduceIte] at f
    exact (isEmptyElim f)
  · exact isEmptyElim (show _ by
      simp only [withConstants, Language.sum, MagmaLanguage, constantsOn_Functions, constantsOnFunc,
        constantsOn_Relations, hn, ↓reduceIte] at f
      exact f.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
    )

theorem TermDefinable.trans (h₁₂ : L₂.TermDefinableFrom L₁) (h₂₃ : L₃.TermDefinableFrom L₂) :
    L₃.TermDefinableFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, trans_aux hA hB⟩

theorem TermStructural.trans (h₁₂ : L₂.TermStructuralFrom L₁) (h₂₃ : L₃.TermStructuralFrom L₂) :
    L₃.TermStructuralFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA1,hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB1,hB2⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, TermDefinable.trans_aux hA1 hB1, TermDefinable.trans_aux hB2 hA2⟩

theorem Definable.trans_aux {G : Type} {M M₂ M₃ : Magma G}
    (h₁ : @Set.Definable _ (∅:Set _) MagmaLanguage M.FOStructure _ M₂.FinArityOp.arityGraph)
    (h₂ : @Set.Definable _ (∅:Set _) MagmaLanguage M₂.FOStructure _ M₃.FinArityOp.arityGraph) :
    @Set.Definable _ (∅:Set _) MagmaLanguage M.FOStructure _ M₃.FinArityOp.arityGraph := by
  apply h₂.trans (inst := M₂.FOStructure) (inst' := M.FOStructure); swap
  · simp [MagmaLanguage, Language.withConstants]
  intro n f
  by_cases hn : n = 2
  · subst hn
    simp only [realize_functions, Magma.FOStructure_funMap']
    exact h₁
  by_cases hn₂ : n = 0
  · subst hn₂
    simp only [withConstants, Language.sum, MagmaLanguage, constantsOn_Functions, constantsOnFunc,
      constantsOn_Relations, OfNat.zero_ne_ofNat, ↓reduceIte] at f
    exact (isEmptyElim f)
  · exact isEmptyElim (show _ by
      simp only [withConstants, Language.sum, MagmaLanguage, constantsOn_Functions, constantsOnFunc,
        constantsOn_Relations, hn, ↓reduceIte] at f
      exact f.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
    )

theorem Definable.trans (h₁₂ : L₂.DefinableFrom L₁) (h₂₃ : L₃.DefinableFrom L₂) :
    L₃.DefinableFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, trans_aux hA hB⟩

theorem Structural.trans (h₁₂ : L₂.StructuralFrom L₁) (h₂₃ : L₃.StructuralFrom L₂) :
    L₃.StructuralFrom L₁ := by
  intro G M hGL₁
  obtain ⟨M₂,hGL₂,hA1,hA2⟩ := h₁₂ M hGL₁
  obtain ⟨M₃,hGL₃,hB1,hB2⟩ := h₂₃ M₂ hGL₂
  exact ⟨M₃, hGL₃, Definable.trans_aux hA1 hB1, Definable.trans_aux hB2 hA2⟩

@[simp]
theorem TermStructural.refl : L₁.TermStructuralFrom L₁ :=
  termStructural_of_implies L₁.implies_refl

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
