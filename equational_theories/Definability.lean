import equational_theories.MagmaLaw
import Mathlib.ModelTheory.Definability
import Mathlib.Data.Rel

/-- The First Order language of expressions in Magmas: just a single binary operation
(represented here as the constant Unit.unit), and no relations.
-/
def MagmaLanguage : FirstOrder.Language where
  Functions n := if n = 2 then Unit else Empty
  Relations _ := Empty

namespace Magma

/-- Magma.FOStructure gives the MagmaLanguage structure that corresponds to the Magma. -/
def FOStructure {G : Type*} (M : Magma G) : MagmaLanguage.Structure G where
  funMap {n} f args :=
    if hn : n = 2 then
      let arg2 := hn ▸ args
      M.op (arg2 0) (arg2 1)
    else
      isEmptyElim (show Empty by simpa [MagmaLanguage, hn] using f)
  RelMap a := isEmptyElim (show Empty from a)

/-- The graph of a magma operation, as Fin 3 → G (which is equivalent to G × G × G). -/
def Graph {G : Type*} (M : Magma G) : Set (Fin 3 → G) :=
  { f : Fin 3 → G | M.op (f 1) (f 2) = f 3 }

end Magma

/-- A MagmaLaw L is definable with a given Magma ⟨M,◇⟩ if it possible to define an
operation □ on M in first-order logic, in the language given by just ◇, such that
the new magma ⟨M,□⟩ obeys the MagmaLaw L.
-/
def DefinableMagma {G β : Type*} (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    -- obeying the law L,
    @satisfies _ G M' L ∧
    -- with a graph definable in the FOStructure of M.
    (@Set.Definable _ ∅ MagmaLanguage M.FOStructure _ M'.Graph)
    -- These explicit @'s are needed because of instance disambiguation.


section TermDef
namespace Set
universe u v w u₁

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

/-- A function from a Cartesian power of a structure to that structure is term-definable over
  a set `A` when the value of the function is given by a term with constants `A`. -/
def IsTermDefinable (f : (α → M) → M) : Prop :=
  ∃ φ : L[[A]].Term α, f = φ.realize

/-- The higher-arity graph of a function. Generalizes Function.graph. -/
def _root_.Function.arityGraph (f : (α → M) → M) : Set ((α ⊕ Unit) → M) :=
  { v | f (v ∘ Sum.inl) = v (Sum.inr Unit.unit) }

/-- Every TermDefinable function has a graph that is definable. -/
theorem definable_if_TermDefinable {f : (α → M) → M} (h : A.IsTermDefinable L f) :
    A.Definable L f.arityGraph := by
  obtain ⟨φ,rfl⟩ := h
  use (φ.relabel Sum.inl).equal (Term.var (Sum.inr Unit.unit))
  ext v
  simp [Function.arityGraph]

end Set
end TermDef

/-- A MagmaLaw L is term-definable with a given Magma ⟨M,◇⟩ if it possible to define an
operation □ on M as just an expression in terms of ◇, such that
the new magma ⟨M,□⟩ obeys the MagmaLaw L.
-/
def TermDefinableMagma {G β : Type*} (L : Law.MagmaLaw β) (M : Magma G) : Prop :=
  --If there exists a magma M',
  ∃ M' : Magma G,
    -- obeying the law L,
    @satisfies _ G M' L ∧
    -- with a graph equal to some formula in M.
    -- let f := M'.op.uncurry ∘ (finTwoArrowEquiv _).toFun
    let f := fun v ↦ M'.op (v (0 : Fin 2)) (v 1)
    (@Set.IsTermDefinable _ ∅ MagmaLanguage M.FOStructure _ f)
