import equational_theories.Conjecture
import equational_theories.AllEquations

universe u
universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α

infixl:65 " ⋆ " => FreeMagma.Fork
def Lf {α : Type u} : (α → FreeMagma α) := FreeMagma.Leaf

instance FreeMagma.Magma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

def fmapFreeMagma {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β
  | FreeMagma.Leaf a => FreeMagma.Leaf (f a)
  | FreeMagma.Fork lchild rchild => FreeMagma.Fork (fmapFreeMagma f lchild) (fmapFreeMagma f rchild)

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α -> G) : FreeMagma α → G
  | FreeMagma.Leaf a => f a
  | FreeMagma.Fork lchild rchild => (evalInMagma f lchild) ∘ (evalInMagma f rchild)

theorem ExpressionEqualsAnything_implies_Equation2 (G: Type u) [Magma G]
  : (∃ n : Nat, ∃ expr : FreeMagma (Fin n), ∀ x : G, ∀ sub : Fin n → G, x = evalInMagma sub expr) → Equation2 G := by
  intros ex x y
  let ⟨n, expr, univ⟩ := ex
  let constx : Fin n → G := fun _ ↦ x
  exact (Eq.trans (univ x constx) (Eq.symm (univ y constx)))

theorem Equation37_implies_Equation2 (G : Type u) [Magma G]
  : (∀ x y z w : G, x = (y ∘ z) ∘ w) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    3,
    (Lf 0 ⋆ Lf 1) ⋆ Lf 2, -- The syntactic representation of (y ∘ z) ∘ w
    fun k sub ↦ univ k (sub 0) (sub 1) (sub 2)
  ⟩

theorem Equation514_implies_Equation2 (G : Type u) [Magma G]
  : (∀ x y : G, x = y ∘ (y ∘ (y ∘ y))) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    1,
    Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)), -- The syntactic representation of y ∘ (y ∘ (y ∘ y)))
    fun k sub ↦ univ k (sub 0)
  ⟩
