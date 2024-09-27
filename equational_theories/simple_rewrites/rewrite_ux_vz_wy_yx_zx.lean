import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation418 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation621 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation824 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1027 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1230 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1433 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1636 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1839 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2042 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2245 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2448 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2651 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2854 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3057 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3260 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3463 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3666 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3869 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4072 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4274 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (x ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4387 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4589 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ x) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation418 (G : Type*) [Magma G] (h : Equation613 G) : Equation418 G := λ x y z => h x x x y x z
theorem Equation816_implies_Equation621 (G : Type*) [Magma G] (h : Equation816 G) : Equation621 G := λ x y z => h x x x y x z
theorem Equation1019_implies_Equation824 (G : Type*) [Magma G] (h : Equation1019 G) : Equation824 G := λ x y z => h x x x y x z
theorem Equation1222_implies_Equation1027 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1027 G := λ x y z => h x x x y x z
theorem Equation1425_implies_Equation1230 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1230 G := λ x y z => h x x x y x z
theorem Equation1628_implies_Equation1433 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1433 G := λ x y z => h x x x y x z
theorem Equation1831_implies_Equation1636 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1636 G := λ x y z => h x x x y x z
theorem Equation2034_implies_Equation1839 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1839 G := λ x y z => h x x x y x z
theorem Equation2237_implies_Equation2042 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2042 G := λ x y z => h x x x y x z
theorem Equation2440_implies_Equation2245 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2245 G := λ x y z => h x x x y x z
theorem Equation2643_implies_Equation2448 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2448 G := λ x y z => h x x x y x z
theorem Equation2846_implies_Equation2651 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2651 G := λ x y z => h x x x y x z
theorem Equation3049_implies_Equation2854 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2854 G := λ x y z => h x x x y x z
theorem Equation3252_implies_Equation3057 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3057 G := λ x y z => h x x x y x z
theorem Equation3455_implies_Equation3260 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3260 G := λ x y z => h x x x y x z
theorem Equation3658_implies_Equation3463 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3463 G := λ x y z => h x x x y x z
theorem Equation3861_implies_Equation3666 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3666 G := λ x y z => h x x x y x z
theorem Equation4064_implies_Equation3869 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3869 G := λ x y z => h x x x y x z
theorem Equation4267_implies_Equation4072 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4072 G := λ x y z => h x x x y x z
theorem Equation4379_implies_Equation4274 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4274 G := λ x y z => h x x x y x z
theorem Equation4582_implies_Equation4387 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4387 G := λ x y z => h x x x y x z
theorem Equation4694_implies_Equation4589 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4589 G := λ x y z => h x x x y x z