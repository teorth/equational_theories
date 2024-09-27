import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation473 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation676 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation879 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1082 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1285 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1488 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1691 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1894 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2097 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2300 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2503 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2706 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2909 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3112 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3315 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3518 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3721 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3924 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4127 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4320 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = y ∘ (x ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4442 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4635 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (y ∘ x) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation473 (G : Type*) [Magma G] (h : Equation613 G) : Equation473 G := λ x y => h x y x y x x
theorem Equation816_implies_Equation676 (G : Type*) [Magma G] (h : Equation816 G) : Equation676 G := λ x y => h x y x y x x
theorem Equation1019_implies_Equation879 (G : Type*) [Magma G] (h : Equation1019 G) : Equation879 G := λ x y => h x y x y x x
theorem Equation1222_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1082 G := λ x y => h x y x y x x
theorem Equation1425_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1285 G := λ x y => h x y x y x x
theorem Equation1628_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1488 G := λ x y => h x y x y x x
theorem Equation1831_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1691 G := λ x y => h x y x y x x
theorem Equation2034_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1894 G := λ x y => h x y x y x x
theorem Equation2237_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2097 G := λ x y => h x y x y x x
theorem Equation2440_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2300 G := λ x y => h x y x y x x
theorem Equation2643_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2503 G := λ x y => h x y x y x x
theorem Equation2846_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2706 G := λ x y => h x y x y x x
theorem Equation3049_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2909 G := λ x y => h x y x y x x
theorem Equation3252_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3112 G := λ x y => h x y x y x x
theorem Equation3455_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3315 G := λ x y => h x y x y x x
theorem Equation3658_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3518 G := λ x y => h x y x y x x
theorem Equation3861_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3721 G := λ x y => h x y x y x x
theorem Equation4064_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3924 G := λ x y => h x y x y x x
theorem Equation4267_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4127 G := λ x y => h x y x y x x
theorem Equation4379_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4320 G := λ x y => h x y x y x x
theorem Equation4582_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4442 G := λ x y => h x y x y x x
theorem Equation4694_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4635 G := λ x y => h x y x y x x