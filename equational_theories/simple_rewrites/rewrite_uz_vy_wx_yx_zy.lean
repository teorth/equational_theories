import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation433 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation636 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation839 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1042 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1245 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1448 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1651 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1854 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2057 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2260 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2463 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2666 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2869 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3072 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3275 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3478 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3681 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3884 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4087 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4287 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4402 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4602 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation433 (G : Type*) [Magma G] (h : Equation613 G) : Equation433 G := λ x y z => h x x y x z y
theorem Equation816_implies_Equation636 (G : Type*) [Magma G] (h : Equation816 G) : Equation636 G := λ x y z => h x x y x z y
theorem Equation1019_implies_Equation839 (G : Type*) [Magma G] (h : Equation1019 G) : Equation839 G := λ x y z => h x x y x z y
theorem Equation1222_implies_Equation1042 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1042 G := λ x y z => h x x y x z y
theorem Equation1425_implies_Equation1245 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1245 G := λ x y z => h x x y x z y
theorem Equation1628_implies_Equation1448 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1448 G := λ x y z => h x x y x z y
theorem Equation1831_implies_Equation1651 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1651 G := λ x y z => h x x y x z y
theorem Equation2034_implies_Equation1854 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1854 G := λ x y z => h x x y x z y
theorem Equation2237_implies_Equation2057 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2057 G := λ x y z => h x x y x z y
theorem Equation2440_implies_Equation2260 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2260 G := λ x y z => h x x y x z y
theorem Equation2643_implies_Equation2463 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2463 G := λ x y z => h x x y x z y
theorem Equation2846_implies_Equation2666 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2666 G := λ x y z => h x x y x z y
theorem Equation3049_implies_Equation2869 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2869 G := λ x y z => h x x y x z y
theorem Equation3252_implies_Equation3072 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3072 G := λ x y z => h x x y x z y
theorem Equation3455_implies_Equation3275 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3275 G := λ x y z => h x x y x z y
theorem Equation3658_implies_Equation3478 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3478 G := λ x y z => h x x y x z y
theorem Equation3861_implies_Equation3681 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3681 G := λ x y z => h x x y x z y
theorem Equation4064_implies_Equation3884 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3884 G := λ x y z => h x x y x z y
theorem Equation4267_implies_Equation4087 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4087 G := λ x y z => h x x y x z y
theorem Equation4379_implies_Equation4287 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4287 G := λ x y z => h x x y x z y
theorem Equation4582_implies_Equation4402 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4402 G := λ x y z => h x x y x z y
theorem Equation4694_implies_Equation4602 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4602 G := λ x y z => h x x y x z y