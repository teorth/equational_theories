import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation438 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation641 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation844 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1047 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1250 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1453 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1656 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1859 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2062 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2265 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2468 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2671 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2874 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3077 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3280 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3483 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3686 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3889 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4092 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4292 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (x ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4407 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4607 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ x) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation438 (G : Type*) [Magma G] (h : Equation613 G) : Equation438 G := λ x y z => h x x y y x z
theorem Equation816_implies_Equation641 (G : Type*) [Magma G] (h : Equation816 G) : Equation641 G := λ x y z => h x x y y x z
theorem Equation1019_implies_Equation844 (G : Type*) [Magma G] (h : Equation1019 G) : Equation844 G := λ x y z => h x x y y x z
theorem Equation1222_implies_Equation1047 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1047 G := λ x y z => h x x y y x z
theorem Equation1425_implies_Equation1250 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1250 G := λ x y z => h x x y y x z
theorem Equation1628_implies_Equation1453 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1453 G := λ x y z => h x x y y x z
theorem Equation1831_implies_Equation1656 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1656 G := λ x y z => h x x y y x z
theorem Equation2034_implies_Equation1859 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1859 G := λ x y z => h x x y y x z
theorem Equation2237_implies_Equation2062 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2062 G := λ x y z => h x x y y x z
theorem Equation2440_implies_Equation2265 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2265 G := λ x y z => h x x y y x z
theorem Equation2643_implies_Equation2468 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2468 G := λ x y z => h x x y y x z
theorem Equation2846_implies_Equation2671 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2671 G := λ x y z => h x x y y x z
theorem Equation3049_implies_Equation2874 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2874 G := λ x y z => h x x y y x z
theorem Equation3252_implies_Equation3077 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3077 G := λ x y z => h x x y y x z
theorem Equation3455_implies_Equation3280 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3280 G := λ x y z => h x x y y x z
theorem Equation3658_implies_Equation3483 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3483 G := λ x y z => h x x y y x z
theorem Equation3861_implies_Equation3686 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3686 G := λ x y z => h x x y y x z
theorem Equation4064_implies_Equation3889 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3889 G := λ x y z => h x x y y x z
theorem Equation4267_implies_Equation4092 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4092 G := λ x y z => h x x y y x z
theorem Equation4379_implies_Equation4292 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4292 G := λ x y z => h x x y y x z
theorem Equation4582_implies_Equation4407 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4407 G := λ x y z => h x x y y x z
theorem Equation4694_implies_Equation4607 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4607 G := λ x y z => h x x y y x z