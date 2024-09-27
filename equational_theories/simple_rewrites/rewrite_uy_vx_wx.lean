import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation541 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation744 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation947 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1150 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1353 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1556 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1759 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1962 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2165 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2368 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2571 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2774 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2977 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3180 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3383 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3586 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3789 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3992 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4195 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4510 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation541 (G : Type*) [Magma G] (h : Equation613 G) : Equation541 G := λ x y z => h x y z x y x
theorem Equation816_implies_Equation744 (G : Type*) [Magma G] (h : Equation816 G) : Equation744 G := λ x y z => h x y z x y x
theorem Equation1019_implies_Equation947 (G : Type*) [Magma G] (h : Equation1019 G) : Equation947 G := λ x y z => h x y z x y x
theorem Equation1222_implies_Equation1150 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1150 G := λ x y z => h x y z x y x
theorem Equation1425_implies_Equation1353 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1353 G := λ x y z => h x y z x y x
theorem Equation1628_implies_Equation1556 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1556 G := λ x y z => h x y z x y x
theorem Equation1831_implies_Equation1759 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1759 G := λ x y z => h x y z x y x
theorem Equation2034_implies_Equation1962 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1962 G := λ x y z => h x y z x y x
theorem Equation2237_implies_Equation2165 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2165 G := λ x y z => h x y z x y x
theorem Equation2440_implies_Equation2368 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2368 G := λ x y z => h x y z x y x
theorem Equation2643_implies_Equation2571 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2571 G := λ x y z => h x y z x y x
theorem Equation2846_implies_Equation2774 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2774 G := λ x y z => h x y z x y x
theorem Equation3049_implies_Equation2977 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2977 G := λ x y z => h x y z x y x
theorem Equation3252_implies_Equation3180 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3180 G := λ x y z => h x y z x y x
theorem Equation3455_implies_Equation3383 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3383 G := λ x y z => h x y z x y x
theorem Equation3658_implies_Equation3586 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3586 G := λ x y z => h x y z x y x
theorem Equation3861_implies_Equation3789 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3789 G := λ x y z => h x y z x y x
theorem Equation4064_implies_Equation3992 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3992 G := λ x y z => h x y z x y x
theorem Equation4267_implies_Equation4195 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4195 G := λ x y z => h x y z x y x
theorem Equation4582_implies_Equation4510 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4510 G := λ x y z => h x y z x y x