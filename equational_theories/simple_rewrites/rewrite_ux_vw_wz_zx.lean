import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation486 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (x ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation689 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ x) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation892 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (x ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1095 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1298 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ x) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1501 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (x ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1704 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1907 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2110 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2313 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2516 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2719 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2922 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3125 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3328 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (x ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3531 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ x) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3734 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (x ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3937 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ x)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4140 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ x) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4329 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (x ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4455 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ x) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4644 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ x) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation486 (G : Type*) [Magma G] (h : Equation613 G) : Equation486 G := λ x y z w => h x y x z x w
theorem Equation816_implies_Equation689 (G : Type*) [Magma G] (h : Equation816 G) : Equation689 G := λ x y z w => h x y x z x w
theorem Equation1019_implies_Equation892 (G : Type*) [Magma G] (h : Equation1019 G) : Equation892 G := λ x y z w => h x y x z x w
theorem Equation1222_implies_Equation1095 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1095 G := λ x y z w => h x y x z x w
theorem Equation1425_implies_Equation1298 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1298 G := λ x y z w => h x y x z x w
theorem Equation1628_implies_Equation1501 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1501 G := λ x y z w => h x y x z x w
theorem Equation1831_implies_Equation1704 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1704 G := λ x y z w => h x y x z x w
theorem Equation2034_implies_Equation1907 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1907 G := λ x y z w => h x y x z x w
theorem Equation2237_implies_Equation2110 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2110 G := λ x y z w => h x y x z x w
theorem Equation2440_implies_Equation2313 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2313 G := λ x y z w => h x y x z x w
theorem Equation2643_implies_Equation2516 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2516 G := λ x y z w => h x y x z x w
theorem Equation2846_implies_Equation2719 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2719 G := λ x y z w => h x y x z x w
theorem Equation3049_implies_Equation2922 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2922 G := λ x y z w => h x y x z x w
theorem Equation3252_implies_Equation3125 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3125 G := λ x y z w => h x y x z x w
theorem Equation3455_implies_Equation3328 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3328 G := λ x y z w => h x y x z x w
theorem Equation3658_implies_Equation3531 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3531 G := λ x y z w => h x y x z x w
theorem Equation3861_implies_Equation3734 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3734 G := λ x y z w => h x y x z x w
theorem Equation4064_implies_Equation3937 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3937 G := λ x y z w => h x y x z x w
theorem Equation4267_implies_Equation4140 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4140 G := λ x y z w => h x y x z x w
theorem Equation4379_implies_Equation4329 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4329 G := λ x y z w => h x y x z x w
theorem Equation4582_implies_Equation4455 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4455 G := λ x y z w => h x y x z x w
theorem Equation4694_implies_Equation4644 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4644 G := λ x y z w => h x y x z x w