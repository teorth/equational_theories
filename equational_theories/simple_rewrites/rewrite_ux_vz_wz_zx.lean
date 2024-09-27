import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation485 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation688 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation891 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1094 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1297 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1500 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1703 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1906 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2109 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2312 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2515 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2718 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2921 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3124 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3327 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3530 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3733 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3936 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4139 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4454 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation485 (G : Type*) [Magma G] (h : Equation613 G) : Equation485 G := λ x y z => h x y x z x z
theorem Equation816_implies_Equation688 (G : Type*) [Magma G] (h : Equation816 G) : Equation688 G := λ x y z => h x y x z x z
theorem Equation1019_implies_Equation891 (G : Type*) [Magma G] (h : Equation1019 G) : Equation891 G := λ x y z => h x y x z x z
theorem Equation1222_implies_Equation1094 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1094 G := λ x y z => h x y x z x z
theorem Equation1425_implies_Equation1297 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1297 G := λ x y z => h x y x z x z
theorem Equation1628_implies_Equation1500 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1500 G := λ x y z => h x y x z x z
theorem Equation1831_implies_Equation1703 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1703 G := λ x y z => h x y x z x z
theorem Equation2034_implies_Equation1906 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1906 G := λ x y z => h x y x z x z
theorem Equation2237_implies_Equation2109 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2109 G := λ x y z => h x y x z x z
theorem Equation2440_implies_Equation2312 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2312 G := λ x y z => h x y x z x z
theorem Equation2643_implies_Equation2515 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2515 G := λ x y z => h x y x z x z
theorem Equation2846_implies_Equation2718 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2718 G := λ x y z => h x y x z x z
theorem Equation3049_implies_Equation2921 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2921 G := λ x y z => h x y x z x z
theorem Equation3252_implies_Equation3124 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3124 G := λ x y z => h x y x z x z
theorem Equation3455_implies_Equation3327 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3327 G := λ x y z => h x y x z x z
theorem Equation3658_implies_Equation3530 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3530 G := λ x y z => h x y x z x z
theorem Equation3861_implies_Equation3733 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3733 G := λ x y z => h x y x z x z
theorem Equation4064_implies_Equation3936 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3936 G := λ x y z => h x y x z x z
theorem Equation4267_implies_Equation4139 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4139 G := λ x y z => h x y x z x z
theorem Equation4582_implies_Equation4454 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4454 G := λ x y z => h x y x z x z