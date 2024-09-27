import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation489 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation692 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation895 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1098 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1301 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1504 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1707 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1910 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2113 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2316 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2519 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2722 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2925 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3128 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3331 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3534 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3737 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3940 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4143 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4332 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4458 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4647 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation489 (G : Type*) [Magma G] (h : Equation613 G) : Equation489 G := λ x y z => h x y x z y z
theorem Equation816_implies_Equation692 (G : Type*) [Magma G] (h : Equation816 G) : Equation692 G := λ x y z => h x y x z y z
theorem Equation1019_implies_Equation895 (G : Type*) [Magma G] (h : Equation1019 G) : Equation895 G := λ x y z => h x y x z y z
theorem Equation1222_implies_Equation1098 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1098 G := λ x y z => h x y x z y z
theorem Equation1425_implies_Equation1301 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1301 G := λ x y z => h x y x z y z
theorem Equation1628_implies_Equation1504 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1504 G := λ x y z => h x y x z y z
theorem Equation1831_implies_Equation1707 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1707 G := λ x y z => h x y x z y z
theorem Equation2034_implies_Equation1910 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1910 G := λ x y z => h x y x z y z
theorem Equation2237_implies_Equation2113 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2113 G := λ x y z => h x y x z y z
theorem Equation2440_implies_Equation2316 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2316 G := λ x y z => h x y x z y z
theorem Equation2643_implies_Equation2519 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2519 G := λ x y z => h x y x z y z
theorem Equation2846_implies_Equation2722 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2722 G := λ x y z => h x y x z y z
theorem Equation3049_implies_Equation2925 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2925 G := λ x y z => h x y x z y z
theorem Equation3252_implies_Equation3128 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3128 G := λ x y z => h x y x z y z
theorem Equation3455_implies_Equation3331 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3331 G := λ x y z => h x y x z y z
theorem Equation3658_implies_Equation3534 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3534 G := λ x y z => h x y x z y z
theorem Equation3861_implies_Equation3737 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3737 G := λ x y z => h x y x z y z
theorem Equation4064_implies_Equation3940 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3940 G := λ x y z => h x y x z y z
theorem Equation4267_implies_Equation4143 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4143 G := λ x y z => h x y x z y z
theorem Equation4379_implies_Equation4332 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4332 G := λ x y z => h x y x z y z
theorem Equation4582_implies_Equation4458 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4458 G := λ x y z => h x y x z y z
theorem Equation4694_implies_Equation4647 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4647 G := λ x y z => h x y x z y z