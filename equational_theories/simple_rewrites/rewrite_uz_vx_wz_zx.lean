import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation491 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation694 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation897 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1100 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1303 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1506 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1709 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1912 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2115 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2318 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2521 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2724 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2927 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3130 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3333 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3536 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3739 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3942 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4145 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4460 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation491 (G : Type*) [Magma G] (h : Equation613 G) : Equation491 G := λ x y z => h x y x z z x
theorem Equation816_implies_Equation694 (G : Type*) [Magma G] (h : Equation816 G) : Equation694 G := λ x y z => h x y x z z x
theorem Equation1019_implies_Equation897 (G : Type*) [Magma G] (h : Equation1019 G) : Equation897 G := λ x y z => h x y x z z x
theorem Equation1222_implies_Equation1100 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1100 G := λ x y z => h x y x z z x
theorem Equation1425_implies_Equation1303 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1303 G := λ x y z => h x y x z z x
theorem Equation1628_implies_Equation1506 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1506 G := λ x y z => h x y x z z x
theorem Equation1831_implies_Equation1709 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1709 G := λ x y z => h x y x z z x
theorem Equation2034_implies_Equation1912 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1912 G := λ x y z => h x y x z z x
theorem Equation2237_implies_Equation2115 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2115 G := λ x y z => h x y x z z x
theorem Equation2440_implies_Equation2318 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2318 G := λ x y z => h x y x z z x
theorem Equation2643_implies_Equation2521 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2521 G := λ x y z => h x y x z z x
theorem Equation2846_implies_Equation2724 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2724 G := λ x y z => h x y x z z x
theorem Equation3049_implies_Equation2927 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2927 G := λ x y z => h x y x z z x
theorem Equation3252_implies_Equation3130 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3130 G := λ x y z => h x y x z z x
theorem Equation3455_implies_Equation3333 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3333 G := λ x y z => h x y x z z x
theorem Equation3658_implies_Equation3536 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3536 G := λ x y z => h x y x z z x
theorem Equation3861_implies_Equation3739 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3739 G := λ x y z => h x y x z z x
theorem Equation4064_implies_Equation3942 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3942 G := λ x y z => h x y x z z x
theorem Equation4267_implies_Equation4145 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4145 G := λ x y z => h x y x z z x
theorem Equation4582_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4460 G := λ x y z => h x y x z z x