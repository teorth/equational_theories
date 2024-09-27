import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation538 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation741 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation944 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1147 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1350 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1553 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1756 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1959 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2162 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2365 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2568 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2771 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2974 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3177 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3380 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3583 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3786 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3989 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4192 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4507 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation538 (G : Type*) [Magma G] (h : Equation613 G) : Equation538 G := λ x y z => h x y z x x y
theorem Equation816_implies_Equation741 (G : Type*) [Magma G] (h : Equation816 G) : Equation741 G := λ x y z => h x y z x x y
theorem Equation1019_implies_Equation944 (G : Type*) [Magma G] (h : Equation1019 G) : Equation944 G := λ x y z => h x y z x x y
theorem Equation1222_implies_Equation1147 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1147 G := λ x y z => h x y z x x y
theorem Equation1425_implies_Equation1350 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1350 G := λ x y z => h x y z x x y
theorem Equation1628_implies_Equation1553 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1553 G := λ x y z => h x y z x x y
theorem Equation1831_implies_Equation1756 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1756 G := λ x y z => h x y z x x y
theorem Equation2034_implies_Equation1959 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1959 G := λ x y z => h x y z x x y
theorem Equation2237_implies_Equation2162 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2162 G := λ x y z => h x y z x x y
theorem Equation2440_implies_Equation2365 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2365 G := λ x y z => h x y z x x y
theorem Equation2643_implies_Equation2568 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2568 G := λ x y z => h x y z x x y
theorem Equation2846_implies_Equation2771 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2771 G := λ x y z => h x y z x x y
theorem Equation3049_implies_Equation2974 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2974 G := λ x y z => h x y z x x y
theorem Equation3252_implies_Equation3177 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3177 G := λ x y z => h x y z x x y
theorem Equation3455_implies_Equation3380 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3380 G := λ x y z => h x y z x x y
theorem Equation3658_implies_Equation3583 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3583 G := λ x y z => h x y z x x y
theorem Equation3861_implies_Equation3786 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3786 G := λ x y z => h x y z x x y
theorem Equation4064_implies_Equation3989 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3989 G := λ x y z => h x y z x x y
theorem Equation4267_implies_Equation4192 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4192 G := λ x y z => h x y z x x y
theorem Equation4582_implies_Equation4507 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4507 G := λ x y z => h x y z x x y