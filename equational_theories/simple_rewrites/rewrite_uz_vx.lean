import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation598 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation801 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1004 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1207 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1410 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1613 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1816 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2019 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2222 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2425 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2628 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2831 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3034 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3237 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3440 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3643 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3846 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4049 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4252 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4567 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation598 (G : Type*) [Magma G] (h : Equation613 G) : Equation598 G := λ x y z w => h x y z w z x
theorem Equation816_implies_Equation801 (G : Type*) [Magma G] (h : Equation816 G) : Equation801 G := λ x y z w => h x y z w z x
theorem Equation1019_implies_Equation1004 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1004 G := λ x y z w => h x y z w z x
theorem Equation1222_implies_Equation1207 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1207 G := λ x y z w => h x y z w z x
theorem Equation1425_implies_Equation1410 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1410 G := λ x y z w => h x y z w z x
theorem Equation1628_implies_Equation1613 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1613 G := λ x y z w => h x y z w z x
theorem Equation1831_implies_Equation1816 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1816 G := λ x y z w => h x y z w z x
theorem Equation2034_implies_Equation2019 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2019 G := λ x y z w => h x y z w z x
theorem Equation2237_implies_Equation2222 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2222 G := λ x y z w => h x y z w z x
theorem Equation2440_implies_Equation2425 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2425 G := λ x y z w => h x y z w z x
theorem Equation2643_implies_Equation2628 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2628 G := λ x y z w => h x y z w z x
theorem Equation2846_implies_Equation2831 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2831 G := λ x y z w => h x y z w z x
theorem Equation3049_implies_Equation3034 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3034 G := λ x y z w => h x y z w z x
theorem Equation3252_implies_Equation3237 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3237 G := λ x y z w => h x y z w z x
theorem Equation3455_implies_Equation3440 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3440 G := λ x y z w => h x y z w z x
theorem Equation3658_implies_Equation3643 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3643 G := λ x y z w => h x y z w z x
theorem Equation3861_implies_Equation3846 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3846 G := λ x y z w => h x y z w z x
theorem Equation4064_implies_Equation4049 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4049 G := λ x y z w => h x y z w z x
theorem Equation4267_implies_Equation4252 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4252 G := λ x y z w => h x y z w z x
theorem Equation4582_implies_Equation4567 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4567 G := λ x y z w => h x y z w z x