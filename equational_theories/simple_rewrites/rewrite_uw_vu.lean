import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (w ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ w) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (w ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ w) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (w ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2434 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2637 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2840 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3043 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3246 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3449 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (w ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3652 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ w) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3855 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (w ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4058 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ w)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4261 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ w) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4576 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ w) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation607 (G : Type*) [Magma G] (h : Equation613 G) : Equation607 G := λ x y z w u => h x y z w w u
theorem Equation816_implies_Equation810 (G : Type*) [Magma G] (h : Equation816 G) : Equation810 G := λ x y z w u => h x y z w w u
theorem Equation1019_implies_Equation1013 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1013 G := λ x y z w u => h x y z w w u
theorem Equation1222_implies_Equation1216 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1216 G := λ x y z w u => h x y z w w u
theorem Equation1425_implies_Equation1419 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1419 G := λ x y z w u => h x y z w w u
theorem Equation1628_implies_Equation1622 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1622 G := λ x y z w u => h x y z w w u
theorem Equation1831_implies_Equation1825 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1825 G := λ x y z w u => h x y z w w u
theorem Equation2034_implies_Equation2028 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2028 G := λ x y z w u => h x y z w w u
theorem Equation2237_implies_Equation2231 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2231 G := λ x y z w u => h x y z w w u
theorem Equation2440_implies_Equation2434 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2434 G := λ x y z w u => h x y z w w u
theorem Equation2643_implies_Equation2637 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2637 G := λ x y z w u => h x y z w w u
theorem Equation2846_implies_Equation2840 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2840 G := λ x y z w u => h x y z w w u
theorem Equation3049_implies_Equation3043 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3043 G := λ x y z w u => h x y z w w u
theorem Equation3252_implies_Equation3246 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3246 G := λ x y z w u => h x y z w w u
theorem Equation3455_implies_Equation3449 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3449 G := λ x y z w u => h x y z w w u
theorem Equation3658_implies_Equation3652 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3652 G := λ x y z w u => h x y z w w u
theorem Equation3861_implies_Equation3855 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3855 G := λ x y z w u => h x y z w w u
theorem Equation4064_implies_Equation4058 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4058 G := λ x y z w u => h x y z w w u
theorem Equation4267_implies_Equation4261 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4261 G := λ x y z w u => h x y z w w u
theorem Equation4582_implies_Equation4576 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4576 G := λ x y z w u => h x y z w w u