import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation542 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation745 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation948 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1151 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1354 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1557 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1760 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1963 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2166 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2369 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2572 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2775 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2978 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3181 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3384 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3587 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3790 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3993 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4196 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4511 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation542 (G : Type*) [Magma G] (h : Equation613 G) : Equation542 G := λ x y z => h x y z x y y
theorem Equation816_implies_Equation745 (G : Type*) [Magma G] (h : Equation816 G) : Equation745 G := λ x y z => h x y z x y y
theorem Equation1019_implies_Equation948 (G : Type*) [Magma G] (h : Equation1019 G) : Equation948 G := λ x y z => h x y z x y y
theorem Equation1222_implies_Equation1151 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1151 G := λ x y z => h x y z x y y
theorem Equation1425_implies_Equation1354 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1354 G := λ x y z => h x y z x y y
theorem Equation1628_implies_Equation1557 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1557 G := λ x y z => h x y z x y y
theorem Equation1831_implies_Equation1760 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1760 G := λ x y z => h x y z x y y
theorem Equation2034_implies_Equation1963 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1963 G := λ x y z => h x y z x y y
theorem Equation2237_implies_Equation2166 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2166 G := λ x y z => h x y z x y y
theorem Equation2440_implies_Equation2369 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2369 G := λ x y z => h x y z x y y
theorem Equation2643_implies_Equation2572 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2572 G := λ x y z => h x y z x y y
theorem Equation2846_implies_Equation2775 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2775 G := λ x y z => h x y z x y y
theorem Equation3049_implies_Equation2978 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2978 G := λ x y z => h x y z x y y
theorem Equation3252_implies_Equation3181 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3181 G := λ x y z => h x y z x y y
theorem Equation3455_implies_Equation3384 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3384 G := λ x y z => h x y z x y y
theorem Equation3658_implies_Equation3587 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3587 G := λ x y z => h x y z x y y
theorem Equation3861_implies_Equation3790 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3790 G := λ x y z => h x y z x y y
theorem Equation4064_implies_Equation3993 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3993 G := λ x y z => h x y z x y y
theorem Equation4267_implies_Equation4196 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4196 G := λ x y z => h x y z x y y
theorem Equation4582_implies_Equation4511 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4511 G := λ x y z => h x y z x y y