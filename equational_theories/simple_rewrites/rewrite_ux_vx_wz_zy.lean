import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation520 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation723 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation926 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1129 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1332 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1535 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1738 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1941 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2144 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2347 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2550 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2753 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2956 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3159 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3362 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3565 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3768 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3971 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4174 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4489 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation520 (G : Type*) [Magma G] (h : Equation613 G) : Equation520 G := λ x y z => h x y y z x x
theorem Equation816_implies_Equation723 (G : Type*) [Magma G] (h : Equation816 G) : Equation723 G := λ x y z => h x y y z x x
theorem Equation1019_implies_Equation926 (G : Type*) [Magma G] (h : Equation1019 G) : Equation926 G := λ x y z => h x y y z x x
theorem Equation1222_implies_Equation1129 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1129 G := λ x y z => h x y y z x x
theorem Equation1425_implies_Equation1332 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1332 G := λ x y z => h x y y z x x
theorem Equation1628_implies_Equation1535 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1535 G := λ x y z => h x y y z x x
theorem Equation1831_implies_Equation1738 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1738 G := λ x y z => h x y y z x x
theorem Equation2034_implies_Equation1941 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1941 G := λ x y z => h x y y z x x
theorem Equation2237_implies_Equation2144 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2144 G := λ x y z => h x y y z x x
theorem Equation2440_implies_Equation2347 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2347 G := λ x y z => h x y y z x x
theorem Equation2643_implies_Equation2550 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2550 G := λ x y z => h x y y z x x
theorem Equation2846_implies_Equation2753 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2753 G := λ x y z => h x y y z x x
theorem Equation3049_implies_Equation2956 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2956 G := λ x y z => h x y y z x x
theorem Equation3252_implies_Equation3159 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3159 G := λ x y z => h x y y z x x
theorem Equation3455_implies_Equation3362 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3362 G := λ x y z => h x y y z x x
theorem Equation3658_implies_Equation3565 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3565 G := λ x y z => h x y y z x x
theorem Equation3861_implies_Equation3768 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3768 G := λ x y z => h x y y z x x
theorem Equation4064_implies_Equation3971 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3971 G := λ x y z => h x y y z x x
theorem Equation4267_implies_Equation4174 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4174 G := λ x y z => h x y y z x x
theorem Equation4582_implies_Equation4489 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4489 G := λ x y z => h x y y z x x