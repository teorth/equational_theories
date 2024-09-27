import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation454 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation657 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation860 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1063 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1266 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1469 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1672 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1875 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2078 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2281 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2484 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2687 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2890 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3093 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3296 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3702 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3905 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4108 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4423 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation454 (G : Type*) [Magma G] (h : Equation613 G) : Equation454 G := λ x y z => h x x y z z x
theorem Equation816_implies_Equation657 (G : Type*) [Magma G] (h : Equation816 G) : Equation657 G := λ x y z => h x x y z z x
theorem Equation1019_implies_Equation860 (G : Type*) [Magma G] (h : Equation1019 G) : Equation860 G := λ x y z => h x x y z z x
theorem Equation1222_implies_Equation1063 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1063 G := λ x y z => h x x y z z x
theorem Equation1425_implies_Equation1266 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1266 G := λ x y z => h x x y z z x
theorem Equation1628_implies_Equation1469 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1469 G := λ x y z => h x x y z z x
theorem Equation1831_implies_Equation1672 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1672 G := λ x y z => h x x y z z x
theorem Equation2034_implies_Equation1875 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1875 G := λ x y z => h x x y z z x
theorem Equation2237_implies_Equation2078 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2078 G := λ x y z => h x x y z z x
theorem Equation2440_implies_Equation2281 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2281 G := λ x y z => h x x y z z x
theorem Equation2643_implies_Equation2484 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2484 G := λ x y z => h x x y z z x
theorem Equation2846_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2687 G := λ x y z => h x x y z z x
theorem Equation3049_implies_Equation2890 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2890 G := λ x y z => h x x y z z x
theorem Equation3252_implies_Equation3093 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3093 G := λ x y z => h x x y z z x
theorem Equation3455_implies_Equation3296 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3296 G := λ x y z => h x x y z z x
theorem Equation3658_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3499 G := λ x y z => h x x y z z x
theorem Equation3861_implies_Equation3702 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3702 G := λ x y z => h x x y z z x
theorem Equation4064_implies_Equation3905 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3905 G := λ x y z => h x x y z z x
theorem Equation4267_implies_Equation4108 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4108 G := λ x y z => h x x y z z x
theorem Equation4582_implies_Equation4423 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4423 G := λ x y z => h x x y z z x