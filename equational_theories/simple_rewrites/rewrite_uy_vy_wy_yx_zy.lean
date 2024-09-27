import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation440 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation643 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation846 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1049 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1252 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1455 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1658 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1861 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2064 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2267 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2470 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2673 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2876 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3079 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3282 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3485 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3688 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3891 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4094 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4409 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation440 (G : Type*) [Magma G] (h : Equation613 G) : Equation440 G := λ x y => h x x y y y y
theorem Equation816_implies_Equation643 (G : Type*) [Magma G] (h : Equation816 G) : Equation643 G := λ x y => h x x y y y y
theorem Equation1019_implies_Equation846 (G : Type*) [Magma G] (h : Equation1019 G) : Equation846 G := λ x y => h x x y y y y
theorem Equation1222_implies_Equation1049 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1049 G := λ x y => h x x y y y y
theorem Equation1425_implies_Equation1252 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1252 G := λ x y => h x x y y y y
theorem Equation1628_implies_Equation1455 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1455 G := λ x y => h x x y y y y
theorem Equation1831_implies_Equation1658 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1658 G := λ x y => h x x y y y y
theorem Equation2034_implies_Equation1861 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1861 G := λ x y => h x x y y y y
theorem Equation2237_implies_Equation2064 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2064 G := λ x y => h x x y y y y
theorem Equation2440_implies_Equation2267 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2267 G := λ x y => h x x y y y y
theorem Equation2643_implies_Equation2470 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2470 G := λ x y => h x x y y y y
theorem Equation2846_implies_Equation2673 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2673 G := λ x y => h x x y y y y
theorem Equation3049_implies_Equation2876 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2876 G := λ x y => h x x y y y y
theorem Equation3252_implies_Equation3079 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3079 G := λ x y => h x x y y y y
theorem Equation3455_implies_Equation3282 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3282 G := λ x y => h x x y y y y
theorem Equation3658_implies_Equation3485 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3485 G := λ x y => h x x y y y y
theorem Equation3861_implies_Equation3688 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3688 G := λ x y => h x x y y y y
theorem Equation4064_implies_Equation3891 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3891 G := λ x y => h x x y y y y
theorem Equation4267_implies_Equation4094 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4094 G := λ x y => h x x y y y y
theorem Equation4582_implies_Equation4409 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4409 G := λ x y => h x x y y y y