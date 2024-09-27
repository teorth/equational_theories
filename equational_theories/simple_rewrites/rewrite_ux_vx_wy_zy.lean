import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation510 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation713 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation916 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1119 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1322 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1525 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1728 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1931 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2134 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2337 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2540 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2743 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2946 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3149 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3352 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3555 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3758 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3961 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4164 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4343 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = y ∘ (x ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4479 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4658 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ y) ∘ y = (y ∘ x) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation510 (G : Type*) [Magma G] (h : Equation613 G) : Equation510 G := λ x y => h x y y y x x
theorem Equation816_implies_Equation713 (G : Type*) [Magma G] (h : Equation816 G) : Equation713 G := λ x y => h x y y y x x
theorem Equation1019_implies_Equation916 (G : Type*) [Magma G] (h : Equation1019 G) : Equation916 G := λ x y => h x y y y x x
theorem Equation1222_implies_Equation1119 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1119 G := λ x y => h x y y y x x
theorem Equation1425_implies_Equation1322 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1322 G := λ x y => h x y y y x x
theorem Equation1628_implies_Equation1525 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1525 G := λ x y => h x y y y x x
theorem Equation1831_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1728 G := λ x y => h x y y y x x
theorem Equation2034_implies_Equation1931 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1931 G := λ x y => h x y y y x x
theorem Equation2237_implies_Equation2134 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2134 G := λ x y => h x y y y x x
theorem Equation2440_implies_Equation2337 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2337 G := λ x y => h x y y y x x
theorem Equation2643_implies_Equation2540 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2540 G := λ x y => h x y y y x x
theorem Equation2846_implies_Equation2743 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2743 G := λ x y => h x y y y x x
theorem Equation3049_implies_Equation2946 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2946 G := λ x y => h x y y y x x
theorem Equation3252_implies_Equation3149 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3149 G := λ x y => h x y y y x x
theorem Equation3455_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3352 G := λ x y => h x y y y x x
theorem Equation3658_implies_Equation3555 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3555 G := λ x y => h x y y y x x
theorem Equation3861_implies_Equation3758 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3758 G := λ x y => h x y y y x x
theorem Equation4064_implies_Equation3961 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3961 G := λ x y => h x y y y x x
theorem Equation4267_implies_Equation4164 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4164 G := λ x y => h x y y y x x
theorem Equation4379_implies_Equation4343 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4343 G := λ x y => h x y y y x x
theorem Equation4582_implies_Equation4479 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4479 G := λ x y => h x y y y x x
theorem Equation4694_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4658 G := λ x y => h x y y y x x