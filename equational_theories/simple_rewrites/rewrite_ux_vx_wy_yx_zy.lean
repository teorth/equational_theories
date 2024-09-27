import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation436 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation639 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation842 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1045 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1248 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1451 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1654 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1857 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2060 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2263 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2466 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2669 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2872 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3075 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3278 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3481 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3684 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3887 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4090 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4290 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (x ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4405 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4605 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ x) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation436 (G : Type*) [Magma G] (h : Equation613 G) : Equation436 G := λ x y => h x x y y x x
theorem Equation816_implies_Equation639 (G : Type*) [Magma G] (h : Equation816 G) : Equation639 G := λ x y => h x x y y x x
theorem Equation1019_implies_Equation842 (G : Type*) [Magma G] (h : Equation1019 G) : Equation842 G := λ x y => h x x y y x x
theorem Equation1222_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1045 G := λ x y => h x x y y x x
theorem Equation1425_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1248 G := λ x y => h x x y y x x
theorem Equation1628_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1451 G := λ x y => h x x y y x x
theorem Equation1831_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1654 G := λ x y => h x x y y x x
theorem Equation2034_implies_Equation1857 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1857 G := λ x y => h x x y y x x
theorem Equation2237_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2060 G := λ x y => h x x y y x x
theorem Equation2440_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2263 G := λ x y => h x x y y x x
theorem Equation2643_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2466 G := λ x y => h x x y y x x
theorem Equation2846_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2669 G := λ x y => h x x y y x x
theorem Equation3049_implies_Equation2872 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2872 G := λ x y => h x x y y x x
theorem Equation3252_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3075 G := λ x y => h x x y y x x
theorem Equation3455_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3278 G := λ x y => h x x y y x x
theorem Equation3658_implies_Equation3481 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3481 G := λ x y => h x x y y x x
theorem Equation3861_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3684 G := λ x y => h x x y y x x
theorem Equation4064_implies_Equation3887 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3887 G := λ x y => h x x y y x x
theorem Equation4267_implies_Equation4090 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4090 G := λ x y => h x x y y x x
theorem Equation4379_implies_Equation4290 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4290 G := λ x y => h x x y y x x
theorem Equation4582_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4405 G := λ x y => h x x y y x x
theorem Equation4694_implies_Equation4605 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4605 G := λ x y => h x x y y x x