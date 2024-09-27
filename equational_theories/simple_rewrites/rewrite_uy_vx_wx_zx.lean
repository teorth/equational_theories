import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation466 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation669 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation872 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1075 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1278 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1481 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1684 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1887 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2090 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2293 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2496 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2699 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2902 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3105 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3308 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3511 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3714 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3917 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4120 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4435 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation466 (G : Type*) [Magma G] (h : Equation613 G) : Equation466 G := λ x y => h x y x x y x
theorem Equation816_implies_Equation669 (G : Type*) [Magma G] (h : Equation816 G) : Equation669 G := λ x y => h x y x x y x
theorem Equation1019_implies_Equation872 (G : Type*) [Magma G] (h : Equation1019 G) : Equation872 G := λ x y => h x y x x y x
theorem Equation1222_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1075 G := λ x y => h x y x x y x
theorem Equation1425_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1278 G := λ x y => h x y x x y x
theorem Equation1628_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1481 G := λ x y => h x y x x y x
theorem Equation1831_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1684 G := λ x y => h x y x x y x
theorem Equation2034_implies_Equation1887 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1887 G := λ x y => h x y x x y x
theorem Equation2237_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2090 G := λ x y => h x y x x y x
theorem Equation2440_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2293 G := λ x y => h x y x x y x
theorem Equation2643_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2496 G := λ x y => h x y x x y x
theorem Equation2846_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2699 G := λ x y => h x y x x y x
theorem Equation3049_implies_Equation2902 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2902 G := λ x y => h x y x x y x
theorem Equation3252_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3105 G := λ x y => h x y x x y x
theorem Equation3455_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3308 G := λ x y => h x y x x y x
theorem Equation3658_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3511 G := λ x y => h x y x x y x
theorem Equation3861_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3714 G := λ x y => h x y x x y x
theorem Equation4064_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3917 G := λ x y => h x y x x y x
theorem Equation4267_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4120 G := λ x y => h x y x x y x
theorem Equation4582_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4435 G := λ x y => h x y x x y x