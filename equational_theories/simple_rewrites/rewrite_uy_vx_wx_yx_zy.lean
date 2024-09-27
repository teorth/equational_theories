import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation429 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation632 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation835 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1038 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1241 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1444 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1647 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1850 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2053 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2256 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2459 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2662 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2865 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3068 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3271 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3474 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3677 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3880 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4083 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4283 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4398 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4598 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation429 (G : Type*) [Magma G] (h : Equation613 G) : Equation429 G := λ x y => h x x y x y x
theorem Equation816_implies_Equation632 (G : Type*) [Magma G] (h : Equation816 G) : Equation632 G := λ x y => h x x y x y x
theorem Equation1019_implies_Equation835 (G : Type*) [Magma G] (h : Equation1019 G) : Equation835 G := λ x y => h x x y x y x
theorem Equation1222_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1038 G := λ x y => h x x y x y x
theorem Equation1425_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1241 G := λ x y => h x x y x y x
theorem Equation1628_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1444 G := λ x y => h x x y x y x
theorem Equation1831_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1647 G := λ x y => h x x y x y x
theorem Equation2034_implies_Equation1850 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1850 G := λ x y => h x x y x y x
theorem Equation2237_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2053 G := λ x y => h x x y x y x
theorem Equation2440_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2256 G := λ x y => h x x y x y x
theorem Equation2643_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2459 G := λ x y => h x x y x y x
theorem Equation2846_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2662 G := λ x y => h x x y x y x
theorem Equation3049_implies_Equation2865 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2865 G := λ x y => h x x y x y x
theorem Equation3252_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3068 G := λ x y => h x x y x y x
theorem Equation3455_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3271 G := λ x y => h x x y x y x
theorem Equation3658_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3474 G := λ x y => h x x y x y x
theorem Equation3861_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3677 G := λ x y => h x x y x y x
theorem Equation4064_implies_Equation3880 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3880 G := λ x y => h x x y x y x
theorem Equation4267_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4083 G := λ x y => h x x y x y x
theorem Equation4379_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4283 G := λ x y => h x x y x y x
theorem Equation4582_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4398 G := λ x y => h x x y x y x
theorem Equation4694_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4598 G := λ x y => h x x y x y x