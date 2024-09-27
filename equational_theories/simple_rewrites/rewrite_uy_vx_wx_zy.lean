import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation503 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation706 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation909 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1112 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1315 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1518 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1721 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1924 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2127 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2330 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2533 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2736 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2939 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3142 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3345 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3548 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3751 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3954 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4157 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4472 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation503 (G : Type*) [Magma G] (h : Equation613 G) : Equation503 G := λ x y => h x y y x y x
theorem Equation816_implies_Equation706 (G : Type*) [Magma G] (h : Equation816 G) : Equation706 G := λ x y => h x y y x y x
theorem Equation1019_implies_Equation909 (G : Type*) [Magma G] (h : Equation1019 G) : Equation909 G := λ x y => h x y y x y x
theorem Equation1222_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1112 G := λ x y => h x y y x y x
theorem Equation1425_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1315 G := λ x y => h x y y x y x
theorem Equation1628_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1518 G := λ x y => h x y y x y x
theorem Equation1831_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1721 G := λ x y => h x y y x y x
theorem Equation2034_implies_Equation1924 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1924 G := λ x y => h x y y x y x
theorem Equation2237_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2127 G := λ x y => h x y y x y x
theorem Equation2440_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2330 G := λ x y => h x y y x y x
theorem Equation2643_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2533 G := λ x y => h x y y x y x
theorem Equation2846_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2736 G := λ x y => h x y y x y x
theorem Equation3049_implies_Equation2939 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2939 G := λ x y => h x y y x y x
theorem Equation3252_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3142 G := λ x y => h x y y x y x
theorem Equation3455_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3345 G := λ x y => h x y y x y x
theorem Equation3658_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3548 G := λ x y => h x y y x y x
theorem Equation3861_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3751 G := λ x y => h x y y x y x
theorem Equation4064_implies_Equation3954 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3954 G := λ x y => h x y y x y x
theorem Equation4267_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4157 G := λ x y => h x y y x y x
theorem Equation4582_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4472 G := λ x y => h x y y x y x