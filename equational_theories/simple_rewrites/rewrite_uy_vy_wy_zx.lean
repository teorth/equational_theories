import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation477 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation680 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation883 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1086 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1289 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1492 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1695 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1898 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2101 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2304 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2507 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2710 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2913 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3116 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3319 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3522 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3725 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3928 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4131 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4446 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation477 (G : Type*) [Magma G] (h : Equation613 G) : Equation477 G := λ x y => h x y x y y y
theorem Equation816_implies_Equation680 (G : Type*) [Magma G] (h : Equation816 G) : Equation680 G := λ x y => h x y x y y y
theorem Equation1019_implies_Equation883 (G : Type*) [Magma G] (h : Equation1019 G) : Equation883 G := λ x y => h x y x y y y
theorem Equation1222_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1086 G := λ x y => h x y x y y y
theorem Equation1425_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1289 G := λ x y => h x y x y y y
theorem Equation1628_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1492 G := λ x y => h x y x y y y
theorem Equation1831_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1695 G := λ x y => h x y x y y y
theorem Equation2034_implies_Equation1898 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1898 G := λ x y => h x y x y y y
theorem Equation2237_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2101 G := λ x y => h x y x y y y
theorem Equation2440_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2304 G := λ x y => h x y x y y y
theorem Equation2643_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2507 G := λ x y => h x y x y y y
theorem Equation2846_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2710 G := λ x y => h x y x y y y
theorem Equation3049_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2913 G := λ x y => h x y x y y y
theorem Equation3252_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3116 G := λ x y => h x y x y y y
theorem Equation3455_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3319 G := λ x y => h x y x y y y
theorem Equation3658_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3522 G := λ x y => h x y x y y y
theorem Equation3861_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3725 G := λ x y => h x y x y y y
theorem Equation4064_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3928 G := λ x y => h x y x y y y
theorem Equation4267_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4131 G := λ x y => h x y x y y y
theorem Equation4582_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4446 G := λ x y => h x y x y y y