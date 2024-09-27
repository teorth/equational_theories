import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation500 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation703 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation906 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1109 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1312 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1515 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1718 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1921 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2124 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2327 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2530 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2733 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2936 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3139 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3342 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3545 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3748 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3951 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4154 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4469 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation500 (G : Type*) [Magma G] (h : Equation613 G) : Equation500 G := λ x y => h x y y x x x
theorem Equation816_implies_Equation703 (G : Type*) [Magma G] (h : Equation816 G) : Equation703 G := λ x y => h x y y x x x
theorem Equation1019_implies_Equation906 (G : Type*) [Magma G] (h : Equation1019 G) : Equation906 G := λ x y => h x y y x x x
theorem Equation1222_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1109 G := λ x y => h x y y x x x
theorem Equation1425_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1312 G := λ x y => h x y y x x x
theorem Equation1628_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1515 G := λ x y => h x y y x x x
theorem Equation1831_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1718 G := λ x y => h x y y x x x
theorem Equation2034_implies_Equation1921 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1921 G := λ x y => h x y y x x x
theorem Equation2237_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2124 G := λ x y => h x y y x x x
theorem Equation2440_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2327 G := λ x y => h x y y x x x
theorem Equation2643_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2530 G := λ x y => h x y y x x x
theorem Equation2846_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2733 G := λ x y => h x y y x x x
theorem Equation3049_implies_Equation2936 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2936 G := λ x y => h x y y x x x
theorem Equation3252_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3139 G := λ x y => h x y y x x x
theorem Equation3455_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3342 G := λ x y => h x y y x x x
theorem Equation3658_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3545 G := λ x y => h x y y x x x
theorem Equation3861_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3748 G := λ x y => h x y y x x x
theorem Equation4064_implies_Equation3951 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3951 G := λ x y => h x y y x x x
theorem Equation4267_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4154 G := λ x y => h x y y x x x
theorem Equation4582_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4469 G := λ x y => h x y y x x x