import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation476 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation679 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation882 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1085 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1288 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1491 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1694 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1897 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2100 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2303 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2506 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2709 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2912 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3115 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3318 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3521 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3724 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3927 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4130 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4445 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation476 (G : Type*) [Magma G] (h : Equation613 G) : Equation476 G := λ x y => h x y x y y x
theorem Equation816_implies_Equation679 (G : Type*) [Magma G] (h : Equation816 G) : Equation679 G := λ x y => h x y x y y x
theorem Equation1019_implies_Equation882 (G : Type*) [Magma G] (h : Equation1019 G) : Equation882 G := λ x y => h x y x y y x
theorem Equation1222_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1085 G := λ x y => h x y x y y x
theorem Equation1425_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1288 G := λ x y => h x y x y y x
theorem Equation1628_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1491 G := λ x y => h x y x y y x
theorem Equation1831_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1694 G := λ x y => h x y x y y x
theorem Equation2034_implies_Equation1897 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1897 G := λ x y => h x y x y y x
theorem Equation2237_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2100 G := λ x y => h x y x y y x
theorem Equation2440_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2303 G := λ x y => h x y x y y x
theorem Equation2643_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2506 G := λ x y => h x y x y y x
theorem Equation2846_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2709 G := λ x y => h x y x y y x
theorem Equation3049_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2912 G := λ x y => h x y x y y x
theorem Equation3252_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3115 G := λ x y => h x y x y y x
theorem Equation3455_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3318 G := λ x y => h x y x y y x
theorem Equation3658_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3521 G := λ x y => h x y x y y x
theorem Equation3861_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3724 G := λ x y => h x y x y y x
theorem Equation4064_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3927 G := λ x y => h x y x y y x
theorem Equation4267_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4130 G := λ x y => h x y x y y x
theorem Equation4582_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4445 G := λ x y => h x y x y y x