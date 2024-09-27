import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation531 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation734 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation937 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1140 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1343 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1546 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1749 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1952 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2155 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2358 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2561 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2764 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2967 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3170 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3576 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3779 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3982 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4185 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4500 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation531 (G : Type*) [Magma G] (h : Equation613 G) : Equation531 G := λ x y z w => h x y y z z w
theorem Equation816_implies_Equation734 (G : Type*) [Magma G] (h : Equation816 G) : Equation734 G := λ x y z w => h x y y z z w
theorem Equation1019_implies_Equation937 (G : Type*) [Magma G] (h : Equation1019 G) : Equation937 G := λ x y z w => h x y y z z w
theorem Equation1222_implies_Equation1140 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1140 G := λ x y z w => h x y y z z w
theorem Equation1425_implies_Equation1343 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1343 G := λ x y z w => h x y y z z w
theorem Equation1628_implies_Equation1546 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1546 G := λ x y z w => h x y y z z w
theorem Equation1831_implies_Equation1749 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1749 G := λ x y z w => h x y y z z w
theorem Equation2034_implies_Equation1952 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1952 G := λ x y z w => h x y y z z w
theorem Equation2237_implies_Equation2155 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2155 G := λ x y z w => h x y y z z w
theorem Equation2440_implies_Equation2358 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2358 G := λ x y z w => h x y y z z w
theorem Equation2643_implies_Equation2561 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2561 G := λ x y z w => h x y y z z w
theorem Equation2846_implies_Equation2764 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2764 G := λ x y z w => h x y y z z w
theorem Equation3049_implies_Equation2967 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2967 G := λ x y z w => h x y y z z w
theorem Equation3252_implies_Equation3170 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3170 G := λ x y z w => h x y y z z w
theorem Equation3455_implies_Equation3373 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3373 G := λ x y z w => h x y y z z w
theorem Equation3658_implies_Equation3576 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3576 G := λ x y z w => h x y y z z w
theorem Equation3861_implies_Equation3779 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3779 G := λ x y z w => h x y y z z w
theorem Equation4064_implies_Equation3982 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3982 G := λ x y z w => h x y y z z w
theorem Equation4267_implies_Equation4185 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4185 G := λ x y z w => h x y y z z w
theorem Equation4582_implies_Equation4500 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4500 G := λ x y z w => h x y y z z w