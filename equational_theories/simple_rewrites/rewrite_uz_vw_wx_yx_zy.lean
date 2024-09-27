import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation435 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation638 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation841 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1044 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1247 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1450 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1653 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1856 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2059 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2262 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2465 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2668 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2871 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3074 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3277 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (x ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3480 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((x ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3683 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ x) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3886 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (x ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4089 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ x) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4289 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = x ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4404 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (x ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4604 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (x ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation435 (G : Type*) [Magma G] (h : Equation613 G) : Equation435 G := λ x y z w => h x x y x z w
theorem Equation816_implies_Equation638 (G : Type*) [Magma G] (h : Equation816 G) : Equation638 G := λ x y z w => h x x y x z w
theorem Equation1019_implies_Equation841 (G : Type*) [Magma G] (h : Equation1019 G) : Equation841 G := λ x y z w => h x x y x z w
theorem Equation1222_implies_Equation1044 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1044 G := λ x y z w => h x x y x z w
theorem Equation1425_implies_Equation1247 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1247 G := λ x y z w => h x x y x z w
theorem Equation1628_implies_Equation1450 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1450 G := λ x y z w => h x x y x z w
theorem Equation1831_implies_Equation1653 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1653 G := λ x y z w => h x x y x z w
theorem Equation2034_implies_Equation1856 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1856 G := λ x y z w => h x x y x z w
theorem Equation2237_implies_Equation2059 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2059 G := λ x y z w => h x x y x z w
theorem Equation2440_implies_Equation2262 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2262 G := λ x y z w => h x x y x z w
theorem Equation2643_implies_Equation2465 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2465 G := λ x y z w => h x x y x z w
theorem Equation2846_implies_Equation2668 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2668 G := λ x y z w => h x x y x z w
theorem Equation3049_implies_Equation2871 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2871 G := λ x y z w => h x x y x z w
theorem Equation3252_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3074 G := λ x y z w => h x x y x z w
theorem Equation3455_implies_Equation3277 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3277 G := λ x y z w => h x x y x z w
theorem Equation3658_implies_Equation3480 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3480 G := λ x y z w => h x x y x z w
theorem Equation3861_implies_Equation3683 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3683 G := λ x y z w => h x x y x z w
theorem Equation4064_implies_Equation3886 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3886 G := λ x y z w => h x x y x z w
theorem Equation4267_implies_Equation4089 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4089 G := λ x y z w => h x x y x z w
theorem Equation4379_implies_Equation4289 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4289 G := λ x y z w => h x x y x z w
theorem Equation4582_implies_Equation4404 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4404 G := λ x y z w => h x x y x z w
theorem Equation4694_implies_Equation4604 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4604 G := λ x y z w => h x x y x z w