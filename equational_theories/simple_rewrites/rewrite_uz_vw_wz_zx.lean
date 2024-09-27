import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation494 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation697 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation900 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1103 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1306 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1509 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1712 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1915 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2118 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2321 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2727 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2930 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3133 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3336 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3539 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3742 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3945 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4148 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4463 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation494 (G : Type*) [Magma G] (h : Equation613 G) : Equation494 G := λ x y z w => h x y x z z w
theorem Equation816_implies_Equation697 (G : Type*) [Magma G] (h : Equation816 G) : Equation697 G := λ x y z w => h x y x z z w
theorem Equation1019_implies_Equation900 (G : Type*) [Magma G] (h : Equation1019 G) : Equation900 G := λ x y z w => h x y x z z w
theorem Equation1222_implies_Equation1103 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1103 G := λ x y z w => h x y x z z w
theorem Equation1425_implies_Equation1306 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1306 G := λ x y z w => h x y x z z w
theorem Equation1628_implies_Equation1509 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1509 G := λ x y z w => h x y x z z w
theorem Equation1831_implies_Equation1712 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1712 G := λ x y z w => h x y x z z w
theorem Equation2034_implies_Equation1915 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1915 G := λ x y z w => h x y x z z w
theorem Equation2237_implies_Equation2118 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2118 G := λ x y z w => h x y x z z w
theorem Equation2440_implies_Equation2321 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2321 G := λ x y z w => h x y x z z w
theorem Equation2643_implies_Equation2524 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2524 G := λ x y z w => h x y x z z w
theorem Equation2846_implies_Equation2727 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2727 G := λ x y z w => h x y x z z w
theorem Equation3049_implies_Equation2930 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2930 G := λ x y z w => h x y x z z w
theorem Equation3252_implies_Equation3133 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3133 G := λ x y z w => h x y x z z w
theorem Equation3455_implies_Equation3336 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3336 G := λ x y z w => h x y x z z w
theorem Equation3658_implies_Equation3539 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3539 G := λ x y z w => h x y x z z w
theorem Equation3861_implies_Equation3742 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3742 G := λ x y z w => h x y x z z w
theorem Equation4064_implies_Equation3945 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3945 G := λ x y z w => h x y x z z w
theorem Equation4267_implies_Equation4148 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4148 G := λ x y z w => h x y x z z w
theorem Equation4582_implies_Equation4463 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4463 G := λ x y z w => h x y x z z w