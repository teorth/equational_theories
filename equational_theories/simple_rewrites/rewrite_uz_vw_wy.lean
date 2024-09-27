import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation565 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation768 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation971 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1174 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1377 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1783 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1986 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2189 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2392 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2595 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2798 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3001 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3204 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3610 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3813 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4016 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4219 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4534 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4680 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation565 (G : Type*) [Magma G] (h : Equation613 G) : Equation565 G := λ x y z w => h x y z y z w
theorem Equation816_implies_Equation768 (G : Type*) [Magma G] (h : Equation816 G) : Equation768 G := λ x y z w => h x y z y z w
theorem Equation1019_implies_Equation971 (G : Type*) [Magma G] (h : Equation1019 G) : Equation971 G := λ x y z w => h x y z y z w
theorem Equation1222_implies_Equation1174 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1174 G := λ x y z w => h x y z y z w
theorem Equation1425_implies_Equation1377 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1377 G := λ x y z w => h x y z y z w
theorem Equation1628_implies_Equation1580 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1580 G := λ x y z w => h x y z y z w
theorem Equation1831_implies_Equation1783 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1783 G := λ x y z w => h x y z y z w
theorem Equation2034_implies_Equation1986 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1986 G := λ x y z w => h x y z y z w
theorem Equation2237_implies_Equation2189 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2189 G := λ x y z w => h x y z y z w
theorem Equation2440_implies_Equation2392 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2392 G := λ x y z w => h x y z y z w
theorem Equation2643_implies_Equation2595 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2595 G := λ x y z w => h x y z y z w
theorem Equation2846_implies_Equation2798 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2798 G := λ x y z w => h x y z y z w
theorem Equation3049_implies_Equation3001 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3001 G := λ x y z w => h x y z y z w
theorem Equation3252_implies_Equation3204 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3204 G := λ x y z w => h x y z y z w
theorem Equation3455_implies_Equation3407 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3407 G := λ x y z w => h x y z y z w
theorem Equation3658_implies_Equation3610 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3610 G := λ x y z w => h x y z y z w
theorem Equation3861_implies_Equation3813 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3813 G := λ x y z w => h x y z y z w
theorem Equation4064_implies_Equation4016 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4016 G := λ x y z w => h x y z y z w
theorem Equation4267_implies_Equation4219 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4219 G := λ x y z w => h x y z y z w
theorem Equation4379_implies_Equation4365 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4365 G := λ x y z w => h x y z y z w
theorem Equation4582_implies_Equation4534 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4534 G := λ x y z w => h x y z y z w
theorem Equation4694_implies_Equation4680 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4680 G := λ x y z w => h x y z y z w