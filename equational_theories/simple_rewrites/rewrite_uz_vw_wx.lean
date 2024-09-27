import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation548 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation751 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation954 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1157 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1360 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1766 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1969 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2172 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2375 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2578 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2781 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2984 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3187 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3390 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3593 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3796 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3999 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4202 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4359 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4674 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation548 (G : Type*) [Magma G] (h : Equation613 G) : Equation548 G := λ x y z w => h x y z x z w
theorem Equation816_implies_Equation751 (G : Type*) [Magma G] (h : Equation816 G) : Equation751 G := λ x y z w => h x y z x z w
theorem Equation1019_implies_Equation954 (G : Type*) [Magma G] (h : Equation1019 G) : Equation954 G := λ x y z w => h x y z x z w
theorem Equation1222_implies_Equation1157 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1157 G := λ x y z w => h x y z x z w
theorem Equation1425_implies_Equation1360 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1360 G := λ x y z w => h x y z x z w
theorem Equation1628_implies_Equation1563 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1563 G := λ x y z w => h x y z x z w
theorem Equation1831_implies_Equation1766 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1766 G := λ x y z w => h x y z x z w
theorem Equation2034_implies_Equation1969 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1969 G := λ x y z w => h x y z x z w
theorem Equation2237_implies_Equation2172 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2172 G := λ x y z w => h x y z x z w
theorem Equation2440_implies_Equation2375 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2375 G := λ x y z w => h x y z x z w
theorem Equation2643_implies_Equation2578 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2578 G := λ x y z w => h x y z x z w
theorem Equation2846_implies_Equation2781 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2781 G := λ x y z w => h x y z x z w
theorem Equation3049_implies_Equation2984 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2984 G := λ x y z w => h x y z x z w
theorem Equation3252_implies_Equation3187 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3187 G := λ x y z w => h x y z x z w
theorem Equation3455_implies_Equation3390 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3390 G := λ x y z w => h x y z x z w
theorem Equation3658_implies_Equation3593 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3593 G := λ x y z w => h x y z x z w
theorem Equation3861_implies_Equation3796 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3796 G := λ x y z w => h x y z x z w
theorem Equation4064_implies_Equation3999 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3999 G := λ x y z w => h x y z x z w
theorem Equation4267_implies_Equation4202 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4202 G := λ x y z w => h x y z x z w
theorem Equation4379_implies_Equation4359 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4359 G := λ x y z w => h x y z x z w
theorem Equation4582_implies_Equation4517 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4517 G := λ x y z w => h x y z x z w
theorem Equation4694_implies_Equation4674 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4674 G := λ x y z w => h x y z x z w