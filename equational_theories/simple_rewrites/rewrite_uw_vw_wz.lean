import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation586 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation789 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation992 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1195 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1398 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1601 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1804 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2007 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2210 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2413 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2819 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3022 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3225 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3631 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3834 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4037 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4240 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4555 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation586 (G : Type*) [Magma G] (h : Equation613 G) : Equation586 G := λ x y z w => h x y z z w w
theorem Equation816_implies_Equation789 (G : Type*) [Magma G] (h : Equation816 G) : Equation789 G := λ x y z w => h x y z z w w
theorem Equation1019_implies_Equation992 (G : Type*) [Magma G] (h : Equation1019 G) : Equation992 G := λ x y z w => h x y z z w w
theorem Equation1222_implies_Equation1195 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1195 G := λ x y z w => h x y z z w w
theorem Equation1425_implies_Equation1398 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1398 G := λ x y z w => h x y z z w w
theorem Equation1628_implies_Equation1601 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1601 G := λ x y z w => h x y z z w w
theorem Equation1831_implies_Equation1804 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1804 G := λ x y z w => h x y z z w w
theorem Equation2034_implies_Equation2007 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2007 G := λ x y z w => h x y z z w w
theorem Equation2237_implies_Equation2210 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2210 G := λ x y z w => h x y z z w w
theorem Equation2440_implies_Equation2413 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2413 G := λ x y z w => h x y z z w w
theorem Equation2643_implies_Equation2616 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2616 G := λ x y z w => h x y z z w w
theorem Equation2846_implies_Equation2819 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2819 G := λ x y z w => h x y z z w w
theorem Equation3049_implies_Equation3022 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3022 G := λ x y z w => h x y z z w w
theorem Equation3252_implies_Equation3225 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3225 G := λ x y z w => h x y z z w w
theorem Equation3455_implies_Equation3428 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3428 G := λ x y z w => h x y z z w w
theorem Equation3658_implies_Equation3631 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3631 G := λ x y z w => h x y z z w w
theorem Equation3861_implies_Equation3834 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3834 G := λ x y z w => h x y z z w w
theorem Equation4064_implies_Equation4037 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4037 G := λ x y z w => h x y z z w w
theorem Equation4267_implies_Equation4240 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4240 G := λ x y z w => h x y z z w w
theorem Equation4582_implies_Equation4555 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4555 G := λ x y z w => h x y z z w w