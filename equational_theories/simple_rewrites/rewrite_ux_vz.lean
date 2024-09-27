import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation590 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation793 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation996 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1199 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1402 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1605 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1808 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2011 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2214 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2417 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2620 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2823 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3026 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3229 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3432 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3635 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3838 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4041 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4244 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4559 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation590 (G : Type*) [Magma G] (h : Equation613 G) : Equation590 G := λ x y z w => h x y z w x z
theorem Equation816_implies_Equation793 (G : Type*) [Magma G] (h : Equation816 G) : Equation793 G := λ x y z w => h x y z w x z
theorem Equation1019_implies_Equation996 (G : Type*) [Magma G] (h : Equation1019 G) : Equation996 G := λ x y z w => h x y z w x z
theorem Equation1222_implies_Equation1199 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1199 G := λ x y z w => h x y z w x z
theorem Equation1425_implies_Equation1402 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1402 G := λ x y z w => h x y z w x z
theorem Equation1628_implies_Equation1605 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1605 G := λ x y z w => h x y z w x z
theorem Equation1831_implies_Equation1808 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1808 G := λ x y z w => h x y z w x z
theorem Equation2034_implies_Equation2011 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2011 G := λ x y z w => h x y z w x z
theorem Equation2237_implies_Equation2214 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2214 G := λ x y z w => h x y z w x z
theorem Equation2440_implies_Equation2417 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2417 G := λ x y z w => h x y z w x z
theorem Equation2643_implies_Equation2620 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2620 G := λ x y z w => h x y z w x z
theorem Equation2846_implies_Equation2823 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2823 G := λ x y z w => h x y z w x z
theorem Equation3049_implies_Equation3026 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3026 G := λ x y z w => h x y z w x z
theorem Equation3252_implies_Equation3229 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3229 G := λ x y z w => h x y z w x z
theorem Equation3455_implies_Equation3432 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3432 G := λ x y z w => h x y z w x z
theorem Equation3658_implies_Equation3635 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3635 G := λ x y z w => h x y z w x z
theorem Equation3861_implies_Equation3838 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3838 G := λ x y z w => h x y z w x z
theorem Equation4064_implies_Equation4041 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4041 G := λ x y z w => h x y z w x z
theorem Equation4267_implies_Equation4244 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4244 G := λ x y z w => h x y z w x z
theorem Equation4582_implies_Equation4559 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4559 G := λ x y z w => h x y z w x z