import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation593 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation796 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation999 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1202 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1405 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1811 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2014 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2217 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2420 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2623 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2826 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3029 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3232 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3435 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3638 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3841 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4044 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4247 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4562 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation593 (G : Type*) [Magma G] (h : Equation613 G) : Equation593 G := λ x y z w => h x y z w y x
theorem Equation816_implies_Equation796 (G : Type*) [Magma G] (h : Equation816 G) : Equation796 G := λ x y z w => h x y z w y x
theorem Equation1019_implies_Equation999 (G : Type*) [Magma G] (h : Equation1019 G) : Equation999 G := λ x y z w => h x y z w y x
theorem Equation1222_implies_Equation1202 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1202 G := λ x y z w => h x y z w y x
theorem Equation1425_implies_Equation1405 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1405 G := λ x y z w => h x y z w y x
theorem Equation1628_implies_Equation1608 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1608 G := λ x y z w => h x y z w y x
theorem Equation1831_implies_Equation1811 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1811 G := λ x y z w => h x y z w y x
theorem Equation2034_implies_Equation2014 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2014 G := λ x y z w => h x y z w y x
theorem Equation2237_implies_Equation2217 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2217 G := λ x y z w => h x y z w y x
theorem Equation2440_implies_Equation2420 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2420 G := λ x y z w => h x y z w y x
theorem Equation2643_implies_Equation2623 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2623 G := λ x y z w => h x y z w y x
theorem Equation2846_implies_Equation2826 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2826 G := λ x y z w => h x y z w y x
theorem Equation3049_implies_Equation3029 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3029 G := λ x y z w => h x y z w y x
theorem Equation3252_implies_Equation3232 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3232 G := λ x y z w => h x y z w y x
theorem Equation3455_implies_Equation3435 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3435 G := λ x y z w => h x y z w y x
theorem Equation3658_implies_Equation3638 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3638 G := λ x y z w => h x y z w y x
theorem Equation3861_implies_Equation3841 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3841 G := λ x y z w => h x y z w y x
theorem Equation4064_implies_Equation4044 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4044 G := λ x y z w => h x y z w y x
theorem Equation4267_implies_Equation4247 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4247 G := λ x y z w => h x y z w y x
theorem Equation4582_implies_Equation4562 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4562 G := λ x y z w => h x y z w y x