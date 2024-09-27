import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation609 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation812 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1015 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1218 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1421 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1624 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1827 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2030 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2233 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2436 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2639 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2842 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3045 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3248 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3451 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3654 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3857 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4060 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4263 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4578 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation609 (G : Type*) [Magma G] (h : Equation613 G) : Equation609 G := λ x y z w u => h x y z w u y
theorem Equation816_implies_Equation812 (G : Type*) [Magma G] (h : Equation816 G) : Equation812 G := λ x y z w u => h x y z w u y
theorem Equation1019_implies_Equation1015 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1015 G := λ x y z w u => h x y z w u y
theorem Equation1222_implies_Equation1218 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1218 G := λ x y z w u => h x y z w u y
theorem Equation1425_implies_Equation1421 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1421 G := λ x y z w u => h x y z w u y
theorem Equation1628_implies_Equation1624 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1624 G := λ x y z w u => h x y z w u y
theorem Equation1831_implies_Equation1827 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1827 G := λ x y z w u => h x y z w u y
theorem Equation2034_implies_Equation2030 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2030 G := λ x y z w u => h x y z w u y
theorem Equation2237_implies_Equation2233 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2233 G := λ x y z w u => h x y z w u y
theorem Equation2440_implies_Equation2436 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2436 G := λ x y z w u => h x y z w u y
theorem Equation2643_implies_Equation2639 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2639 G := λ x y z w u => h x y z w u y
theorem Equation2846_implies_Equation2842 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2842 G := λ x y z w u => h x y z w u y
theorem Equation3049_implies_Equation3045 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3045 G := λ x y z w u => h x y z w u y
theorem Equation3252_implies_Equation3248 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3248 G := λ x y z w u => h x y z w u y
theorem Equation3455_implies_Equation3451 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3451 G := λ x y z w u => h x y z w u y
theorem Equation3658_implies_Equation3654 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3654 G := λ x y z w u => h x y z w u y
theorem Equation3861_implies_Equation3857 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3857 G := λ x y z w u => h x y z w u y
theorem Equation4064_implies_Equation4060 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4060 G := λ x y z w u => h x y z w u y
theorem Equation4267_implies_Equation4263 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4263 G := λ x y z w u => h x y z w u y
theorem Equation4582_implies_Equation4578 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4578 G := λ x y z w u => h x y z w u y