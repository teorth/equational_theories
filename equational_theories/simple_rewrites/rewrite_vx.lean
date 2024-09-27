import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation608 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation811 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1014 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1217 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1420 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1623 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1826 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2029 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2232 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2435 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2638 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2841 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3044 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3247 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3450 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3653 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3856 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4059 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4262 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4577 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation608 (G : Type*) [Magma G] (h : Equation613 G) : Equation608 G := λ x y z w u => h x y z w u x
theorem Equation816_implies_Equation811 (G : Type*) [Magma G] (h : Equation816 G) : Equation811 G := λ x y z w u => h x y z w u x
theorem Equation1019_implies_Equation1014 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1014 G := λ x y z w u => h x y z w u x
theorem Equation1222_implies_Equation1217 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1217 G := λ x y z w u => h x y z w u x
theorem Equation1425_implies_Equation1420 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1420 G := λ x y z w u => h x y z w u x
theorem Equation1628_implies_Equation1623 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1623 G := λ x y z w u => h x y z w u x
theorem Equation1831_implies_Equation1826 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1826 G := λ x y z w u => h x y z w u x
theorem Equation2034_implies_Equation2029 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2029 G := λ x y z w u => h x y z w u x
theorem Equation2237_implies_Equation2232 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2232 G := λ x y z w u => h x y z w u x
theorem Equation2440_implies_Equation2435 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2435 G := λ x y z w u => h x y z w u x
theorem Equation2643_implies_Equation2638 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2638 G := λ x y z w u => h x y z w u x
theorem Equation2846_implies_Equation2841 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2841 G := λ x y z w u => h x y z w u x
theorem Equation3049_implies_Equation3044 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3044 G := λ x y z w u => h x y z w u x
theorem Equation3252_implies_Equation3247 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3247 G := λ x y z w u => h x y z w u x
theorem Equation3455_implies_Equation3450 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3450 G := λ x y z w u => h x y z w u x
theorem Equation3658_implies_Equation3653 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3653 G := λ x y z w u => h x y z w u x
theorem Equation3861_implies_Equation3856 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3856 G := λ x y z w u => h x y z w u x
theorem Equation4064_implies_Equation4059 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4059 G := λ x y z w u => h x y z w u x
theorem Equation4267_implies_Equation4262 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4262 G := λ x y z w u => h x y z w u x
theorem Equation4582_implies_Equation4577 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4577 G := λ x y z w u => h x y z w u x