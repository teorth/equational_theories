import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation442 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation645 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation848 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1051 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1254 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1457 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1660 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1863 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2066 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2269 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2472 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2675 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2878 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3081 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3284 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3487 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3690 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3893 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4096 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4295 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4411 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4610 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation442 (G : Type*) [Magma G] (h : Equation613 G) : Equation442 G := λ x y z => h x x y y z x
theorem Equation816_implies_Equation645 (G : Type*) [Magma G] (h : Equation816 G) : Equation645 G := λ x y z => h x x y y z x
theorem Equation1019_implies_Equation848 (G : Type*) [Magma G] (h : Equation1019 G) : Equation848 G := λ x y z => h x x y y z x
theorem Equation1222_implies_Equation1051 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1051 G := λ x y z => h x x y y z x
theorem Equation1425_implies_Equation1254 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1254 G := λ x y z => h x x y y z x
theorem Equation1628_implies_Equation1457 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1457 G := λ x y z => h x x y y z x
theorem Equation1831_implies_Equation1660 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1660 G := λ x y z => h x x y y z x
theorem Equation2034_implies_Equation1863 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1863 G := λ x y z => h x x y y z x
theorem Equation2237_implies_Equation2066 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2066 G := λ x y z => h x x y y z x
theorem Equation2440_implies_Equation2269 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2269 G := λ x y z => h x x y y z x
theorem Equation2643_implies_Equation2472 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2472 G := λ x y z => h x x y y z x
theorem Equation2846_implies_Equation2675 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2675 G := λ x y z => h x x y y z x
theorem Equation3049_implies_Equation2878 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2878 G := λ x y z => h x x y y z x
theorem Equation3252_implies_Equation3081 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3081 G := λ x y z => h x x y y z x
theorem Equation3455_implies_Equation3284 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3284 G := λ x y z => h x x y y z x
theorem Equation3658_implies_Equation3487 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3487 G := λ x y z => h x x y y z x
theorem Equation3861_implies_Equation3690 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3690 G := λ x y z => h x x y y z x
theorem Equation4064_implies_Equation3893 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3893 G := λ x y z => h x x y y z x
theorem Equation4267_implies_Equation4096 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4096 G := λ x y z => h x x y y z x
theorem Equation4379_implies_Equation4295 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4295 G := λ x y z => h x x y y z x
theorem Equation4582_implies_Equation4411 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4411 G := λ x y z => h x x y y z x
theorem Equation4694_implies_Equation4610 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4610 G := λ x y z => h x x y y z x