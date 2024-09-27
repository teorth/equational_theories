import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation446 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation649 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation852 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1055 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1258 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1461 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1664 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1867 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2070 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2273 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2476 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2679 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2882 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3085 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3288 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3491 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3694 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3897 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4100 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4299 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4415 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4614 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation446 (G : Type*) [Magma G] (h : Equation613 G) : Equation446 G := λ x y z => h x x y z x x
theorem Equation816_implies_Equation649 (G : Type*) [Magma G] (h : Equation816 G) : Equation649 G := λ x y z => h x x y z x x
theorem Equation1019_implies_Equation852 (G : Type*) [Magma G] (h : Equation1019 G) : Equation852 G := λ x y z => h x x y z x x
theorem Equation1222_implies_Equation1055 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1055 G := λ x y z => h x x y z x x
theorem Equation1425_implies_Equation1258 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1258 G := λ x y z => h x x y z x x
theorem Equation1628_implies_Equation1461 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1461 G := λ x y z => h x x y z x x
theorem Equation1831_implies_Equation1664 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1664 G := λ x y z => h x x y z x x
theorem Equation2034_implies_Equation1867 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1867 G := λ x y z => h x x y z x x
theorem Equation2237_implies_Equation2070 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2070 G := λ x y z => h x x y z x x
theorem Equation2440_implies_Equation2273 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2273 G := λ x y z => h x x y z x x
theorem Equation2643_implies_Equation2476 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2476 G := λ x y z => h x x y z x x
theorem Equation2846_implies_Equation2679 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2679 G := λ x y z => h x x y z x x
theorem Equation3049_implies_Equation2882 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2882 G := λ x y z => h x x y z x x
theorem Equation3252_implies_Equation3085 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3085 G := λ x y z => h x x y z x x
theorem Equation3455_implies_Equation3288 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3288 G := λ x y z => h x x y z x x
theorem Equation3658_implies_Equation3491 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3491 G := λ x y z => h x x y z x x
theorem Equation3861_implies_Equation3694 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3694 G := λ x y z => h x x y z x x
theorem Equation4064_implies_Equation3897 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3897 G := λ x y z => h x x y z x x
theorem Equation4267_implies_Equation4100 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4100 G := λ x y z => h x x y z x x
theorem Equation4379_implies_Equation4299 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4299 G := λ x y z => h x x y z x x
theorem Equation4582_implies_Equation4415 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4415 G := λ x y z => h x x y z x x
theorem Equation4694_implies_Equation4614 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4614 G := λ x y z => h x x y z x x