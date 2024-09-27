import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation456 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation659 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation862 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1065 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1268 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1471 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1674 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1877 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2080 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2283 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2486 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2689 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2892 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3095 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3298 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3501 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3704 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3907 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4110 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4425 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation456 (G : Type*) [Magma G] (h : Equation613 G) : Equation456 G := λ x y z => h x x y z z z
theorem Equation816_implies_Equation659 (G : Type*) [Magma G] (h : Equation816 G) : Equation659 G := λ x y z => h x x y z z z
theorem Equation1019_implies_Equation862 (G : Type*) [Magma G] (h : Equation1019 G) : Equation862 G := λ x y z => h x x y z z z
theorem Equation1222_implies_Equation1065 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1065 G := λ x y z => h x x y z z z
theorem Equation1425_implies_Equation1268 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1268 G := λ x y z => h x x y z z z
theorem Equation1628_implies_Equation1471 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1471 G := λ x y z => h x x y z z z
theorem Equation1831_implies_Equation1674 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1674 G := λ x y z => h x x y z z z
theorem Equation2034_implies_Equation1877 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1877 G := λ x y z => h x x y z z z
theorem Equation2237_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2080 G := λ x y z => h x x y z z z
theorem Equation2440_implies_Equation2283 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2283 G := λ x y z => h x x y z z z
theorem Equation2643_implies_Equation2486 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2486 G := λ x y z => h x x y z z z
theorem Equation2846_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2689 G := λ x y z => h x x y z z z
theorem Equation3049_implies_Equation2892 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2892 G := λ x y z => h x x y z z z
theorem Equation3252_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3095 G := λ x y z => h x x y z z z
theorem Equation3455_implies_Equation3298 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3298 G := λ x y z => h x x y z z z
theorem Equation3658_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3501 G := λ x y z => h x x y z z z
theorem Equation3861_implies_Equation3704 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3704 G := λ x y z => h x x y z z z
theorem Equation4064_implies_Equation3907 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3907 G := λ x y z => h x x y z z z
theorem Equation4267_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4110 G := λ x y z => h x x y z z z
theorem Equation4582_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4425 G := λ x y z => h x x y z z z