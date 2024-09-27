import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation432 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation635 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation838 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1041 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1244 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1447 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1650 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1853 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2056 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2259 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2462 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2665 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2868 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3071 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3274 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3477 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3680 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3883 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4086 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4286 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4401 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4601 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation432 (G : Type*) [Magma G] (h : Equation613 G) : Equation432 G := λ x y z => h x x y x z x
theorem Equation816_implies_Equation635 (G : Type*) [Magma G] (h : Equation816 G) : Equation635 G := λ x y z => h x x y x z x
theorem Equation1019_implies_Equation838 (G : Type*) [Magma G] (h : Equation1019 G) : Equation838 G := λ x y z => h x x y x z x
theorem Equation1222_implies_Equation1041 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1041 G := λ x y z => h x x y x z x
theorem Equation1425_implies_Equation1244 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1244 G := λ x y z => h x x y x z x
theorem Equation1628_implies_Equation1447 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1447 G := λ x y z => h x x y x z x
theorem Equation1831_implies_Equation1650 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1650 G := λ x y z => h x x y x z x
theorem Equation2034_implies_Equation1853 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1853 G := λ x y z => h x x y x z x
theorem Equation2237_implies_Equation2056 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2056 G := λ x y z => h x x y x z x
theorem Equation2440_implies_Equation2259 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2259 G := λ x y z => h x x y x z x
theorem Equation2643_implies_Equation2462 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2462 G := λ x y z => h x x y x z x
theorem Equation2846_implies_Equation2665 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2665 G := λ x y z => h x x y x z x
theorem Equation3049_implies_Equation2868 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2868 G := λ x y z => h x x y x z x
theorem Equation3252_implies_Equation3071 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3071 G := λ x y z => h x x y x z x
theorem Equation3455_implies_Equation3274 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3274 G := λ x y z => h x x y x z x
theorem Equation3658_implies_Equation3477 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3477 G := λ x y z => h x x y x z x
theorem Equation3861_implies_Equation3680 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3680 G := λ x y z => h x x y x z x
theorem Equation4064_implies_Equation3883 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3883 G := λ x y z => h x x y x z x
theorem Equation4267_implies_Equation4086 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4086 G := λ x y z => h x x y x z x
theorem Equation4379_implies_Equation4286 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4286 G := λ x y z => h x x y x z x
theorem Equation4582_implies_Equation4401 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4401 G := λ x y z => h x x y x z x
theorem Equation4694_implies_Equation4601 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4601 G := λ x y z => h x x y x z x