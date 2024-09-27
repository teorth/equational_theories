import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation537 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation740 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation943 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1146 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1349 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1552 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1755 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1958 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2161 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2364 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2567 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2770 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2973 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3176 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3379 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3582 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3785 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3988 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4191 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4506 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation537 (G : Type*) [Magma G] (h : Equation613 G) : Equation537 G := λ x y z => h x y z x x x
theorem Equation816_implies_Equation740 (G : Type*) [Magma G] (h : Equation816 G) : Equation740 G := λ x y z => h x y z x x x
theorem Equation1019_implies_Equation943 (G : Type*) [Magma G] (h : Equation1019 G) : Equation943 G := λ x y z => h x y z x x x
theorem Equation1222_implies_Equation1146 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1146 G := λ x y z => h x y z x x x
theorem Equation1425_implies_Equation1349 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1349 G := λ x y z => h x y z x x x
theorem Equation1628_implies_Equation1552 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1552 G := λ x y z => h x y z x x x
theorem Equation1831_implies_Equation1755 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1755 G := λ x y z => h x y z x x x
theorem Equation2034_implies_Equation1958 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1958 G := λ x y z => h x y z x x x
theorem Equation2237_implies_Equation2161 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2161 G := λ x y z => h x y z x x x
theorem Equation2440_implies_Equation2364 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2364 G := λ x y z => h x y z x x x
theorem Equation2643_implies_Equation2567 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2567 G := λ x y z => h x y z x x x
theorem Equation2846_implies_Equation2770 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2770 G := λ x y z => h x y z x x x
theorem Equation3049_implies_Equation2973 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2973 G := λ x y z => h x y z x x x
theorem Equation3252_implies_Equation3176 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3176 G := λ x y z => h x y z x x x
theorem Equation3455_implies_Equation3379 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3379 G := λ x y z => h x y z x x x
theorem Equation3658_implies_Equation3582 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3582 G := λ x y z => h x y z x x x
theorem Equation3861_implies_Equation3785 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3785 G := λ x y z => h x y z x x x
theorem Equation4064_implies_Equation3988 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3988 G := λ x y z => h x y z x x x
theorem Equation4267_implies_Equation4191 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4191 G := λ x y z => h x y z x x x
theorem Equation4582_implies_Equation4506 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4506 G := λ x y z => h x y z x x x