import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation411 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation614 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ ((x ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation817 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ x) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1020 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1223 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (((x ∘ x) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1426 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ (x ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1629 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1832 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2035 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2238 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2441 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2644 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2847 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3050 (G: Type*) [Magma G] := ∀ x : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3253 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = x ∘ (x ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3456 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = x ∘ ((x ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3659 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = (x ∘ x) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3862 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = (x ∘ (x ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4065 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = ((x ∘ x) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4380 (G: Type*) [Magma G] := ∀ x : G, x ∘ (x ∘ x) = (x ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation411 (G : Type*) [Magma G] (h : Equation613 G) : Equation411 G := λ x => h x x x x x x
theorem Equation816_implies_Equation614 (G : Type*) [Magma G] (h : Equation816 G) : Equation614 G := λ x => h x x x x x x
theorem Equation1019_implies_Equation817 (G : Type*) [Magma G] (h : Equation1019 G) : Equation817 G := λ x => h x x x x x x
theorem Equation1222_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1020 G := λ x => h x x x x x x
theorem Equation1425_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1223 G := λ x => h x x x x x x
theorem Equation1628_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1426 G := λ x => h x x x x x x
theorem Equation1831_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1629 G := λ x => h x x x x x x
theorem Equation2034_implies_Equation1832 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1832 G := λ x => h x x x x x x
theorem Equation2237_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2035 G := λ x => h x x x x x x
theorem Equation2440_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2238 G := λ x => h x x x x x x
theorem Equation2643_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2441 G := λ x => h x x x x x x
theorem Equation2846_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2644 G := λ x => h x x x x x x
theorem Equation3049_implies_Equation2847 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2847 G := λ x => h x x x x x x
theorem Equation3252_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3050 G := λ x => h x x x x x x
theorem Equation3455_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3253 G := λ x => h x x x x x x
theorem Equation3658_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3456 G := λ x => h x x x x x x
theorem Equation3861_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3659 G := λ x => h x x x x x x
theorem Equation4064_implies_Equation3862 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3862 G := λ x => h x x x x x x
theorem Equation4267_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4065 G := λ x => h x x x x x x
theorem Equation4582_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4380 G := λ x => h x x x x x x