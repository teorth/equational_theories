import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation430 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation633 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation836 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1039 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1242 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1445 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1648 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1851 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2054 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2257 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2460 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2663 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2866 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3069 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3272 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3475 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3678 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3881 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4084 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4284 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4399 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4599 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation430 (G : Type*) [Magma G] (h : Equation613 G) : Equation430 G := λ x y => h x x y x y y
theorem Equation816_implies_Equation633 (G : Type*) [Magma G] (h : Equation816 G) : Equation633 G := λ x y => h x x y x y y
theorem Equation1019_implies_Equation836 (G : Type*) [Magma G] (h : Equation1019 G) : Equation836 G := λ x y => h x x y x y y
theorem Equation1222_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1039 G := λ x y => h x x y x y y
theorem Equation1425_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1242 G := λ x y => h x x y x y y
theorem Equation1628_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1445 G := λ x y => h x x y x y y
theorem Equation1831_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1648 G := λ x y => h x x y x y y
theorem Equation2034_implies_Equation1851 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1851 G := λ x y => h x x y x y y
theorem Equation2237_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2054 G := λ x y => h x x y x y y
theorem Equation2440_implies_Equation2257 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2257 G := λ x y => h x x y x y y
theorem Equation2643_implies_Equation2460 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2460 G := λ x y => h x x y x y y
theorem Equation2846_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2663 G := λ x y => h x x y x y y
theorem Equation3049_implies_Equation2866 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2866 G := λ x y => h x x y x y y
theorem Equation3252_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3069 G := λ x y => h x x y x y y
theorem Equation3455_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3272 G := λ x y => h x x y x y y
theorem Equation3658_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3475 G := λ x y => h x x y x y y
theorem Equation3861_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3678 G := λ x y => h x x y x y y
theorem Equation4064_implies_Equation3881 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3881 G := λ x y => h x x y x y y
theorem Equation4267_implies_Equation4084 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4084 G := λ x y => h x x y x y y
theorem Equation4379_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4284 G := λ x y => h x x y x y y
theorem Equation4582_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4399 G := λ x y => h x x y x y y
theorem Equation4694_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4599 G := λ x y => h x x y x y y