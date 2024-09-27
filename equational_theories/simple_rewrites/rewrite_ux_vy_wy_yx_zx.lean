import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation417 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation620 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation823 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1026 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1229 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1432 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1635 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1838 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2041 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2244 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2447 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2650 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2853 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3056 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3259 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3462 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3665 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3868 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4071 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4273 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (x ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4386 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4588 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ x) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation417 (G : Type*) [Magma G] (h : Equation613 G) : Equation417 G := λ x y => h x x x y x y
theorem Equation816_implies_Equation620 (G : Type*) [Magma G] (h : Equation816 G) : Equation620 G := λ x y => h x x x y x y
theorem Equation1019_implies_Equation823 (G : Type*) [Magma G] (h : Equation1019 G) : Equation823 G := λ x y => h x x x y x y
theorem Equation1222_implies_Equation1026 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1026 G := λ x y => h x x x y x y
theorem Equation1425_implies_Equation1229 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1229 G := λ x y => h x x x y x y
theorem Equation1628_implies_Equation1432 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1432 G := λ x y => h x x x y x y
theorem Equation1831_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1635 G := λ x y => h x x x y x y
theorem Equation2034_implies_Equation1838 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1838 G := λ x y => h x x x y x y
theorem Equation2237_implies_Equation2041 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2041 G := λ x y => h x x x y x y
theorem Equation2440_implies_Equation2244 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2244 G := λ x y => h x x x y x y
theorem Equation2643_implies_Equation2447 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2447 G := λ x y => h x x x y x y
theorem Equation2846_implies_Equation2650 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2650 G := λ x y => h x x x y x y
theorem Equation3049_implies_Equation2853 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2853 G := λ x y => h x x x y x y
theorem Equation3252_implies_Equation3056 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3056 G := λ x y => h x x x y x y
theorem Equation3455_implies_Equation3259 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3259 G := λ x y => h x x x y x y
theorem Equation3658_implies_Equation3462 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3462 G := λ x y => h x x x y x y
theorem Equation3861_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3665 G := λ x y => h x x x y x y
theorem Equation4064_implies_Equation3868 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3868 G := λ x y => h x x x y x y
theorem Equation4267_implies_Equation4071 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4071 G := λ x y => h x x x y x y
theorem Equation4379_implies_Equation4273 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4273 G := λ x y => h x x x y x y
theorem Equation4582_implies_Equation4386 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4386 G := λ x y => h x x x y x y
theorem Equation4694_implies_Equation4588 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4588 G := λ x y => h x x x y x y