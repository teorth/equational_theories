import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation529 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation732 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation935 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1138 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1341 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1544 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1747 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1950 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2153 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2356 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2559 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2762 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2965 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3168 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3371 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3574 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3777 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3980 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4183 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4498 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation529 (G : Type*) [Magma G] (h : Equation613 G) : Equation529 G := λ x y z => h x y y z z y
theorem Equation816_implies_Equation732 (G : Type*) [Magma G] (h : Equation816 G) : Equation732 G := λ x y z => h x y y z z y
theorem Equation1019_implies_Equation935 (G : Type*) [Magma G] (h : Equation1019 G) : Equation935 G := λ x y z => h x y y z z y
theorem Equation1222_implies_Equation1138 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1138 G := λ x y z => h x y y z z y
theorem Equation1425_implies_Equation1341 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1341 G := λ x y z => h x y y z z y
theorem Equation1628_implies_Equation1544 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1544 G := λ x y z => h x y y z z y
theorem Equation1831_implies_Equation1747 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1747 G := λ x y z => h x y y z z y
theorem Equation2034_implies_Equation1950 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1950 G := λ x y z => h x y y z z y
theorem Equation2237_implies_Equation2153 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2153 G := λ x y z => h x y y z z y
theorem Equation2440_implies_Equation2356 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2356 G := λ x y z => h x y y z z y
theorem Equation2643_implies_Equation2559 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2559 G := λ x y z => h x y y z z y
theorem Equation2846_implies_Equation2762 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2762 G := λ x y z => h x y y z z y
theorem Equation3049_implies_Equation2965 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2965 G := λ x y z => h x y y z z y
theorem Equation3252_implies_Equation3168 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3168 G := λ x y z => h x y y z z y
theorem Equation3455_implies_Equation3371 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3371 G := λ x y z => h x y y z z y
theorem Equation3658_implies_Equation3574 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3574 G := λ x y z => h x y y z z y
theorem Equation3861_implies_Equation3777 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3777 G := λ x y z => h x y y z z y
theorem Equation4064_implies_Equation3980 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3980 G := λ x y z => h x y y z z y
theorem Equation4267_implies_Equation4183 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4183 G := λ x y z => h x y y z z y
theorem Equation4582_implies_Equation4498 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4498 G := λ x y z => h x y y z z y