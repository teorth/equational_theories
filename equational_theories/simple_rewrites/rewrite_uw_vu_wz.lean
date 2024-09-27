import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation587 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (z ∘ (w ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation790 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((z ∘ w) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation993 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ z) ∘ (w ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1196 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1399 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ z) ∘ w) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (z ∘ (w ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3429 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (z ∘ (w ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3632 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((z ∘ w) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3835 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ z) ∘ (w ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4038 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (z ∘ w)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4241 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ z) ∘ w) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4373 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = z ∘ (w ∘ u)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4556 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (z ∘ w) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4688 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (z ∘ w) ∘ u
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation587 (G : Type*) [Magma G] (h : Equation613 G) : Equation587 G := λ x y z w u => h x y z z w u
theorem Equation816_implies_Equation790 (G : Type*) [Magma G] (h : Equation816 G) : Equation790 G := λ x y z w u => h x y z z w u
theorem Equation1019_implies_Equation993 (G : Type*) [Magma G] (h : Equation1019 G) : Equation993 G := λ x y z w u => h x y z z w u
theorem Equation1222_implies_Equation1196 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1196 G := λ x y z w u => h x y z z w u
theorem Equation1425_implies_Equation1399 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1399 G := λ x y z w u => h x y z z w u
theorem Equation1628_implies_Equation1602 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1602 G := λ x y z w u => h x y z z w u
theorem Equation1831_implies_Equation1805 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1805 G := λ x y z w u => h x y z z w u
theorem Equation2034_implies_Equation2008 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2008 G := λ x y z w u => h x y z z w u
theorem Equation2237_implies_Equation2211 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2211 G := λ x y z w u => h x y z z w u
theorem Equation2440_implies_Equation2414 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2414 G := λ x y z w u => h x y z z w u
theorem Equation2643_implies_Equation2617 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2617 G := λ x y z w u => h x y z z w u
theorem Equation2846_implies_Equation2820 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2820 G := λ x y z w u => h x y z z w u
theorem Equation3049_implies_Equation3023 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3023 G := λ x y z w u => h x y z z w u
theorem Equation3252_implies_Equation3226 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3226 G := λ x y z w u => h x y z z w u
theorem Equation3455_implies_Equation3429 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3429 G := λ x y z w u => h x y z z w u
theorem Equation3658_implies_Equation3632 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3632 G := λ x y z w u => h x y z z w u
theorem Equation3861_implies_Equation3835 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3835 G := λ x y z w u => h x y z z w u
theorem Equation4064_implies_Equation4038 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4038 G := λ x y z w u => h x y z z w u
theorem Equation4267_implies_Equation4241 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4241 G := λ x y z w u => h x y z z w u
theorem Equation4379_implies_Equation4373 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4373 G := λ x y z w u => h x y z z w u
theorem Equation4582_implies_Equation4556 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4556 G := λ x y z w u => h x y z z w u
theorem Equation4694_implies_Equation4688 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4688 G := λ x y z w u => h x y z z w u