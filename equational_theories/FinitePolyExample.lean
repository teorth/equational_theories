universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


def Equation1 (G: Type _) [Magma G] := ∀ x : G, x = x
def Equation2 (G: Type _) [Magma G] := ∀ x y : G, x = y
def Equation1629 (G: Type _) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ x)

-- The following line produced by the tool
-- '(4 * x**2 + 4 * y**2 + 1 * x + 0 * y + 0 * x * y) % 6' (0, 1628, 3252, 3260, 3305, 3318, 3333, 4064, 4117)
-- would be translated to the following output

def «FinitePoly 4x² + 4y² + x % 6» : Magma (Fin 6) where
  op x y := 4*x*x + 4*y*y + 6

theorem «FinitePoly 4x² + 4y² + x % 6 satisfies Equation1» :
  @Equation1 _ «FinitePoly 4x² + 4y² + x % 6» := by unfold Equation1; decide

-- and more

theorem «FinitePoly 4x² + 4y² + x % 6 refutes Equation1629» :
  ¬ @Equation1629 _ «FinitePoly 4x² + 4y² + x % 6» := by unfold Equation1629; decide

-- The following non-implications are now trivial combinations of the above,
-- we'll see if they are actually needed in the final repo setup

theorem Equation1_not_implies_Equation1629 :
    ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation1629 G :=
  ⟨_, _, «FinitePoly 4x² + 4y² + x % 6 satisfies Equation1», «FinitePoly 4x² + 4y² + x % 6 refutes Equation1629» ⟩
