import equational_theories.Equations.Basic

class WeakCentralGroupoid (G : Type*) extends Magma G where
  /-- equation 1485 -/
  eqn (x y z : G) : (y ◇ x) ◇ (x ◇ (z ◇ y)) = x

class WeakCentralDigraph (G : Type*) where
  Path : G → G → Prop
  IsGood : G → G → G → Prop
  isGood_path {x y z : G} : IsGood x y z → Path x y ∧ Path y z
  isGood_unique (x y : G) : Unique {z : G // IsGood x z y}
  isGood_left {x y : G} : Path x y → ∃ z, IsGood z x y
  isGood_right {x y : G} : Path x y → ∃ z, IsGood x y z
  isGood_five {a b c d e : G} : IsGood a b c → IsGood c d e → Path e a → IsGood b c d

namespace WeakCentralGroupoid

variable {G : Type*} [WeakCentralGroupoid G]

  /-- equation 2162 -/
theorem dual_eqn (x y z : G) : ((y ◇ z) ◇ x) ◇ (x ◇ y) = x := by
  conv in _ ◇ y => rw [← eqn y, eqn z z z]
  apply eqn

def Path (x y : G) : Prop := ∃ z, x = z ◇ y

theorem Path.def' {x y : G} : Path x y ↔ ∃ z, x ◇ z = y := by
  constructor <;> rintro ⟨z, rfl⟩
  · exact ⟨_, by rw [← eqn z z z, dual_eqn]⟩
  · exact ⟨_, by rw [← eqn z z z, eqn]⟩

def IsGood (x y z : G) : Prop := y = x ◇ z

theorem isGood_five {a b c d e : G} : IsGood a b c → IsGood c d e → Path e a → IsGood b c d := by
  rintro rfl rfl ⟨_, rfl⟩; exact (eqn ..).symm

variable (G) in
def toDigraph : WeakCentralDigraph G where
  Path := Path
  IsGood := IsGood
  isGood_path := fun h => ⟨Path.def'.2 ⟨_, h.symm⟩, ⟨_, h⟩⟩
  isGood_unique x y :=
    ⟨⟨⟨x ◇ y, rfl⟩⟩, fun ⟨z, (h : _ = _)⟩ => by simp [h]⟩
  isGood_left h := h
  isGood_right h := (Path.def'.1 h).imp fun z h => h.symm
  isGood_five := isGood_five

end WeakCentralGroupoid

def WeakCentralDigraph.toGroupoid
    (G : Type*) [WeakCentralDigraph G] : WeakCentralGroupoid G := by
  let inst : Magma G := { op := fun x y => (isGood_unique x y).1.1 }
  refine { inst with eqn := fun c a u => ?_ }
  have isGood_def {x y z : G} : IsGood x y z ↔ y = x ◇ z := by
    constructor <;> intro H
    · exact Subtype.val_inj.2 <| (isGood_unique x z).2 ⟨_, H⟩
    · subst y; exact (isGood_unique x z).1.1.2
  rw [Eq.comm, ← isGood_def]
  exact isGood_five (isGood_def.2 rfl) (isGood_def.2 rfl) ((isGood_path (isGood_def.2 rfl)).2)
