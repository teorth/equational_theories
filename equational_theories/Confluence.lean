import equational_theories.FreeMagma
import equational_theories.AllEquations
import equational_theories.FactsSyntax

def FreeMagma.length {α : Type} : FreeMagma α → Nat
  | .Leaf _ => 1
  | .Fork m1 m2 => FreeMagma.length m1 + FreeMagma.length m2

theorem FreeMagma.length_pos {α : Type} : (x : FreeMagma α) → 0 < FreeMagma.length x
  | .Leaf _ => by simp [FreeMagma.length]
  | .Fork m1 m2 => by
    have h1 := FreeMagma.length_pos m1
    have h2 := FreeMagma.length_pos m2
    simp [FreeMagma.length]
    omega

@[simp]
theorem FreeMagma.length_0 {α : Type} (x : FreeMagma α) : ¬ (FreeMagma.length x = 0) :=
  Nat.not_eq_zero_of_lt x.length_pos

-- equation 477 := x = y ◇ (x ◇ (y ◇ (y ◇ y)))

def simp477 {α : Type} [DecidableEq α] : FreeMagma α → FreeMagma α
  | .Leaf x => .Leaf x
  | .Fork m1 m2 =>
    let y1 := simp477 m1
    let m2' := simp477 m2
    match m2' with
    | .Fork x (.Fork y2 (.Fork y3 y4)) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        .Fork y1 m2'
    | _ =>
        .Fork y1 m2'

attribute [simp] simp477.eq_1

inductive IsNF {α : Type} [DecidableEq α] : FreeMagma α → Prop
  | leaf (x : α) : IsNF (.Leaf x)
  | fork (m1 m2 : FreeMagma α) : IsNF m1 → IsNF m2 → simp477 (.Fork m1 m2) = (.Fork m1 m2) → IsNF (.Fork m1 m2)

theorem idem_of_IsNF {α : Type} [DecidableEq α] {x : FreeMagma α} : IsNF x → simp477 x = x
  | .leaf x => rfl
  | .fork _ _ _ _ h => h

theorem simp477_NF {α : Type} [DecidableEq α] (x : FreeMagma α) : IsNF (simp477 x) := by
  unfold simp477
  split
  · constructor
  · rename_i x m1 m2
    simp (config := {zetaDelta := true})
    split
    · rename_i m2' x y2 y3 y4 heq
      split
      · have := simp477_NF m2
        rw [heq] at this
        cases this
        assumption
      · constructor
        · apply simp477_NF
        · apply simp477_NF
        · simp [simp477]
          rw [idem_of_IsNF (simp477_NF m2)]
          rw [idem_of_IsNF (simp477_NF m1)]
          simp [*]
    · constructor
      · apply simp477_NF
      · apply simp477_NF
      · simp [simp477]
        rw [idem_of_IsNF (simp477_NF m2)]
        rw [idem_of_IsNF (simp477_NF m1)]
        simp [*]

theorem simp477_idempotent {α : Type} [DecidableEq α] (x : FreeMagma α) :
    simp477 (simp477 x) = simp477 x := idem_of_IsNF (simp477_NF x)

-- def Magma477 (α) [DecidableEq α] := Quot (λ x y => @simp477 α _ x = simp477 y)

def Magma477 (α) [DecidableEq α] := {x : FreeMagma α // simp477 x = x }

instance (α) [DecidableEq α] : Coe α (Magma477 α) where
  coe x := ⟨x, by rfl⟩

instance instMagmaMagma477 {α} [DecidableEq α] : Magma (Magma477 α) where
  op := fun x y => ⟨simp477 (x.1 ◇ y.1), simp477_idempotent _⟩

instance {α} [DecidableEq α] : DecidableEq (Magma477 α) :=
  inferInstanceAs (DecidableEq {x : FreeMagma α // simp477 x = x })

theorem simp477_yy {α} [DecidableEq α] (y : FreeMagma α) :
    simp477 (y ⋆ y) = simp477 y ⋆ simp477 y := by
  simp [simp477]
  split
  · split
    · exfalso
      rename_i m2' x y2 y3 y4 heq hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos (simp477 y)
      omega
    · rfl
  · rfl

theorem simp477_yyy {α} [DecidableEq α] (y : FreeMagma α) :
    simp477 (y ⋆ (y ⋆ y)) = simp477 y ⋆ simp477 (y ⋆ y) := by
  simp [simp477_yy]
  rw [simp477]
  split
  · split
    · exfalso
      rename_i m2' x y2 y3 y4 heq hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      simp [simp477_yy] at heq
      obtain ⟨rfl, heq⟩ := heq
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [simp477_yy]
  · simp [simp477_yy]

theorem simp477_xyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    simp477 (x ⋆ (y ⋆ (y ⋆ y))) = simp477 x ⋆ simp477 (y ⋆ (y ⋆ y)) := by
  simp [simp477_yyy]
  rw [simp477]
  split
  · split
    · exfalso
      rename_i m2' x y2 y3 y4 heq hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      simp [simp477_yyy, simp477_yy] at heq
      obtain ⟨rfl, hxy, heq⟩ := heq
      rw [hxy] at heq
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [simp477_yyy]
  · simp [simp477_yyy]

@[equational_result]
theorem Equation477_Facts :
  ∃ (G : Type) (_ : Magma G), Facts G [477] [1426, 1519, 2035, 2128, 3050, 3150] := by
  use Magma477 Nat, instMagmaMagma477
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op]
    apply Subtype.ext
    simp only
    simp [hx, hy, simp477_yy, simp477_idempotent, simp477_yyy, simp477_xyyy]
    unfold simp477
    simp [hx, hy, simp477_yy, simp477_idempotent, simp477_yyy, simp477_xyyy]
  · intro h
    replace h := h (0 : Nat)
    revert h
    decide
  · intro h
    replace h := h (0 : Nat) (1 : Nat)
    revert h
    decide
  · intro h
    replace h := h (0 : Nat)
    revert h
    decide
  · intro h
    replace h := h (0 : Nat) (1 : Nat)
    revert h
    decide
  · intro h
    replace h := h (0 : Nat)
    revert h
    decide
  · intro h
    replace h := h (0 : Nat) (1 : Nat)
    revert h
    decide
