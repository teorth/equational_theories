import equational_theories.FreeMagma
import equational_theories.AllEquations
import equational_theories.FactsSyntax

namespace FreeMagma

variable {α : Type}
/-
inductive Everywhere (P : FreeMagma α → Prop) : FreeMagma α → Prop
  | leaf (x : α) : P (.Leaf x) → Everywhere P (.Leaf x)
  | fork (m1 m2 : FreeMagma α) : Everywhere P m1 → Everywhere P m2 → P (.Fork m1 m2) → Everywhere P (.Fork m1 m2)
-/
def Everywhere (P : FreeMagma α → Prop) : FreeMagma α → Prop
  | .Leaf x => P (.Leaf x)
  | .Fork x y => x.Everywhere P ∧ y.Everywhere P ∧ P (x ⋆ y)

theorem Everywhere.top {P : FreeMagma α → Prop} : {x : FreeMagma α} → Everywhere P x → P x
  | .Leaf _ => fun h => h
  | .Fork _ _ => fun h => h.2.2

@[simp]
theorem Everywhere_idem {P : FreeMagma α → Prop} : Everywhere (Everywhere P) = Everywhere P := by
  ext x
  constructor
  · intro h
    induction x with
    | Leaf => exact h
    | Fork x y ihx ihy => exact ⟨ihx h.1, ihy h.2.1,  h.2.2.2.2⟩
  · intro h
    induction x with
    | Leaf =>
      exact h
    | Fork x y ihx ihy => exact ⟨ihx h.1, ihy h.2.1, h⟩

/-
inductive SubtermOf (x : FreeMagma α) : FreeMagma α → Prop where
| here : SubtermOf x x
| left a b : SubtermOf x a → SubtermOf x (a ⋆ b)
| right a b : SubtermOf x b → SubtermOf x (a ⋆ b)
-/
def SubtermOf (x : FreeMagma α) : (y : FreeMagma α) → Prop
| .Leaf a => x = .Leaf a
| .Fork a b => x = .Fork a b ∨ SubtermOf x a ∨ SubtermOf x b

@[refl]
theorem SubtermOf.refl (x : FreeMagma α) : SubtermOf x x := by
  cases x with
  | Leaf => rfl
  | Fork x y => left; rfl

theorem everywhere_of_subterm_of_everywhere {P : FreeMagma α → Prop} {x} (h : x.Everywhere P) {y}
    (hsub : SubtermOf y x) : y.Everywhere P := by
  induction x with
  | Leaf =>
    cases hsub
    apply h.top
  | Fork x y ihx ihy =>
    obtain (rfl | hsub | hsub) := hsub
    · apply h
    · apply ihx h.1 hsub
    · apply ihy h.2.1 hsub

theorem subterm_everywhere {P : FreeMagma α → Prop} {x} (h : x.Everywhere P) {y} (hsub : SubtermOf y x) : P y := by
  apply (everywhere_of_subterm_of_everywhere h hsub).top

class IsProj (rw : FreeMagma α → FreeMagma α) : Prop where
  proj : ∀ x, SubtermOf (rw x) x

theorem everywhere_of_projection_of_everywhere
    (rw : FreeMagma α → FreeMagma α) [IsProj rw] P :
    ∀ x, Everywhere P x → (rw x).Everywhere P :=
  fun x he ↦ everywhere_of_subterm_of_everywhere he (IsProj.proj x)

theorem projection_everywhere
    (rw : FreeMagma α → FreeMagma α) [IsProj rw] P :
    ∀ x, Everywhere P x → P (rw x) :=
  fun x he ↦ subterm_everywhere he (IsProj.proj x)


end FreeMagma

namespace Confluence

open FreeMagma

variable {α : Type}

variable (rw : FreeMagma α → FreeMagma α)

def bu : FreeMagma α → FreeMagma α
  | .Leaf x => .Leaf x
  | .Fork x y => rw (bu x ⋆ bu y)

attribute [simp] bu.eq_1

def NF (x : FreeMagma α) : Prop := x.Everywhere (fun y => bu rw y = y)

def bu_nf [hproj : IsProj rw] : ∀ x, NF rw (bu rw x) := by
  intro x
  induction x with
  | Leaf =>
    simp [NF, bu, Everywhere]
  | Fork x y ihx ihy =>
    simp only [NF, bu]
    have hsub := hproj.proj (bu rw x ⋆ bu rw y)
    obtain (heq | hsub | hsub) := hsub
    · apply everywhere_of_projection_of_everywhere
      refine ⟨ihx, ihy, ?_⟩
      dsimp
      simp [bu, Everywhere, *, ihx.top, ihy.top]
    · exact everywhere_of_subterm_of_everywhere ihx hsub
    · exact everywhere_of_subterm_of_everywhere ihy hsub

theorem idem_of_NF {x : FreeMagma α} (h : NF rw x) : bu rw x = x := by
  apply h.top

variable [IsProj rw]

@[simp] theorem bu_idem x : bu rw (bu rw x) = bu rw x := idem_of_NF rw (bu_nf rw x)

def ConfMagma := {x : FreeMagma α // bu rw x = x }

instance : Coe α (ConfMagma rw) where
  coe x := ⟨x, by rfl⟩

instance instMagmaMagma477 : Magma (ConfMagma rw) where
  op := fun x y => ⟨bu rw (x.1 ◇ y.1), bu_idem rw _⟩

instance [DecidableEq α] : DecidableEq (ConfMagma rw) :=
  inferInstanceAs (DecidableEq {x : FreeMagma α // bu rw x = x })


section rw477

variable [DecidableEq α]

-- equation 477 := x = y ◇ (x ◇ (y ◇ (y ◇ y)))
def rw477 : FreeMagma α → FreeMagma α
  | m@(.Fork y1 (.Fork x (.Fork y2 (.Fork y3 y4)))) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rw477_projection : IsProj (@rw477 α _) where
  proj := by
    intro x
    unfold rw477
    split
    · split
      · right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rw477_yy (y : FreeMagma α) : rw477 (y ⋆ y) = y ⋆ y := by
  unfold rw477
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rw477_yyy {α} [DecidableEq α] (y : FreeMagma α) :
    rw477 (y ⋆ (y ⋆ y)) = y ⋆ (y ⋆ y) := by
  unfold rw477
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rw477_xyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rw477 (x ⋆ (y ⋆ (y ⋆ y))) = x ⋆ (y ⋆ (y ⋆ y)) := by
  unfold rw477
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rw477_yxyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rw477 (y ⋆ (x ⋆ (y ⋆ (y ⋆ y)))) = x := by
  simp [rw477]

@[equational_result]
theorem Equation477_Facts :
  ∃ (G : Type) (_ : Magma G), Facts G [477] [1426, 1519, 2035, 2128, 3050, 3150] := by
  use ConfMagma (@rw477 Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op]
    apply Subtype.ext
    simp only
    simp [bu, hx, hy]
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

end rw477



end Confluence
