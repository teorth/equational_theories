/-
  This file defines the dual word and proves Lemma 3.5, that is
  (w ≃ w' ⇒ w'' ≃ w''') implies (w.op ≃ w'.op ⇒ w''.op ≃ w'''.op)
-/

import equational_theories.FreeMagma
import equational_theories.MagmaLaw
import equational_theories.Preorder

open FreeMagma
open Law

def FreeMagma.op {α} (w : FreeMagma α) : FreeMagma α :=
match w with
| .Leaf x => .Leaf x
| .Fork w₁ w₂ => .Fork w₂.op w₁.op

/--
The dual is indeed dual (an involution).
-/
@[simp]
theorem FreeMagma.op_op {α} (w : FreeMagma α) : w.op.op = w := by
 induction w <;> simp [op, *]

@[simp]
def Op (G : Type) : Type := G

@[simp]
instance opMagma {G : Type} [Magma G] : Magma (Op G) := { op := λ (x y : G) ↦ (y ◇ x : G) }

def Magma.opHom {G} [Magma G] : G → Op G := fun x => x

theorem evalInMagmaOp {α G} [Magma G] (φ : α → G) (w : FreeMagma α):
  evalInMagma (G := Op G) φ w.op = evalInMagma (G := G) φ w :=
by
  cases w; trivial
  case Fork w₁ w₂ =>
    simp [evalInMagma]
    repeat rw [evalInMagmaOp]

theorem models.Op {α} {G : Type} [Magma G] {w₁ w₂ : FreeMagma α} (h : G ⊧ w₁ ≃ w₂) :
  (Op G) ⊧ w₁.op ≃ w₂.op :=
by
  intros φ
  simp [satisfies, satisfiesPhi]
  repeat rw [@evalInMagmaOp]
  apply h

namespace Law.MagmaLaw

def op {α} (l : MagmaLaw α) : MagmaLaw α := { lhs := l.lhs.op, rhs := l.rhs.op}

theorem law_op_op {α} (l : MagmaLaw α) : l.op.op = l := by simp [op]

theorem satisfiesPhi_op {α G} [Magma G] {l : MagmaLaw α} {φ : α → G}
  (h : satisfiesPhi (Magma.opHom ∘ φ) l) : satisfiesPhi φ l.op := by
  simp [satisfiesPhi, evalInMagma, op] at *
  rw [← evalInMagmaOp φ l.lhs.op, ← evalInMagmaOp φ l.rhs.op]
  simp
  exact h

theorem satisfies_op_op {α G} [Magma G] {l : MagmaLaw α} (h : (Op G) ⊧ l) : G ⊧ l.op := by
  intro φ
  simp [op, satisfies]
  apply satisfiesPhi_op
  apply h

theorem implies_op {α} {l₁ l₂ : Law.MagmaLaw α} (h : l₁.implies l₂) : l₁.op.implies l₂.op := by
  simp [op, implies] at *
  intro G inst hsat
  apply satisfies_op_op
  apply h
  rw [← law_op_op l₁]
  apply satisfies_op_op
  exact hsat

end Law.MagmaLaw
