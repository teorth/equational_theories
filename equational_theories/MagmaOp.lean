/-
  This file defines the dual word and proves Lemma 3.5, that is
  (w ≃ w' ⇒ w'' ≃ w''') implies (w.op ≃ w'.op ⇒ w''.op ≃ w'''.op)
-/

import equational_theories.FreeMagma
import equational_theories.Completeness

#print FreeMagma

def FreeMagma.op {α} (w : FreeMagma α) : FreeMagma α :=
match w with
| .Leaf x => .Leaf x
| .Fork w₁ w₂ => .Fork w₂.op w₁.op

@[simp]
def Op (G : Type) : Type := G

@[simp]
instance opMagma {G : Type} [Magma G] : Magma (Op G) := { op := λ (x y : G) ↦ (y ∘ x : G) }

#check evalInMagma

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
