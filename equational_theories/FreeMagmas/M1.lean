import equational_theories.Completeness
import equational_theories.Equations.All
import equational_theories.Homomorphisms

namespace M1

variable {α : Type}

theorem models1 : FreeMagma α ⊧ Law1 := by intro ; rfl
theorem models1' : FreeMagma α ⊧ {Law1} := by simp [satisfiesSet]; exact models1

def extract : FreeMagmaWithLaws α {Law1} →◇ FreeMagma α :=
  FreeMagmaWithLaws.evalHom Lf models1'

def freeMagmaWith1 : FreeMagmaWithLaws α {Law1} ≃◇ FreeMagma α where
  toFun := extract
  invFun x := embed {Law1} x
  left_inv x := by
    refine FreeMagmaWithLaws.inductionOn x fun x => ?_
    induction x with
    | Leaf => simp [extract]
    | Fork l r ih1 ih2 =>
      simp at ih1 ih2
      have h : l ⋆ r = l ◇ r := Eq.refl (l ⋆ r)
      simp ; rw [h, embed_fork, MagmaHom.map_op, embed_fork, ih1, ih2]
  right_inv x := by
    induction x with
    | Leaf x => simp [extract]
    | Fork l r ih1 ih2 =>
      have h : l ⋆ r = l ◇ r := Eq.refl (l ⋆ r)
      simp ; rw [h, embed_fork, MagmaHom.map_op, ih1, ih2]
  map_op' := extract.map_op'
