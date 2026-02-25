import equational_theories.Completeness
import equational_theories.Equations.All
import equational_theories.Homomorphisms

namespace M2

variable {α : Type} [Inhabited α]

instance : Magma Unit where
  op _ _ := ()

theorem models2 : Unit ⊧ Law2 := by intro ; simp [satisfiesPhi]

-- Should go in Completeness.lean?
@[simp] def isModelSingleLaw (E : Law.NatMagmaLaw) : FreeMagmaWithLaws α {E} ⊧ E := by
  apply FreeMagmaWithLaws.isModel
  simp

theorem law2_eq2 {G} [Magma G] (h : G ⊧ Law2) (x y : G) : x = y :=
  h (fun | 0 => x | _ => y)

def freeMagmaWith2 : FreeMagmaWithLaws α {Law2} ≃◇ Unit where
  toFun _ := ()
  invFun _ := LfEmbed {Law2} default
  left_inv x := by
    simp
    exact law2_eq2 (isModelSingleLaw Law2) _ _
  right_inv x := by simp [Function.RightInverse, Function.LeftInverse]
  map_op' := by simp
