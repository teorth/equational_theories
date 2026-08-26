import equational_theories.Completeness
import equational_theories.Equations.All
import equational_theories.Homomorphisms

namespace M4

variable {α : Type}

def Left (α : Type) := α

instance : Magma (Left α) where
  op x _ := x

def left (a : α) : Left α := a

theorem models4 : Left α ⊧ Law4 := by intro ; rfl
theorem models4' : Left α ⊧ {Law4} := by simp [satisfiesSet]; exact models4

def extract : FreeMagmaWithLaws α {Law4} →◇ Left α :=
  FreeMagmaWithLaws.evalHom left models4'

theorem law4_eq4 {G} [Magma G] (h : G ⊧ Law4) (x y : G) : x = x ◇ y :=
  h (fun | 0 => x | _ => y)

def leftmost : FreeMagma α → α
  | FreeMagma.Leaf a => a
  | FreeMagma.Fork l _ => leftmost l

theorem leftmost_fork (l r : FreeMagma α) : leftmost (l ⋆ r) = leftmost l := by simp [leftmost]

theorem eval_leftmost {G} [Magma G] (h : G ⊧ Law4) (x : FreeMagma α) (f : α → G) :
    FreeMagma.evalInMagma f x = f (leftmost x) := by
  induction x with
  | Leaf => simp [FreeMagma.evalInMagma, leftmost]
  | Fork l _ hi _ => simp [FreeMagma.evalInMagma, leftmost, ←law4_eq4 h, hi]

theorem extract_embed (x : FreeMagma α) : extract (embed {Law4} x) = leftmost x := by
  apply eval_leftmost models4

-- Should go in Completeness.lean?
@[simp] def isModelSingleLaw (E : Law.NatMagmaLaw) : FreeMagmaWithLaws α {E} ⊧ E := by
  apply FreeMagmaWithLaws.isModel
  simp

theorem embed_law4_fork (l r : FreeMagma α) : embed {Law4} (l ⋆ r) = embed {Law4} l := by
  have h : l ⋆ r = l ◇ r := Eq.refl (l ⋆ r)
  rw [h, embed_fork]
  simp [←law4_eq4]

theorem embed_leftmost (x : FreeMagma α) : embed {Law4} x = LfEmbed {Law4} (leftmost x) := by
  induction x with
  | Leaf => rfl
  | Fork l r ih _ => rw [leftmost_fork, embed_law4_fork, ih]

def freeMagmaWith4 : FreeMagmaWithLaws α {Law4} ≃◇ Left α where
  toFun := extract
  invFun := LfEmbed {Law4}
  left_inv x := by
    refine FreeMagmaWithLaws.inductionOn x fun x => ?_
    rw [extract_embed, embed_leftmost]
  right_inv _ := by simp [extract]; rfl
  map_op' := extract.map_op'
