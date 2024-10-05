import equational_theories.EquationalResult
-- import equational_theories.AllEquations
import equational_theories.Homomorphisms

universe u
universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq

instance (α : Type u) : Magma (FreeMagma α) where
  op := FreeMagma.Fork

infixl:65 " ⋆ " => FreeMagma.Fork

instance {α : Type _} : Coe α (FreeMagma α) where
  coe a := FreeMagma.Leaf a

@[simp]
theorem FreeMagma_op_eq_fork (α : Type u) (a b : FreeMagma α) : a ◇ b = a ⋆ b := rfl

notation "Lf" => FreeMagma.Leaf

instance FreeMagma.isMagma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

namespace FreeMagma

def fmapFreeMagma {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β
  | Lf a => FreeMagma.Leaf (f a)
  | lchild ⋆ rchild => FreeMagma.Fork (fmapFreeMagma f lchild) (fmapFreeMagma f rchild)

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => (evalInMagma f lchild) ◇ (evalInMagma f rchild)

theorem evalHom {α : Type u} {G : Type v} [Magma G] (f : α → G) (map : G →◇ G) :
    evalInMagma (map ∘ f) = map ∘ evalInMagma f := by
  funext t
  induction t with
  | Leaf a => rfl
  | Fork lchild rchild ihl ihr => simp [evalInMagma, ihl, ihr, map.map_op]

end FreeMagma
