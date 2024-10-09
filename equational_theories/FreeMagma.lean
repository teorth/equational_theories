import equational_theories.EquationalResult
import equational_theories.Homomorphisms

universe u
universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq

instance (α : Type u) : Magma (FreeMagma α) where
  op := FreeMagma.Fork

instance (α : Type u) : Coe α (FreeMagma α) where
  coe x := FreeMagma.Leaf x

instance {n : Nat} : OfNat (FreeMagma ℕ) n := ⟨FreeMagma.Leaf n⟩

open Lean in
def FreeMagma.toJson {α} [ToJson α] : FreeMagma α → Json
  | FreeMagma.Leaf x => .mkObj [("leaf", Lean.toJson x)]
  | FreeMagma.Fork x y => .mkObj [("left", toJson x), ("right", toJson y)]

open Lean in
instance {α} [ToJson α] : ToJson (FreeMagma α) where
  toJson := FreeMagma.toJson

infixl:65 " ⋆ " => FreeMagma.Fork

@[simp]
theorem FreeMagma_op_eq_fork (α : Type u) (a b : FreeMagma α) : a ◇ b = a ⋆ b := rfl

notation "Lf" => FreeMagma.Leaf

instance FreeMagma.isMagma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

namespace FreeMagma

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α -> G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => (evalInMagma f lchild) ◇ (evalInMagma f rchild)

def evalHom {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α →◇ G where
   toFun := evalInMagma f
   map_op' := fun _ _ ↦ rfl

 def fmapFreeMagma {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β :=
    evalInMagma (Lf ∘ f)

 def fmapHom {α : Type u} {β : Type v} (f : α → β) : FreeMagma α →◇ FreeMagma β :=
   evalHom (Lf ∘ f)

 theorem EvalFreeMagmaUniversalProperty {α : Type u} {G : Type v} [Magma G] (f : α → G)
    : ∀ g : FreeMagma α →◇ G, g.toFun ∘ Lf = f → evalInMagma f = g.toFun := by
   intros g glift
   let rec equiv : ∀ tx : FreeMagma α, evalInMagma f tx = g.toFun tx := fun tx ↦
      match tx with
      | FreeMagma.Leaf x => Eq.symm $ congrFun glift x
      | FreeMagma.Fork txleft txright => Eq.trans
         (congrArg (fun t ↦ t ◇ evalInMagma f txright) (equiv txleft)) $ Eq.trans
         (congrArg (fun t ↦ g.toFun txleft ◇ t) (equiv txright))
         (Eq.symm $ g.map_op' txleft txright)
   exact (funext equiv)

 theorem FmapFreeMagmaUniversalProperty {α : Type u} {β : Type u} (f : α → β)
    : ∀ g : FreeMagma α →◇ FreeMagma β, g ∘ Lf = Lf ∘ f → fmapFreeMagma f = g :=
    EvalFreeMagmaUniversalProperty (Lf ∘ f)

theorem evalInMagma_comp {α β} {G} [Magma G] (f : α → β) (g : β → G) :
  ∀ (x : FreeMagma α), evalInMagma (g ∘ f) x = evalInMagma g (fmapFreeMagma f x) := by
  intro x
  induction x <;> simp [fmapFreeMagma, evalInMagma, *]

lemma Fin0_impossible (x : FreeMagma (Fin 0)) : False := by
  induction x
  case Leaf l =>
    cases l; contradiction
  case Fork => assumption

def length {α : Type} : FreeMagma α → Nat
  | .Leaf _ => 1
  | .Fork m1 m2 => FreeMagma.length m1 + FreeMagma.length m2

theorem length_pos {α : Type} : (x : FreeMagma α) → 0 < FreeMagma.length x
  | .Leaf _ => by simp [FreeMagma.length]
  | .Fork m1 m2 => by
    have h1 := FreeMagma.length_pos m1
    have h2 := FreeMagma.length_pos m2
    simp [FreeMagma.length]
    omega

@[simp]
theorem length_ne_0 {α : Type} (x : FreeMagma α) : FreeMagma.length x ≠ 0 :=
  Nat.not_eq_zero_of_lt x.length_pos

end FreeMagma
