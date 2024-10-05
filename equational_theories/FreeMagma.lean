import equational_theories.AllEquations
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
   map_op' := fun _ _ ↦ refl _

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

 theorem FmapFreeMagmaUniversalProperty {α : Type u} [Magma α] {β : Type u} (f : α → β)
    : ∀ g : FreeMagma α →◇ FreeMagma β, g ∘ Lf = Lf ∘ f → fmapFreeMagma f = g :=
    EvalFreeMagmaUniversalProperty (Lf ∘ f)

end FreeMagma

theorem ExpressionEqualsAnything_implies_Equation2 (G: Type u) [Magma G] :
    (∃ n : Nat, ∃ expr : FreeMagma (Fin n), ∀ x : G, ∀ sub : Fin n → G, x = expr.evalInMagma sub) → Equation2 G := by
  intro ⟨n, expr, univ⟩ x y
  let constx : Fin n → G := fun _ ↦ x
  exact (univ x constx).trans (univ y constx).symm

theorem Equation37_implies_Equation2 (G : Type u) [Magma G] :
    (∀ x y z w : G, x = (y ◇ z) ◇ w) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    3,
    (Lf 0 ⋆ Lf 1) ⋆ Lf 2, -- The syntactic representation of (y ◇ z) ◇ w
    fun k sub ↦ univ k (sub 0) (sub 1) (sub 2)
  ⟩

theorem Equation514_implies_Equation2 (G : Type u) [Magma G] :
    (∀ x y : G, x = y ◇ (y ◇ (y ◇ y))) → Equation2 G :=
  fun univ ↦ ExpressionEqualsAnything_implies_Equation2 G ⟨
    1,
    Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)), -- The syntactic representation of y ◇ (y ◇ (y ◇ y)))
    fun k sub ↦ univ k (sub 0)
  ⟩
