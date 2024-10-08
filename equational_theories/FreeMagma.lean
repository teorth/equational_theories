import equational_theories.AllEquations
import equational_theories.EquationalResult
import equational_theories.Homomorphisms
import Mathlib.Data.List.NodupEquivFin

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

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => evalInMagma f lchild ◇ evalInMagma f rchild

def evalHom {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α →◇ G where
   toFun := evalInMagma f
   map_op' := fun _ _ ↦ refl _

@[simp] theorem evalHom_apply {α G} [Magma G] (f : α → G) (m : FreeMagma α) :
    evalHom f m = evalInMagma f m := rfl

theorem evalInMagma_leaf {α} (m : FreeMagma α) : evalInMagma Lf m = m := by
  induction m <;> simp [evalInMagma, *]

 def fmapFreeMagma {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β :=
    evalInMagma (Lf ∘ f)

 def fmapHom {α : Type u} {β : Type v} (f : α → β) : FreeMagma α →◇ FreeMagma β :=
   evalHom (Lf ∘ f)

theorem evalInMagma_hom {α G H} [Magma G] [Magma H] (f : α → G) (g : G →◇ H) (m : FreeMagma α) :
    g (evalInMagma f m) = evalInMagma (g ∘ f) m := by
  induction m <;> simp [evalInMagma, g.map_op, *]

theorem evalInMagma_equiv {α G H} [Magma G] [Magma H] (f : α → G) (g : G ≃◇ H) (m : FreeMagma α) :
    g (evalInMagma f m) = evalInMagma (g ∘ f) m :=
  evalInMagma_hom f (MagmaHomClass.toMagmaHom g) m

theorem SubstEval {α β G} [Magma G] (t : FreeMagma α) (σ : α → FreeMagma β) (φ : β → G) :
    evalInMagma φ (evalInMagma σ t) = evalInMagma (evalInMagma φ ∘ σ) t :=
  evalInMagma_hom _ (evalHom _) _

theorem evalInMagma_fmapHom {α β G} [Magma G] (f : α → β) (g : β → G) (m : FreeMagma α) :
    evalInMagma g (fmapHom f m) = evalInMagma (g ∘ f) m := by
  show evalInMagma g (evalInMagma (Lf ∘ f) m) = evalInMagma (g ∘ f) m
  induction m <;> simp [evalInMagma, *]

theorem evalHom_comp_fmapHom {α β G} [Magma G] (f : α → β) (g : β → G) :
    (fmapHom f).comp (evalHom g) = evalHom (g ∘ f) := by
  ext m; apply evalInMagma_fmapHom

theorem fmapHom_comp' {α β γ} (f : α → β) (g : β → γ) (m : FreeMagma α) :
    fmapHom g (fmapHom f m) = fmapHom (g ∘ f) m := by
  rw [fmapHom, evalHom_apply, evalInMagma_fmapHom]; rfl

theorem fmapHom_comp {α β γ} (f : α → β) (g : β → γ) :
    (fmapHom f).comp (fmapHom g) = fmapHom (g ∘ f) := by
  ext m; apply fmapHom_comp'

theorem fmapHom_id {α} (m : FreeMagma α) : fmapHom id m = m := evalInMagma_leaf _

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

def Mem {α} (a : α) : FreeMagma α → Prop
  | Lf a' => a = a'
  | lchild ⋆ rchild => Mem a lchild ∨ Mem a rchild

def first {α} : FreeMagma α → α
  | Lf a => a
  | lchild ⋆ _ => lchild.first

theorem first_mem {α} : ∀ m : FreeMagma α, Mem m.first m
  | Lf _ => rfl
  | lchild ⋆ _ => .inl lchild.first_mem

def elems {α} [DecidableEq α] : (m : FreeMagma α) → {l : List α // l.Nodup ∧ ∀ a, a ∈ l ↔ Mem a m}
  | Lf a => ⟨[a], List.nodup_singleton _, by simp [Mem]⟩
  | lchild ⋆ rchild => by
    let ⟨l, _, hl⟩ := lchild.elems
    let ⟨r, nr, hr⟩ := rchild.elems
    use l ∪ r, .union _ nr; simp [Mem, hl, hr]

def finEquiv {α} [DecidableEq α] (m : FreeMagma α) : Fin m.elems.1.length ≃ {a // Mem a m} := by
  convert ← m.elems.2.1.getEquiv; apply m.elems.2.2

def pmap {α β} : ∀ (m : FreeMagma α), (∀ a, Mem a m → β) → FreeMagma β
  | Lf a, f => Lf (f a rfl)
  | lchild ⋆ rchild, f =>
    pmap lchild (fun a h => f a (.inl h)) ⋆ pmap rchild (fun a h => f a (.inr h))

def attach {α} (m : FreeMagma α) : FreeMagma {a // Mem a m} := pmap m .mk

def toFin {α} [DecidableEq α] (m : FreeMagma α) : FreeMagma (Fin m.elems.1.length) :=
  fmapHom (finEquiv m).symm m.attach

def toNat {α} [DecidableEq α] (m : FreeMagma α) : FreeMagma ℕ :=
  fmapHom (·.val) (toFin m)

theorem evalInMagma_pmap {α β G} [Magma G] {φ : β → G} {ψ : α → G}
    (m : FreeMagma α) {f : (a : α) → Mem a m → β} (H : ∀ a h, φ (f a h) = ψ a) :
    evalInMagma φ (m.pmap f) = evalInMagma ψ m := by
  induction m <;> simp [pmap, evalInMagma, *]

theorem attach_map_val {α} (m : FreeMagma α) : fmapHom (·.val) m.attach = m :=
  (evalInMagma_pmap _ (by simp)).trans (fmapHom_id _)

theorem mem_evalInMagma_of_mem {α β a b} {f : α → FreeMagma β} :
    ∀ {m : FreeMagma α}, Mem b m → Mem a (f b) → Mem a (evalInMagma f m)
  | Lf _, rfl, h => h
  | _ ⋆ _, .inl h1, h2 => .inl <| mem_evalInMagma_of_mem h1 h2
  | _ ⋆ _, .inr h1, h2 => .inr <| mem_evalInMagma_of_mem h1 h2

theorem pmap_evalInMagma {α β γ} (f : α → FreeMagma β) (m : FreeMagma α)
    (g : (a : β) → Mem a (evalInMagma f m) → γ)
    (k : α → FreeMagma γ)
    (h : ∀ a ha, ((f a).pmap fun b hb => g b (mem_evalInMagma_of_mem ha hb)) = k a) :
    (evalInMagma f m).pmap g = evalInMagma k m := by
  induction m with simp [evalInMagma, pmap, *]
  | Leaf => exact h _ rfl
  | Fork _ _ iha ihb => exact ⟨iha _ fun a ha => h a (.inl ha), ihb _ fun a ha => h a (.inr ha)⟩

theorem pmap_eq_map {α β} (m : FreeMagma α)
    (f : (a : α) → Mem a m → β) (g : α → β) (h : ∀ a h, f a h = g a) :
    m.pmap f = fmapHom g m := by
  simp [fmapHom]; induction m <;> simp [evalInMagma, pmap, *]

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
