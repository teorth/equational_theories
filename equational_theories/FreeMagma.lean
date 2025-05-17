import equational_theories.Homomorphisms
import Mathlib.Data.List.NodupEquivFin

universe u
universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq

instance (α : Type u) [Inhabited α] : Inhabited (FreeMagma α) where
  default := .Leaf default

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

def FreeMagma.toString {α} [ToString α] (outermost : Bool) : FreeMagma α → String
  | FreeMagma.Leaf x => s!"{x}"
  | FreeMagma.Fork x y =>
    let s := s!"{x.toString false} ◇ {y.toString false}"
    if outermost then s else s!"({s})"

instance {α} [ToString α] : ToString (FreeMagma α) where
  toString := FreeMagma.toString true

infixl:65 " ⋆ " => FreeMagma.Fork

@[simp]
theorem FreeMagma_op_eq_fork (α : Type u) (a b : FreeMagma α) : a ◇ b = a ⋆ b := rfl

notation "Lf" => FreeMagma.Leaf

instance FreeMagma.isMagma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

namespace FreeMagma

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => evalInMagma f lchild ◇ evalInMagma f rchild

notation:63 t:63 " ⬝ " σ:64 => evalInMagma σ t

def evalHom {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α →◇ G where
   toFun := evalInMagma f
   map_op' := fun _ _ ↦ rfl

@[simp] theorem evalHom_apply {α G} [Magma G] (f : α → G) (m : FreeMagma α) :
    evalHom f m = evalInMagma f m := rfl

theorem evalInMagma_leaf {α} (m : FreeMagma α) : m ⬝ Lf = m := by
  induction m <;> simp [evalInMagma, *]

 def fmapFreeMagma {α : Type u} {β : Type v} (f : α → β) : FreeMagma α → FreeMagma β :=
    evalInMagma (Lf ∘ f)

 def fmapHom {α : Type u} {β : Type v} (f : α → β) : FreeMagma α →◇ FreeMagma β :=
   evalHom (Lf ∘ f)

theorem evalInMagma_hom {α G H} [Magma G] [Magma H] (f : α → G) (g : G →◇ H) (m : FreeMagma α) :
    g (m ⬝ f) = m ⬝ (g ∘ f) := by
  induction m <;> simp [evalInMagma, g.map_op, *]

theorem evalInMagma_equiv {α G H} [Magma G] [Magma H] (f : α → G) (g : G ≃◇ H) (m : FreeMagma α) :
    g (m ⬝ f) = m ⬝ (g ∘ f) :=
  evalInMagma_hom f (MagmaHomClass.toMagmaHom g) m

theorem SubstEval {α β G} [Magma G] (t : FreeMagma α) (σ : α → FreeMagma β) (φ : β → G) :
    t ⬝ σ ⬝ φ = t ⬝ (evalInMagma φ ∘ σ) :=
  evalInMagma_hom _ (evalHom _) _

theorem evalInMagma_fmapHom {α β G} [Magma G] (f : α → β) (g : β → G) (m : FreeMagma α) :
    fmapHom f m ⬝ g = m ⬝ (g ∘ f) := by
  show evalInMagma g (evalInMagma (Lf ∘ f) m) = evalInMagma (g ∘ f) m
  induction m <;> simp [evalInMagma, *]

theorem evalInMagma_comp {α β} {G} [Magma G] (f : α → β) (g : β → G) (m : FreeMagma α) :
    m ⬝ (g ∘ f) = fmapFreeMagma f m ⬝ g :=
  (evalInMagma_fmapHom ..).symm

theorem evalHom_comp_fmapHom {α β G} [Magma G] (f : α → β) (g : β → G) :
    (fmapHom f).comp (evalHom g) = evalHom (g ∘ f) := by
  ext; apply evalInMagma_fmapHom

theorem fmapHom_comp' {α β γ} (f : α → β) (g : β → γ) (m : FreeMagma α) :
    fmapHom g (fmapHom f m) = fmapHom (g ∘ f) m := by
  rw [fmapHom, evalHom_apply, evalInMagma_fmapHom]; rfl

theorem fmapHom_comp {α β γ} (f : α → β) (g : β → γ) :
    (fmapHom f).comp (fmapHom g) = fmapHom (g ∘ f) := by
  ext; apply fmapHom_comp'

theorem fmapHom_id {α} (m : FreeMagma α) : fmapHom id m = m := evalInMagma_leaf _

 theorem EvalFreeMagmaUniversalProperty {α : Type u} {G : Type v} [Magma G] (f : α → G) :
    ∀ g : FreeMagma α →◇ G, g.toFun ∘ Lf = f → evalInMagma f = g.toFun := by
   intro g glift
   let rec equiv : ∀ tx : FreeMagma α, evalInMagma f tx = g.toFun tx := fun tx ↦
      match tx with
      | FreeMagma.Leaf x => (congrFun glift x).symm
      | FreeMagma.Fork txleft txright =>
        (congrArg (fun t ↦ t ◇ evalInMagma f txright) (equiv txleft)).trans
          ((congrArg (fun t ↦ g.toFun txleft ◇ t) (equiv txright)).trans
            (g.map_op' txleft txright).symm)
   exact (funext equiv)

 theorem FmapFreeMagmaUniversalProperty {α : Type u} {β : Type u} (f : α → β) :
      ∀ g : FreeMagma α →◇ FreeMagma β, g ∘ Lf = Lf ∘ f → fmapFreeMagma f = g :=
    EvalFreeMagmaUniversalProperty (Lf ∘ f)

def Mem {α} (a : α) : FreeMagma α → Prop
  | Lf a' => a = a'
  | lchild ⋆ rchild => Mem a lchild ∨ Mem a rchild

def first {α} : FreeMagma α → α
  | Lf a => a
  | lchild ⋆ _ => lchild.first

def last {α} : FreeMagma α → α
  | Lf a => a
  | _ ⋆ rchild => rchild.last

theorem first_mem {α} : ∀ m : FreeMagma α, Mem m.first m
  | Lf _ => rfl
  | lchild ⋆ _ => .inl lchild.first_mem

lemma Fin0_impossible (x : FreeMagma (Fin 0)) : False := nomatch x.first

def forks {α} : FreeMagma α → Nat
  | .Leaf _ => 0
  | .Fork m1 m2 => (m1.forks + m2.forks).succ

theorem forks_left_lt_self {α} (x y : FreeMagma α) : x.forks < (x ⋆ y).forks := by
  simp only [forks]
  omega

theorem forks_right_lt_self {α} (x y : FreeMagma α) : y.forks < (x ⋆ y).forks := by
  simp only [forks]
  omega

@[simp] theorem map_forks {α β} (m : FreeMagma α) (f : α → β) :
    (fmapHom f m).forks = m.forks := by
  induction m with
  | Leaf a => rfl
  | Fork m1 m2 ih1 ih2 => simp [fmapHom, evalInMagma, forks, ih1, ih2] at *

@[simp] def length {α} : FreeMagma α → Nat
  | .Leaf _ => 1
  | .Fork m1 m2 => FreeMagma.length m1 + FreeMagma.length m2

lemma length_eq_succ_forks {α} (x: FreeMagma α) : x.length = x.forks.succ := by
  induction x with
  | Leaf =>
    simp [length, forks]
  | Fork x y hx hy =>
    simp [hx, hy, length, forks]
    omega

theorem length_pos {α} (x : FreeMagma α): 0 < FreeMagma.length x := by
  rw [length_eq_succ_forks]
  exact Nat.zero_lt_succ _

@[simp]
theorem length_ne_0 {α} (x : FreeMagma α) : FreeMagma.length x ≠ 0 :=
  Nat.ne_zero_of_lt x.length_pos

theorem length_left_lt_self {α} (x y : FreeMagma α) : x.length < (x ⋆ y).length := by
  simp only [length, Nat.lt_add_right_iff_pos]
  exact length_pos y

theorem length_right_lt_self {α} (x y : FreeMagma α) : y.length < (x ⋆ y).length := by
  simp only [length, Nat.lt_add_left_iff_pos]
  exact length_pos x

@[simp] def toList {α} : FreeMagma α → List α
  | Lf a => [a]
  | l ⋆ r => l.toList ++ r.toList

private def toListTR {α} : FreeMagma α → List α := go [] where
  go : List α → FreeMagma α → List α
  | acc, Lf a => a :: acc
  | acc, l ⋆ r => go (go acc r) l

@[csimp] private theorem toList_eq_toListTR : @toList = @toListTR := by
  funext α m
  have (m acc) : @toListTR.go α acc m = toList m ++ acc := by
    induction m generalizing acc <;> simp [toListTR.go, toList, *]
  simpa using (this m []).symm

theorem toList_length {α} (m : FreeMagma α) : m.toList.length = m.length := by
  induction m <;> simp [*]

@[simp] def map_toList {α β} (m : FreeMagma α) (f : α → β) :
    (fmapHom f m).toList = m.toList.map f := by
  induction m with
  | Leaf a => rfl
  | Fork m1 m2 ih1 ih2 => simp [fmapHom, evalInMagma, ih1, ih2] at *

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
    m.pmap f ⬝ φ = m ⬝ ψ := by
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
