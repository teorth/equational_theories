import equational_theories.MagmaLaw
import equational_theories.Homomorphisms

open Law

class LiftingMagma (G : Type → Type) where
  instMagma {α} : Magma (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α}, (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α}, ∀ f : α → G α, f = (lift f) ∘ ι

instance {G : Type → Type} [LiftingMagma G] {α : Type} : Magma (G α) := LiftingMagma.instMagma

theorem MagmaLaw.models_iff_satisfies_ι {α : Type} {G : Type → Type} (law : MagmaLaw α) [LiftingMagma G] :
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagma.ι law := by
  constructor
  · intro h
    apply h
  · intro h
    intro f
    have := LiftingMagma.lift_factors f
    rw [this, satisfiesPhi.evalHom, h]

section Example

@[simp] theorem Fin2.match_eq (X : Sort _) (f : Fin 2 → X) : (fun | 0 => f 0 | 1 => f 1) = f := by
  funext i
  match i with
  | 0 | 1 => rfl

theorem Fin2.uncurry {X : Type _} (P : (Fin 2 → X) → Prop) : (∀ f : Fin 2 → X, P f) ↔
      ∀ x y : X, P (fun | 0 => x | 1 => y) := by
  constructor
  · intro h _ _
    apply h
  · intro h f
    have := h (f 0) (f 1)
    simpa only [match_eq]

theorem Fin2.models_iff (G  : Type _) [Magma G] (law : MagmaLaw (Fin 2)) : G ⊧ law ↔
    ∀ x y : G, satisfiesPhi (fun | 0 => x | 1 => y) law := by
  rw [satisfies, Fin2.uncurry]

def Law43 : MagmaLaw (Fin 2) := {
  lhs := (.Leaf 0) ⋆ (.Leaf 1),
  rhs := (.Leaf 1) ⋆ (.Leaf 0)
}

example (G  : Type _) [Magma G] : (G ⊧ Law43) ↔ Equation43 G := Fin2.models_iff G Law43

end Example
