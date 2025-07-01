/-
Copyright (c) 2024 Cody Roux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Roux, Judah Towery
-/
import equational_theories.Magma
import Mathlib.Order.BooleanAlgebra

/-!
In this file we introduce "Sheffer Algebras", which are simply a presentation of Boolean Algebras,
but with a single operation, the Sheffer stroke, or NAND, as the only primitive operation.
This operation satisfies 3 laws, the Sheffer axioms.

The structure of the development roughly follows the original Sheffer paper, "A set of five
independent postulates for Boolean algebras, with application to logical constants".

The main result of this file is that the Sheffer stroke is a complete axiomatization of Boolean
Algebras, and vice versa. The latter is done by showing that the Sheffer stroke
(defined as `a | b = (a ∧ b)ᶜ`) satisfies the three Sheffer axioms.

The other direction is a bit more fiddly, and requires a careful set of lemmas, which give a
structure involving `⊔` and `⊓` which is similar but distinct from the ring structure of a Boolean
Ring. The final tie in with actual Boolean algebras follows the surprisingly detailed Wikipedia
article found here: https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Axiomatics

We also introduce a class for the Sheffer stroke notation, for convenience.

-/

section ShefferLaws

-- Taking notations from https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf and
-- the original Sheffer paper, "A set of five independent postulates for Boolean algebras,
-- with application to logical constants"
class Stroke (α : Type*) where
  stroke : α → α → α

infix:80 " | " => Stroke.stroke

def prime {α} [Stroke α] (a : α) := a | a

postfix:max " ′ " => prime

-- The three laws axiomatize the Sheffer stroke, or NAND, entirely.
-- The remainder of this file is dedicated to that proof.
class ShefferAlgebra (α : Type*) extends Stroke α where
-- We need to assume α is nonempty
elt : α
sh₁ : ∀ a : α, a′′ = a
sh₂ : ∀ a b : α, a | (b | b′) = a′
sh₃ : ∀ a b c : α, (a | (b | c))′ = (b′ | a) | (c′ | a)

variable {α : Type*}

variable [ShefferAlgebra α]

open ShefferAlgebra

lemma commut (a b : α) : a | b = b | a := by
  calc
    a | b = (a | b)′′ := by rw [sh₁]
    _     = (a | (b′′))′′ := by rw [sh₁ b]
    _     = (b′′ | a)′′ := by conv => left; arg 1; arg 1; simp [prime]
                              conv => left; arg 1; rw [sh₃]
                              rfl
    _     = b | a := by repeat rw [sh₁]

lemma all_bot (a b : α) : a | a′ = b | b′ := by
  calc
    a | a′ = (a | a′)′′ := by rw [sh₁]
    _      = ((a | a′) | (b | b′))′ := by rw [sh₂]
    _      = ((b | b′) | (a | a′))′ := by rw [commut]
    _      = (b | b′)′′ := by rw [sh₂]
    _      = b | b′     := by rw [sh₁]

instance : Min α where
  min a b := (a′ | b′)

lemma inf (a b : α) : a ⊓ b = (a′ | b′) := rfl

instance : Max α where
 max a b := (a | b)′

lemma sup (a b : α) : a ⊔ b = (a | b)′ := rfl

instance : HasCompl α where
  compl a := a′

lemma comple (a : α) : aᶜ = a′ := rfl

def z : α := elt | elt′

def u : α := z′

lemma commut₁ (a b : α) : a ⊔ b = b ⊔ a := by simp only [sup, commut]

lemma commut₂ (a b : α) : a ⊓ b = b ⊓ a := by simp only [inf, commut]

@[simp]
lemma ident₁ (a : α) : a ⊔ z = a := by simp only [sup, z, sh₁, sh₂]

@[simp]
lemma ident₂ (a : α) : a ⊓ u = a := by simp only [inf, u, z, sh₁, sh₂]

lemma distrib₁ (a b c : α) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  simp only [sup, inf, sh₁, sh₃, commut]

lemma distrib₂ (a b c : α) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  simp only [sup, inf, sh₁]
  conv => left; exact (sh₁ _).symm
  rw [sh₃]
  exact congr rfl (congr (congr rfl (commut ..)) (commut ..))

@[simp]
lemma compl₁ (a : α) : a ⊔ aᶜ = u := by
  simp only [sup, u, z, comple]
  exact congr rfl (all_bot a elt)

@[simp]
lemma compl₂ (a  : α) : a ⊓ aᶜ = z := by
  simp only [inf, z, u, comple, sh₁, commut]
  exact all_bot a elt

@[simp]
lemma bound₁ (a : α) : a ⊔ u = u := by
  calc
    a ⊔ u = (a ⊔ u) ⊓ u        := by rw [ident₂]
    _     = u ⊓ (a ⊔ u)        := by rw [commut₂]
    _     = (a ⊔ aᶜ) ⊓ (a ⊔ u) := by rw [compl₁]
    _     = a ⊔ (aᶜ ⊓ u)       := by rw [distrib₁]
    _     = a ⊔ aᶜ             := by rw [ident₂]
    _     = u                  := compl₁ a

@[simp]
lemma bound₂ (a : α) : a ⊓ z = z := by
  calc
    a ⊓ z = (a ⊓ z) ⊔ z        := by rw [ident₁]
    _     = z ⊔ (a ⊓ z)        := by rw [commut₁]
    _     = (a ⊓ aᶜ) ⊔ (a ⊓ z) := by rw [compl₂]
    _     = a ⊓ (aᶜ ⊔ z)       := by rw [distrib₂]
    _     = a ⊓ aᶜ             := by rw [ident₁]
    _     = z                  := compl₂ a

@[simp] -- This simp is a little overeager.
lemma absorb₁ (a b : α) : a ⊔ (a ⊓ b) = a := by
  calc
    a ⊔ (a ⊓ b) = (a ⊓ u) ⊔ (a ⊓ b) := by rw [ident₂]
    _           = a ⊓ (u ⊔ b)       := by rw [distrib₂]
    _           = a ⊓ (b ⊔ u)       := by conv => lhs; rw [commut₁]
    _           = a ⊓ u             := by rw [bound₁]
    _           = a                 := ident₂ a

-- it would be nice to have a "dualization" tactic. This might be some work though.
@[simp] -- This simp is a little overeager.
lemma absorb₂ (a b : α) : a ⊓ (a ⊔ b) = a := by
  calc
    a ⊓ (a ⊔ b) = (a ⊔ z) ⊓ (a ⊔ b) := by rw [ident₁]
    _           = a ⊔ (z ⊓ b)       := by rw [distrib₁]
    _           = a ⊔ (b ⊓ z)       := by conv => lhs; rw [commut₂]
    _           = a ⊔ z             := by rw [bound₂]
    _           = a                 := ident₁ a

@[simp]
lemma idemp₂ (a : α) : a ⊓ a = a := by
  symm
  calc
    a = a ⊓ (a ⊔ z) := Eq.symm (absorb₂ a z)
    _ = a ⊓ a       := by rw [ident₁]

lemma inv (a a' : α) : a ⊔ a' = u → a ⊓ a' = z → a' = aᶜ := by
  intro h₁ h₂
  calc
    a' = a' ⊓ u               := Eq.symm (ident₂ a')
    _  = a' ⊓ (a ⊔ aᶜ)        := by rw [compl₁]
    _  = (a' ⊓ a) ⊔ (a' ⊓ aᶜ) := by rw [distrib₂]
    _  = (a' ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; right; exact commut₂ a' aᶜ
    _  = (a ⊓ a') ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a' a
    _  = z ⊔ (aᶜ ⊓ a')        := by rw [h₂]
    _  = (a ⊓ aᶜ) ⊔ (aᶜ ⊓ a') := by rw [compl₂]
    _  = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a aᶜ
    _  = aᶜ ⊓ (a ⊔ a')        := by rw [distrib₂]
    _  = aᶜ ⊓ u               := by rw [h₁]
    _  = aᶜ                   := ident₂ aᶜ

lemma dne (a : α) : aᶜᶜ = a := by
  symm
  apply inv
  . rw [commut₁]; exact compl₁ a
  . rw [commut₂]; exact compl₂ a

lemma inv_elim (a b : α) : aᶜ = bᶜ → a = b := by
  intro h
  have h' : aᶜᶜ = bᶜᶜ := congrArg compl h
  simp only [dne] at h'
  trivial

lemma cancel (a b : α) : a ⊔ bᶜ = u → a ⊓ bᶜ = z → a = b := by
  intro h₁ h₂
  have h : bᶜ = aᶜ := by apply inv <;> trivial
  apply inv_elim; symm; trivial

/-
From here on, we temporarily depart from standard Mathlib naming conventions to conform to
https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Axiomatics
-/
@[simp]
lemma A₁ (a b : α) : a ⊔ (aᶜ ⊔ b) = u := by
  calc
    a ⊔ (aᶜ ⊔ b) = (a ⊔ (aᶜ ⊔ b)) ⊓ u := by rw [ident₂]
    _            = u ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [commut₂]
    _            = (a ⊔ aᶜ) ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [compl₁]
    _            = a ⊔ (aᶜ ⊓ (aᶜ ⊔ b)) := by rw [distrib₁]
    _            = a ⊔ aᶜ := by rw [absorb₂, compl₁]
    _            = u := by rw [compl₁]

@[simp]
lemma A₂ (a b : α) : a ⊓ (aᶜ ⊓ b) = z := by
  calc
    a ⊓ (aᶜ ⊓ b) = (a ⊓ (aᶜ ⊓ b)) ⊔ z := by rw [ident₁]
    _            = z ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [commut₁]
    _            = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [compl₂]
    _            = a ⊓ (aᶜ ⊔ (aᶜ ⊓ b)) := by rw [distrib₂]
    _            = a ⊓ aᶜ := by rw [absorb₁, compl₂]
    _            = z := by rw [compl₂]


@[simp]
lemma dm₁ (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₁, distrib₁]
    conv => left; left; rw [commut₁]; right; left; exact Eq.symm (dne a)
    rw [A₁, commut₂, ident₂, commut₁]
    conv => left; right; rw [commut₁]; left; exact Eq.symm (dne b)
    simp
  . rw [distrib₂]
    conv => left; left; rw [commut₂]
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]
    simp

@[simp]
lemma dm₂ (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₂, distrib₁]
    conv => left; left; rw [commut₁]; right; rw [commut₁]
    rw [A₁, commut₂, ident₂]
    rw [commut₁]
    rw [A₁]
  . rw [commut₂, distrib₂]
    conv => left; left; rw [commut₂]; right; left; exact Eq.symm (dne a)
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]; left; exact Eq.symm (dne b)
    rw [A₂]

lemma D₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ aᶜ = u := by
  rw [commut₁]
  conv => left; right; left; exact Eq.symm (dne a)
  simp

lemma E₁ (a b c : α) : b ⊓ (a ⊔ (b ⊔ c)) = b := by rw [distrib₂, absorb₂, commut₁, absorb₁]

lemma E₂ (a b c : α) : b ⊔ (a ⊓ (b ⊓ c)) = b := by rw [distrib₁, absorb₁, commut₂, absorb₂]

lemma F₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ bᶜ = u := by
  calc
    (a ⊔ (b ⊔ c)) ⊔ bᶜ = bᶜ ⊔ (a ⊔ (b ⊔ c)) := by rw [commut₁]
    _                  = u ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₂]; simp
    _                  = (b ⊔ bᶜ) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by simp
    _                  = (bᶜ ⊔ b) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₁]
    _                  = bᶜ ⊔ (b ⊓ (a ⊔ (b ⊔ c))) := by rw [distrib₁]
    _                  = bᶜ ⊔ b := by rw [E₁]
    _                  = u := by rw [commut₁]; simp

lemma G₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ cᶜ = u := by
  conv => left; left; right; rw [commut₁]
  apply F₁

lemma H₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ a = z := by
  simp; rw [commut₂]
  calc
    a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ) = (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) ⊔ z := by rw [ident₁]
    _                  = z ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [commut₁]
    _                  = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [compl₂]
    _                  = a ⊓ (aᶜ ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [distrib₂]
    _                  = a ⊓ (aᶜ ⊔ (cᶜ ⊓ (aᶜ ⊓ bᶜ))) := by conv => left; right; right; rw [commut₂]
    _                  = a ⊓ aᶜ := by rw [E₂]
    _                  = z := by rw [compl₂]

lemma I₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ b = z := by
  conv => left; left; arg 1; left; rw [commut₁]
  exact H₁ ..

lemma J₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ c = z := by
  simp
  rw [commut₂]
  conv => left; right; rw [commut₂]
  simp

-- Incredibly, these are derivable
@[simp]
lemma assoc₁ (a b c : α) : a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  apply cancel; simp
  . calc
      (a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ) = ((a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ)) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) :=
        by rw [distrib₁]
      _ = ((a ⊔ (b ⊔ c) ⊔ aᶜ) ⊓ ((a ⊔ (b ⊔ c) ⊔ bᶜ))) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _ = (u ⊓ u) ⊓ u := by rw [D₁, F₁, G₁]
      _ = u := by simp
  . rw [commut₂]
    rw [distrib₂]; rw [distrib₂]
    calc
      (a ⊔ b ⊔ c)ᶜ ⊓ a ⊔ ((a ⊔ b ⊔ c)ᶜ ⊓ b ⊔ (a ⊔ b ⊔ c)ᶜ ⊓ c) = z ⊔ (z ⊔ z) :=
        by rw [H₁, I₁, J₁]
      _ = z := by repeat rw [ident₁]

-- We don't try to dualize the proof here, that's too painful, we apply de Morgan liberally
@[simp]
lemma assoc₂ (a b c : α) : a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c := by
  apply inv_elim
  simp

instance ShefferLE : LE α := ⟨ λ a b ↦ a = b ⊓ a ⟩

lemma Sheffer.le_refl (a : α) : a ≤ a := by simp [ShefferLE]

lemma Sheffer.le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
  rw [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a       := h₁
    _ = (c ⊓ b) ⊓ a := by conv => lhs; rw [h₂]
    _ = c ⊓ (b ⊓ a) := Eq.symm (assoc₂ c b a)
    _ = c ⊓ a       := by rw [← h₁]

lemma Sheffer.le_antisymm (a b : α) : a ≤ b → b ≤ a → a = b := by
  simp [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a := h₁
    _ = a ⊓ b := commut₂ ..
    _ = b     := id (Eq.symm h₂)


instance ShefferToBooleanAlg : BooleanAlgebra α where
  sup := (. ⊔ .)
  le_refl := fun a ↦ Sheffer.le_refl a
  le_trans := fun a b c a_1 a_2 ↦ Sheffer.le_trans a b c a_1 a_2
  le_antisymm := Sheffer.le_antisymm
  le_sup_left := by
    intro a b
    simp only [ShefferLE, Sup.sup]
    rw [commut₂]
    exact Eq.symm (absorb₂ a b)
  le_sup_right := by
    intro a b
    simp only [ShefferLE]
    rw [commut₂, commut₁]
    exact Eq.symm (absorb₂ b a)
  sup_le := by
    intro a b c
    simp only [ShefferLE]
    intro h₁ h₂
    calc
      a ⊔ b = (c ⊓ a) ⊔ b       := by conv => left; left; rw [h₁]
      _     = (c ⊓ a) ⊔ (c ⊓ b) := by conv => left; right; rw [h₂]
      _     = c ⊓ (a ⊔ b)       := Eq.symm (distrib₂ ..)
  inf := (. ⊓ .)
  inf_le_left := by
    intro a b; simp [ShefferLE]
  inf_le_right := by
    intro a b; simp only [ShefferLE]
    calc
      a ⊓ b = a ⊓ (b ⊓ b) := by rw [idemp₂]
      _     = a ⊓ b ⊓ b   := assoc₂ a b b
      _     = b ⊓ a ⊓ b   := by conv => left; left; rw [commut₂]
      _     = b ⊓ (a ⊓ b) := Eq.symm (assoc₂ ..)
  le_inf := by
    intro a b c h₁ h₂
    simp only [ShefferLE]
    calc
      a = b ⊓ a       := h₁
      _ = b ⊓ (c ⊓ a) := by conv => left; right; rw [h₂]
      _ = b ⊓ c ⊓ a  := by exact assoc₂ b c a
  le_sup_inf := by intro a b c; rw [distrib₁]; exact Sheffer.le_refl ..
  top := u
  bot := z
  inf_compl_le_bot := by intro a; simp only [compl₂]; exact Sheffer.le_refl ..
  top_le_sup_compl := by intro a; simp only [compl₁]; exact Sheffer.le_refl ..
  le_top := by intro a; simp only [ShefferLE]; rw [commut₂]; exact Eq.symm (ident₂ a)
  bot_le := by intro a; simp [ShefferLE]

end ShefferLaws

section BooleanToSheffer

variable {α : Type*}
variable [BooleanAlgebra α]

-- This is intentionally not an instance to avoid creating an instance cycle
-- Boolean Algebra -> Sheffer Algebra -> Boolean Algebra.
def BooleanAlgToSheffer : ShefferAlgebra α where
  stroke x y := (x ⊓ y)ᶜ
  elt := ⊥
  sh₁ := by intro a; simp [prime]
  sh₂ := by intro a b; simp [prime]
  sh₃ := by intro a b c; simp [prime]; rw [inf_sup_left]
            conv => left; left; rw [inf_comm]
            conv => left; right; rw [inf_comm]

end BooleanToSheffer
