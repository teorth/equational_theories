import equational_theories.BooleanAlternate
import equational_theories.Magma

section ShafferLaws

open BooleanRing


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
class Sheffer (α : Type*) extends Stroke α where
-- We need to assume α is nonempty
elt : α
sh₁ : ∀ a : α, a′′ = a
sh₂ : ∀ a b : α, a | (b | b′) = a′
sh₃ : ∀ a b c : α, (a | (b | c))′ = (b′ | a) | (c′ | a)

variable {α : Type*}

variable [Sheffer α]

open Sheffer

def z : α := elt | elt′

def u : α := z′

lemma commut (a b : α) : a | b = b | a :=
by
  calc
    a | b = (a | b)′′ := by rw [sh₁] -- exact Eq.symm (sh₁ _)
    _     = (a | (b′′))′′ := by rw [sh₁ b]
    _     = (b′′ | a)′′ := by conv => left; arg 1; arg 1; simp [prime]
                              conv => left; arg 1; rw [sh₃]
                              exact rfl
    _     = b | a := by repeat rw [sh₁]

lemma all_bot (a b : α) : a | a′ = b | b′ :=
by
  calc
    a | a′ = (a | a′)′′ := by rw [sh₁]
    _      = ((a | a′) | (b | b′))′ := by rw [sh₂]
    _      = ((b | b′) | (a | a′))′ := by rw [commut]
    _      = (b | b′)′′ := by rw [sh₂]
    _      = b | b′     := by rw [sh₁]

instance ShefferToBooleanRing : BooleanRing α where
mul := (.′ | .′)
add := λ a b ↦ (a | b)′
zero := z
one := u
compl := (.′)
commut₁ :=
by
  intros a b; simp [HAdd.hAdd]
  apply congr; trivial
  exact commut a b
commut₂ :=
by
  intros a b; simp [HMul.hMul]
  exact commut a ′ b ′
ident₁ :=
by
  intros a; simp [HAdd.hAdd, OfNat.ofNat]
  simp [z]; rw [sh₂]; exact sh₁ a
ident₂ :=
by
  intros a; simp [HMul.hMul, OfNat.ofNat, u, z]
  rw [sh₁, sh₂]; exact sh₁ a
distrib₁ :=
by
  intros a b c; simp [HAdd.hAdd, HMul.hMul]
  rw [sh₃]; repeat rw [sh₁]
  apply congr
  . apply congr; trivial
    exact commut b a
  . exact commut c a
distrib₂ :=
by
  intros a b c; simp [HAdd.hAdd, HMul.hMul]
  rw [sh₁]
  conv => left; exact Eq.symm (sh₁ _)
  rw [sh₃]
  apply congr; trivial; apply congr
  . apply congr; trivial
    exact commut b ′ a ′
  . exact commut c ′ a ′
compl₁ :=
by
  intros a; simp [HAdd.hAdd, OfNat.ofNat, u, z]
  apply congr; trivial
  exact all_bot a elt
compl₂ :=
by
  intros a; simp [HMul.hMul, OfNat.ofNat, u, z]
  rw [sh₁, commut]
  exact all_bot a elt

end ShafferLaws
