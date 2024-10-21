import equational_theories.BooleanRing
import equational_theories.Magma

section ShafferLaws

open BooleanRing

variable {α : Type*}
variable [Magma α]

def prime (a : α) := a ◇ a


-- Taking notations from https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf and
-- the original Sheffer paper, "A set of five independent postulates for Boolean algebras,
-- with application to logical constants"
postfix:max " ′ " => prime

-- These three laws axiomatize the Sheffer stroke, or NAND, entirely.
-- The remainder of this file is dedicated to that proof.
variable (sh₁ : ∀ a : α, a′′ = a)
variable (sh₂ : ∀ a b : α, a ◇ (b ◇ b′) = a′)
variable (sh₃ : ∀ a b c : α, (a ◇ (b ◇ c))′ = (b′ ◇ a) ◇ (c′ ◇ a))

-- We need to assume α is nonempty
variable (e : α)

include sh₁ sh₂ sh₃

def z : α := e ◇ e′

def u : α := (z e)′

@[simp]
def sheffer₁ : ∀ a : α, a′′ = a := sh₁

def sheffer₂ : ∀ a b : α, a ◇ (b ◇ b′) = a′ := sh₂

def sheffer₃ : ∀ a b c : α, (a ◇ (b ◇ c))′ = (b′ ◇ a) ◇ (c′ ◇ a) := sh₃

omit sh₂ in
lemma commut (a b : α) : a ◇ b = b ◇ a :=
by
  calc
    a ◇ b = (a ◇ b)′′ := by rw [sh₁] -- exact Eq.symm (sh₁ _)
    _     = (a ◇ (b′′))′′ := by rw [sh₁ b]
    _     = (b′′ ◇ a)′′ := by simp [prime] at * ; rw [sh₃ a (b◇b) (b◇b)]
    _     = b ◇ a := by repeat rw [sh₁]

lemma all_bot (a b : α) : a ◇ a′ = b ◇ b′ :=
by
  calc
    a ◇ a′ = (a ◇ a′)′′ := by rw [sh₁]
    _      = ((a ◇ a′) ◇ (b ◇ b′))′ := by rw [sh₂]
    _      = ((b ◇ b′) ◇ (a ◇ a′))′ := by rw [commut sh₁ sh₃]
    _      = (b ◇ b′)′′ := by rw [sh₂]
    _      = b ◇ b′     := by rw [sh₁]

instance ShefferIsBool : BooleanRing α where
mul := (.′ ◇ .′)
add := λ a b ↦ (a ◇ b)′
zero := z e
one := u e
compl := (.′)
commut₁ :=
by
  intros a b; simp [HAdd.hAdd]
  apply congr; trivial
  exact @commut _ _ sh₁ sh₃ a b
commut₂ :=
by
  intros a b; simp [HMul.hMul]
  exact @commut _ _ sh₁ sh₃ a ′ b ′
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
    exact commut sh₁ sh₃ b a
  . exact commut sh₁ sh₃ c a
distrib₂ :=
by
  intros a b c; simp [HAdd.hAdd, HMul.hMul]
  rw [sh₁]
  conv => left; exact Eq.symm (sh₁ _)
  rw [sh₃]
  apply congr; trivial; apply congr
  . apply congr; trivial
    exact commut sh₁ sh₃ b ′ a ′
  . exact commut sh₁ sh₃ c ′ a ′
compl₁ :=
by
  intros a; simp [HAdd.hAdd, OfNat.ofNat, u, z]
  apply congr; trivial
  exact all_bot sh₁ sh₂ sh₃ a e
compl₂ :=
by
  intros a; simp [HMul.hMul, OfNat.ofNat, u, z]
  rw [sh₁, commut sh₁ sh₃]
  exact all_bot sh₁ sh₂ sh₃ a e

end ShafferLaws
