import equational_theories.MagmaLaw

open Law

def FreeMagma.evalBounded {G} [Magma G] (ls : List G) :
    (m : FreeMagma Nat) → (∀ a, m.Mem a → a < ls.length) → G
  | a ⋆ b, h => a.evalBounded ls (h · ∘ .inl) ◇ b.evalBounded ls (h · ∘ .inr)
  | Lf a, h => ls.get ⟨a, h _ rfl⟩

def Law.MagmaLaw.evalBounded {G} [Magma G] (ls : List G) :
    (m : NatMagmaLaw) → (∀ a, m.Mem a → a < ls.length) → Prop
  | ⟨a, b⟩, h => a.evalBounded ls (h · ∘ .inl) = b.evalBounded ls (h · ∘ .inr)

def FreeMagma.bounded (n : Nat) : FreeMagma Nat → Bool
  | a ⋆ b => a.bounded n && b.bounded n
  | Lf a => a < n

def Law.MagmaLaw.bounded (n : Nat) : NatMagmaLaw → Bool
  | ⟨a, b⟩ => a.bounded n && b.bounded n

theorem FreeMagma.bounded_iff {n} {m : FreeMagma Nat} : m.bounded n ↔ ∀ a, m.Mem a → a < n := by
  induction m <;> simp [bounded, Mem, or_imp, forall_and, *]

theorem Law.MagmaLaw.bounded_iff {n} {m : NatMagmaLaw} : m.bounded n ↔ ∀ a, m.Mem a → a < n := by
  cases m; simp [bounded, Mem, or_imp, forall_and, FreeMagma.bounded_iff]

def ModelsIffType (G : Type*) [Magma G] (law : NatMagmaLaw) :
    (n : Nat) → (ls : List G) → law.bounded (n + ls.length) → Prop
  | 0, xs, h => law.evalBounded xs.reverse (by simpa using Law.MagmaLaw.bounded_iff.1 h)
  | n+1, xs, h => ∀ x, ModelsIffType G law n (x::xs) (by rwa [Nat.succ_add] at h)

theorem models_iff_n (law : NatMagmaLaw) (n) (h : law.bounded n) (G : Type _) [Magma G] :
    G ⊧ law ↔ ModelsIffType G law n [] h := by
  suffices ∀ n k (h : law.bounded (n + k)),
      G ⊧ law ↔ ∀ xs (h' : xs.length = k), ModelsIffType G law n xs (h' ▸ h) by
    refine (this n 0 h).trans ?_
    exact ⟨fun H => H [] rfl, fun H xs h => by cases List.length_eq_zero_iff.1 h; assumption⟩
  intro n k h
  induction n generalizing k with
  | succ n ih =>
    refine (ih (k+1) (by rwa [Nat.succ_add] at h)).trans ?_
    simp only [ModelsIffType]
    exact ⟨fun H xs hxs x => H _ (hxs ▸ rfl), fun | H, x::xs, h => H xs (Nat.succ.inj h) x⟩
  | zero =>
    simp only [Nat.zero_add, Law.MagmaLaw.bounded_iff] at h
    rw [← satisfies_pmap_mk _ h, satisfies]
    let eqv : {xs : List G // xs.length = k} ≃ ({a // a < k} → G) := {
      toFun := fun ⟨xs, hx⟩ ⟨i, hi⟩ => xs[i]'(hx ▸ hi)
      invFun := fun f => ⟨List.ofFn fun i => f ⟨i.1, i.2⟩, by simp⟩
      left_inv := fun ⟨_, _⟩ => by subst k; simp
      right_inv := fun _ => by simp
    }
    let rev : {xs : List G // xs.length = k} ≃ {xs : List G // xs.length = k} := {
      toFun := fun ⟨xs, hx⟩ => ⟨xs.reverse, by simp [hx]⟩
      invFun := fun ⟨xs, hx⟩ => ⟨xs.reverse, by simp [hx]⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    }
    simp only [← eqv.forall_congr_right, Equiv.coe_fn_mk, eqv,  ModelsIffType]
    refine Iff.trans (forall_congr' fun ⟨xs, hx⟩ => ?_)
      ((rev.forall_congr_right
        (q := fun xs => law.evalBounded xs.1 (by simpa [xs.2] using h))).symm.trans Subtype.forall)
    clear eqv rev; subst k
    have (m : FreeMagma Nat) (h) : m.evalBounded xs h =
        (m.pmap fun a h' ↦ ⟨a, h a h'⟩) ⬝ (fun x : {a//a<xs.length} ↦ xs.get ⟨x.1, x.2⟩) := by
      induction m <;> simp [FreeMagma.pmap, FreeMagma.evalInMagma, FreeMagma.evalBounded, *]
    simp [satisfiesPhi, MagmaLaw.pmap, MagmaLaw.evalBounded, this]
