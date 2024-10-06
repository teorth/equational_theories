import equational_theories.MagmaLaw

open Law

/-! Zero variables -/

@[simp] theorem Fin0.match_eq (X : Sort _) (f : Fin 0 → X) : Fin.elim0 = f := by
  funext i
  cases i
  contradiction

theorem Fin0.uncurry {X : Type _} (P : (Fin 0 → X) → Prop) : (∀ f : Fin 0 → X, P f) ↔
      P Fin.elim0 := by
  constructor
  · intro h
    apply h
  · intro h f
    simpa only [← match_eq]

theorem models_iff_0 (law : MagmaLaw (Fin 0)) (G  : Type _) [Magma G] : G ⊧ law ↔
    satisfiesPhi (Fin.elim0 (α := G)) law := by
  rw [satisfies, Fin0.uncurry]

/-! One variable -/

@[simp] theorem Fin1.match_eq (X : Sort _) (f : Fin 1 → X) : (fun | 0 => f 0) = f := by
  funext i
  match i with
  | 0 => rfl

theorem Fin1.uncurry {X : Type _} (P : (Fin 1 → X) → Prop) : (∀ f : Fin 1 → X, P f) ↔
      ∀ x : X, P (fun | 0 => x) := by
  constructor
  · intro h _
    apply h
  · intro h f
    have := h (f 0)
    simpa only [match_eq]

theorem models_iff_1 (law : MagmaLaw (Fin 1)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x : G, satisfiesPhi (fun | 0 => x) law := by
  rw [satisfies, Fin1.uncurry]

/-! Two variables -/

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

theorem models_iff_2 (law : MagmaLaw (Fin 2)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x y : G, satisfiesPhi (fun | 0 => x | 1 => y) law := by
  rw [satisfies, Fin2.uncurry]

/-! Three variables -/

@[simp] theorem Fin3.match_eq (X : Sort _) (f : Fin 3 → X) : (fun | 0 => f 0 | 1 => f 1 | 2 => f 2) = f := by
  funext i
  match i with
  | 0 | 1 | 2 => rfl

theorem Fin3.uncurry {X : Type _} (P : (Fin 3 → X) → Prop) : (∀ f : Fin 3 → X, P f) ↔
    ∀ x y z : X, P (fun | 0 => x | 1 => y | 2 => z) := by
  constructor
  · intro h _ _ _
    apply h
  · intro h f
    have := h (f 0) (f 1) (f 2)
    simpa only [match_eq]

theorem models_iff_3 (law : MagmaLaw (Fin 3)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x y z : G, satisfiesPhi (fun | 0 => x | 1 => y | 2 => z) law := by
  rw [satisfies, Fin3.uncurry]

/-! Four variables -/

@[simp] theorem Fin4.match_eq (X : Sort _) (f : Fin 4 → X) : (fun | 0 => f 0 | 1 => f 1 | 2 => f 2 | 3 => f 3) = f := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 => rfl

theorem Fin4.uncurry {X : Type _} (P : (Fin 4 → X) → Prop) : (∀ f : Fin 4 → X, P f) ↔
    ∀ x y z w : X, P (fun | 0 => x | 1 => y | 2 => z | 3 => w) := by
  constructor
  · intro h _ _ _ _
    apply h
  · intro h f
    have := h (f 0) (f 1) (f 2) (f 3)
    simpa only [match_eq]

theorem models_iff_4 (law : MagmaLaw (Fin 4)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x y z w : G, satisfiesPhi (fun | 0 => x | 1 => y | 2 => z | 3 => w) law := by
  rw [satisfies, Fin4.uncurry]

/-! Five variables -/

@[simp] theorem Fin5.match_eq (X : Sort _) (f : Fin 5 → X) : (fun | 0 => f 0 | 1 => f 1 | 2 => f 2 | 3 => f 3 | 4 => f 4) = f := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl

theorem Fin5.uncurry {X : Type _} (P : (Fin 5 → X) → Prop) : (∀ f : Fin 5 → X, P f) ↔
    ∀ x y z w v : X, P (fun | 0 => x | 1 => y | 2 => z | 3 => w | 4 => v) := by
  constructor
  · intro h _ _ _ _ _
    apply h
  · intro h f
    have := h (f 0) (f 1) (f 2) (f 3) (f 4)
    simpa only [match_eq]

theorem models_iff_5 (law : MagmaLaw (Fin 5)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x y z w v : G, satisfiesPhi (fun | 0 => x | 1 => y | 2 => z | 3 => w | 4 => v) law := by
  rw [satisfies, Fin5.uncurry]

/-! Six variables -/

@[simp] theorem Fin6.match_eq (X : Sort _) (f : Fin 6 → X) : (fun | 0 => f 0 | 1 => f 1 | 2 => f 2 | 3 => f 3 | 4 => f 4 | 5 => f 5) = f := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl

theorem Fin6.uncurry {X : Type _} (P : (Fin 6 → X) → Prop) : (∀ f : Fin 6 → X, P f) ↔
    ∀ x y z w v u : X, P (fun | 0 => x | 1 => y | 2 => z | 3 => w | 4 => v | 5 => u) := by
  constructor
  · intro h _ _ _ _ _ _
    apply h
  · intro h f
    have := h (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
    simpa only [match_eq]

theorem models_iff_6 (law : MagmaLaw (Fin 6)) (G  : Type _) [Magma G] : G ⊧ law ↔
    ∀ x y z w v u : G, satisfiesPhi (fun | 0 => x | 1 => y | 2 => z | 3 => w | 4 => v | 5 => u) law := by
  rw [satisfies, Fin6.uncurry]
