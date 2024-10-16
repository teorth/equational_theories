import equational_theories.Magma
import equational_theories.Equations.All

namespace Planar3RegTree

abbrev F := List (Fin 3)

local notation x "⁻¹" => List.reverse x

def IsRed (w : F) : Prop := ∀ i, (h : i + 1 < w.length) → w[i] ≠ w[i+1]

@[simp]
theorem IsRed_nil : IsRed [] := by simp [IsRed]

@[simp]
theorem IsRed_singleton x : IsRed [x] := by simp [IsRed]

theorem IsRed_reverse (w : F) : IsRed (w ⁻¹) → IsRed w := by
  intro h i hi
  specialize h (w.length - (i+2)) (by simp; omega)
  simp at h
  symm
  show ¬_
  convert h using 3 <;> omega

@[simp]
theorem IsRed_reverse_iff (w : F) : IsRed (w ⁻¹) ↔ IsRed w := by
  constructor
  · intro h; apply IsRed_reverse; apply h
  · intro h; apply IsRed_reverse; rw [List.reverse_reverse]; apply h

theorem IsRed_uncons {x} {ys} (h : IsRed (x :: ys)) : IsRed ys := by
    intro i hi
    specialize h (i+1) (by simp; omega)
    simpa

theorem IsRed_cons {y} {x} {ys} (hne : y ≠ x) (h : IsRed (x :: ys)) : IsRed (y :: x :: ys) := by
  intro i hi
  simp [List.length_append] at hi
  match i with
  | 0 => simpa
  | i+1 =>
    specialize h i (by simp [hi])
    simpa

lemma IsRed_not_repeated {ys} {x} {xs} : ¬ IsRed (ys ++ x :: x :: xs) := by
  intro h
  specialize h ys.length (by simp)
  rw [List.getElem_append_right] at h
  rotate_left; simp
  rw [List.getElem_append_right] at h
  rotate_left; simp
  simp at h

def red (w : F) : F := go [] w
where
  go | ys, [] => ys.reverse
     | [], x::xs => go [x] xs
     | y::ys, x::xs => if x = y then go ys xs else go (x::y::ys) xs

@[simp] theorem red_nil : red [] = [] := rfl
@[simp] theorem red_singleton (x : Fin 3) : red [x] = [x] := rfl

@[simp]
theorem red_duoton_succ (x : Fin 3) : red [x, x+1] = [x, x+1] := by
  simp! [red]; omega

@[simp]
theorem red_duoton_succ_succ (x : Fin 3) : red [x + 1 + 1, x] = [x+1+1, x] := by
  simp! [red]; omega

@[simp]
theorem red_IsRed (w : F) : IsRed (red w) :=
  go [] w (by simp)
where
  go (ys xs : F) (h : IsRed ys) : IsRed (red.go ys xs) := by
    induction ys, xs using red.go.induct
    next => simpa [red.go]
    next ih => apply ih; simp
    next ih =>
      simp [red.go]
      apply ih
      apply IsRed_uncons
      apply h
    next hne ih =>
      simp [red.go, hne]
      apply ih
      apply IsRed_cons hne h

theorem red_length_le (w : F) : (red w).length ≤ w.length := by
  simpa using go [] w
where
  go (w v) : (red.go w v).length ≤ w.length + v.length := by
    induction w, v using red.go.induct <;>
      (simp_all [red.go] <;> omega)

theorem red.go_length_le (ys xs : F) :
    ys.length ≤ (red.go ys xs).length + xs.length := by
  induction ys, xs using red.go.induct <;>
    (simp_all [red.go] <;> omega)

@[simp]
theorem red_eq_of_IsRed {w : F} (h : IsRed w) : red w = w :=
  go [] w h
where
  go ys xs (h : IsRed (ys⁻¹ ++ xs)) : red.go ys xs = ys ⁻¹ ++ xs := by
    induction ys, xs using red.go.induct
    next => simp [red.go, h]
    next ih =>
      apply ih
      simpa
    next ih =>
      exfalso; clear ih
      simp at h
      apply IsRed_not_repeated h
    next ih =>
      simp [red.go, *]
      simp [red.go, *] at ih
      apply ih
      simpa using h

@[simp]
theorem red_red (w : F) : red (red w) = red w := red_eq_of_IsRed (red_IsRed _)

theorem red_reduce {ys} {x} {xs} : red (ys ++ x :: x :: xs) = red (ys ++ xs) :=
  go [] ys (by simp)
where
  go zs ys (h : IsRed zs) : red.go zs (ys ++ x :: x :: xs) = red.go zs (ys ++ xs) := by
    induction zs, ys using red.go.induct
    next ys =>
      cases ys
      next => simp [red.go]
      next y ys =>
        simp [red.go]
        intro hx
        subst y
        cases ys
        · simp [red.go]
        · simp [red.go]
          intro hx
          subst hx
          exfalso
          apply IsRed_not_repeated (ys := []) h
    next ih =>
      apply ih
      simp
    next ih =>
      simp [red.go]
      apply ih
      apply IsRed_uncons
      assumption
    next hne ih =>
      simp [red.go, *]
      simp [red.go, *] at ih
      apply ih
      apply IsRed_cons hne h

@[simp]
theorem rev_red (w : F) : (red w)⁻¹ = red (w⁻¹) := by
  simpa [red] using go [] w (by simp)
where
  go ys xs (h : IsRed ys) : (red.go ys xs)⁻¹ = red (xs⁻¹ ++ ys) := by
    induction ys, xs using red.go.induct
    next ys => simp [red.go, red_eq_of_IsRed, h]
    next x xs ih =>
      simp [red.go]
      apply ih
      simp
    next ys x xs ih =>
      simp [red.go]
      rw [ih]
      rotate_left; apply IsRed_uncons h
      rw [red_reduce]
    next ys y x xs hne ih =>
      simp [red.go, hne]
      apply ih
      apply IsRed_cons hne h

@[simp]
theorem red_append_red (w v : F) : red (w ++ red v) = red (w ++ v) := by
  simpa [red] using go [] v
where
  go ys xs : red (w ++ red.go ys xs) = red (w ++ (ys⁻¹) ++ xs) := by
    induction ys, xs using red.go.induct
    next ys => simp [red.go]
    next x xs ih =>
      simp [red.go]
      simp at ih
      apply ih
    next ys x xs ih =>
      simp [red.go]
      rw [ih]; clear ih
      symm
      simpa [List.append_assoc] using @red_reduce (w ++ (ys⁻¹)) x xs
    next ys y x xs hne ih =>
      simp [red.go, hne]
      simp at ih
      apply ih

@[simp]
theorem red_append_red' (w v : F) : red (red w ++ v) = red (w ++ v) := by
  apply List.reverse_injective; simp

@[simp]
theorem red_append_inv (w v : F) : red (w⁻¹ ++ (w ++ v)) = red v := by
  induction w <;> simp [red_reduce, *]

@[simp]
theorem red_rev_self (w : F) : red (w⁻¹ ++ w) = [] := by
  simpa using red_append_inv w []

theorem red_append_nil_iff_of_IsRed (w v : F) (hw : IsRed w) (hv : IsRed v) :
    red (w ++ v) = [] ↔ w = v⁻¹ := by
  constructor
  · exact go [] w hw
  · intro h
    simp [h]
where
  go ys xs (hxs : IsRed (ys⁻¹ ++ xs)) : red.go ys (xs ++ v) = [] → (ys⁻¹ ++ xs) = v⁻¹ := by
    induction ys, xs using red.go.induct
    next ys =>
      simp
      apply go2 ys v hv
    next x xs ih =>
      apply ih
      simpa using hxs
    next ys x xs _ =>
      exfalso
      simp at hxs
      apply IsRed_not_repeated hxs
    next ys y x xs hne ih =>
      simp [red.go, hne]
      simp at ih
      apply ih
      simpa using hxs
  go2 ys xs  (hxs : IsRed xs) : red.go ys xs = [] → ys = xs := by
    intro h
    induction ys, xs using red.go.induct
    next ys => simpa [red.go] using h
    next x xs _ =>
      exfalso
      simp only [red.go] at h
      change red (x :: xs) = [] at h
      rw [red_eq_of_IsRed hxs] at h
      contradiction
    next ys x xs ih =>
      simp
      simp [red.go] at h
      apply ih (IsRed_uncons hxs) h
    next y ys x xs hne ih =>
      exfalso
      simp [red.go, hne] at h
      specialize ih  (IsRed_uncons hxs) h
      subst ih
      have := @IsRed_not_repeated [] x (y :: ys)
      contradiction



-- @[simp]
theorem red_append_nil_iff (w v : F) :
    red (w ++ v) = [] ↔ red w = red v⁻¹ := by
  rw [← red_append_red, ← red_append_red']
  apply red_append_nil_iff_of_IsRed
  exact red_IsRed w
  exact red_IsRed v

theorem red_append_nil_iff' (w v : F) :
  red (w⁻¹ ++ v) = [] ↔ red w = red v := by simp [← rev_red, red_append_nil_iff]

@[simp]
theorem red_append_inj (w v : F) (h : IsRed w):
    w = red (w ++ v) ↔ red v = [] := by
  constructor
  · intro heq
    rw [← red_eq_of_IsRed h] at heq
    rw [red_append_red'] at heq
    symm at heq
    rw [← red_append_nil_iff'] at heq
    rw [List.reverse_append] at heq
    induction w
    case nil => simpa [← rev_red] using heq
    case cons x xs ih =>
      apply ih (IsRed_uncons h)
      simp at heq
      have := @red_reduce ((xs ++ v)⁻¹) x xs
      simp_all
  · intro heq
    rw [← red_append_red, heq, List.append_nil]
    simp [h]


attribute [simp] List.reverse_append

def f : F → F
  | [] => []
  | [x] => [x+1]
  | x::_::_ => [x]

attribute [simp] f.eq_1 f.eq_2

@[simp]
theorem red_f (w : F) : red (f w) = f w := by
  unfold f; split <;> simp

@[simp]
theorem rev_f (w : F) : (f w)⁻¹ = f w := by
  unfold f; split <;> simp

theorem ff_fff (z : F) (h : IsRed z) : f (f z) = f (red (f (f z) ++ z)) := by
  match z with
  | [] => simp
  | [x] => simp [f]
  | x::y::zs =>
    have : IsRed ((x + 1) :: x :: y :: zs) := IsRed_cons (by simp; omega) h
    simp [f.eq_3, this]

abbrev M := {x : F // IsRed x}

instance inst : Magma M where
  op := fun ⟨x, _hx⟩ ⟨y, _hy⟩ =>
    ⟨red (x ++ f (red (x.reverse ++ y))), red_IsRed _⟩

theorem M.Satisfies206 : Equation206 M := by
  unfold Equation206
  intro ⟨w, hw⟩ ⟨v, hv⟩
  simpa [Magma.op, hw, hv, red_append_nil_iff] using
    ff_fff (red (w⁻¹ ++ v)) (red_IsRed _)

theorem M.Refutes1684 : ¬ Equation1684 M := by
  unfold Equation1684
  push_neg
  use ⟨[1], by simp⟩, ⟨[2], by simp⟩
  decide
