import equational_theories.Magma
import equational_theories.Equations.All

/-!
Bernhard Reinke writes:

I think I have a sketch for an example of a magma satisfying 206 but not 1648. I use the translation
invariant approach, but for a non-commutative group: let $$ G $$ the free product of three cyclic
groups of order 2. If we have the alphabet $$ A = \{a,b,c\} $$ then we can identify $$ G $$ with the
reduced words in $$ A $$ that have no subwords of the form $$ aa, bb, cc $$.

Our magma will be defined on G and will satisfy
```math
x ◇ y = x f(x^{-1}y)
```
where $$ f \colon G \rightarrow \{1, a, b, c\} $$.

Then the RHS of 206 is
```math
(x ◇ (x ◇ y)) ◇ y = (x ◇ (x f(x^{-1}y)) ◇ y = (x f(f(x^{-1} y))) ◇ y = x  f(f(x^{-1} y)) f( (f(f(x^{-1} y))^{-1} x^{-1} y)
```
Setting $$ z = x^{-1} y $$, we get that 206 is equivalent to
$$ f(f(z)) f ( f(f(z))^{-1} z) = 1 $$. Under the assumption that $$f$$ maps to $$\{1, a, b, c\}$$
(so $$ f(z) = f(z)^{-1} $$), this simplifies to
```math
f(f(z)) = f( f(f(z)) z)
```
 I claim the following f satisfies this: we set
```math
f(1) = 1, f(a) = b, f(b) = c, f(c) = a
```
now, if $$w$$ is a nonempty reduced word not starting in $$a$$, we set $$ f(aw) = a $$, cyclically
symmetric for reduced words starting in b and and c. Let us check that this satisfies $$f(f(z)) = f(
f(f(z)) z)$$:

It is clear that $$ f(f(1)) = f( f(f(1)) 1) = 1 $$.

We have $$ f(f(a)) = f(b) = c$$, and $$f(f(f(a))a) = f(ca) = c$$.

For $$w$$ is a nonempty reduced word not starting in $$a$$, we have
$$ f(f(aw)) = f(a) = b, so f( f(f(aw)) aw) = f(baw) = b$$. The rest follows by symmetry.

I think 1648 translates to
$$ f(z)f(f((f(z))^{-1} z)) = 1 $$
this is not satisfied, as $$ f(a) f(f( (f(a))^{-1} a) = b f(f(ba)) = b f(b) = bc \not= 1 $$.

I hope I haven't made any computational mistakes (this is in fact my second try, :sweat_smile: ),
would someone like to check whether this makes sense? I don't think I would be able to formalize
this in Lean myself.

-/

namespace Planar3RegTree

/-- Free words over three generators -/
abbrev W := List (Fin 3)

/-- List reversal is going to be our inverse, so let's introduce convenient notation. -/
local notation x "⁻¹" => List.reverse x

/-- Reduced words do not have the same element adjacent to each other -/
def IsRed (w : W) : Prop := ∀ i, (h : i + 1 < w.length) → w[i] ≠ w[i+1]

@[simp]
theorem IsRed_nil : IsRed [] := by simp [IsRed]

@[simp]
theorem IsRed_singleton x : IsRed [x] := by simp [IsRed]

theorem IsRed_reverse (w : W) : IsRed (w ⁻¹) → IsRed w := by
  intro h i hi
  symm
  specialize h (w.length - (i+2)) (by simp; omega)
  simp only [List.getElem_reverse, ne_eq] at h
  show ¬_
  convert h using 3 <;> omega

@[simp]
theorem IsRed_reverse_iff (w : W) : IsRed (w ⁻¹) ↔ IsRed w := by
  constructor
  · intro h; apply IsRed_reverse; apply h
  · intro h; apply IsRed_reverse; rw [List.reverse_reverse]; apply h

theorem IsRed_uncons {x} {ys} (h : IsRed (x :: ys)) : IsRed ys := by
    intro i hi
    specialize h (i+1) (by simp; omega)
    simpa

theorem IsRed_cons {y} {x} {ys} (hne : y ≠ x) (h : IsRed (x :: ys)) : IsRed (y :: x :: ys) := by
  intro i hi
  match i with
  | 0 => simpa
  | i+1 =>
    specialize h i (by simpa [List.length_append] using hi)
    simpa

lemma IsRed_not_repeated {ys} {x} {xs} : ¬ IsRed (ys ++ x :: x :: xs) := by
  intro h
  specialize h ys.length (by simp)
  rw [List.getElem_append_right] at h
  rotate_left; · simp
  rw [List.getElem_append_right] at h
  rotate_left; · simp
  simp at h

/-!
The reduction function, nicely concrete and executabe (for `by decide` later) and somewhat
efficient (not that that matters).
-/
def red (w : W) : W := go [] w
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
theorem red_IsRed (w : W) : IsRed (red w) :=
  go [] w (by simp)
where
  go (ys xs : W) (h : IsRed ys) : IsRed (red.go ys xs) := by
    induction ys, xs using red.go.induct
    next => simpa [red.go]
    next ih => apply ih; simp
    next ih => simpa [red.go] using ih (IsRed_uncons h)
    next hne ih => simpa [red.go, hne] using ih (IsRed_cons hne h)

theorem red_length_le (w : W) : (red w).length ≤ w.length := by
  simpa using go [] w
where
  go (w v) : (red.go w v).length ≤ w.length + v.length := by
    induction w, v using red.go.induct <;> simp_all [red.go] <;> omega

theorem red.go_length_le (ys xs : W) :
    ys.length ≤ (red.go ys xs).length + xs.length := by
  induction ys, xs using red.go.induct <;> simp_all [red.go] <;> omega

@[simp]
theorem red_eq_of_IsRed {w : W} (h : IsRed w) : red w = w :=
  go [] w h
where
  go ys xs (h : IsRed (ys⁻¹ ++ xs)) : red.go ys xs = ys ⁻¹ ++ xs := by
    induction ys, xs using red.go.induct
    next => simp [red.go, h]
    next ih =>
      apply ih
      simpa
    next ih =>
      exfalso; clear ih -- cannot happen
      apply IsRed_not_repeated
      simpa [List.reverse_cons, List.append_assoc, List.singleton_append] using h
    next ih =>
      simp [red.go, *]
      simp [red.go, *] at ih
      apply ih
      simpa using h

@[simp]
theorem red_red (w : W) : red (red w) = red w := red_eq_of_IsRed (red_IsRed _)

/-- We can reduce anywhere in a term. This is essentially a proof of confluence -/
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
    next ih => exact ih (IsRed_singleton _)
    next ih =>
      simp only [red.go, ↓reduceIte, List.append_eq]
      exact ih (IsRed_uncons h)
    next hne ih =>
      simp [red.go, *]
      simp [red.go, *] at ih
      exact ih (IsRed_cons hne h)

@[simp]
theorem rev_red (w : W) : (red w)⁻¹ = red (w⁻¹) := by
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
theorem red_append_red (w v : W) : red (w ++ red v) = red (w ++ v) := by
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
theorem red_append_red' (w v : W) : red (red w ++ v) = red (w ++ v) := by
  apply List.reverse_injective; simp

@[simp]
theorem red_append_inv (w v : W) : red (w⁻¹ ++ (w ++ v)) = red v := by
  induction w <;> simp [red_reduce, *]

@[simp]
theorem red_rev_self (w : W) : red (w⁻¹ ++ w) = [] := by
  simpa using red_append_inv w []

theorem red_append_nil_iff_of_IsRed (w v : W) (hw : IsRed w) (hv : IsRed v) :
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
theorem red_append_nil_iff (w v : W) :
    red (w ++ v) = [] ↔ red w = red v⁻¹ := by
  rw [← red_append_red, ← red_append_red']
  apply red_append_nil_iff_of_IsRed
  exact red_IsRed w
  exact red_IsRed v

theorem red_append_nil_iff' (w v : W) :
  red (w⁻¹ ++ v) = [] ↔ red w = red v := by simp [← rev_red, red_append_nil_iff]

@[simp]
theorem red_append_inj (w v : W) (h : IsRed w):
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

def f : W → W
  | [] => []
  | [x] => [x+1]
  | x::_::_ => [x]

attribute [simp] f.eq_1 f.eq_2

@[simp]
theorem red_f (w : W) : red (f w) = f w := by
  unfold f; split <;> simp

@[simp]
theorem rev_f (w : W) : (f w)⁻¹ = f w := by
  unfold f; split <;> simp

theorem ff_fff (z : W) (h : IsRed z) : f (f z) = f (red (f (f z) ++ z)) := by
  match z with
  | [] => simp
  | [x] => simp [f]
  | x::y::zs =>
    have : IsRed ((x + 1) :: x :: y :: zs) := IsRed_cons (by simp; omega) h
    simp [f.eq_3, this]

abbrev M := {x : W // IsRed x}

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
