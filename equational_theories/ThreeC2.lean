import equational_theories.Magma
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.EquationalResult

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

/-!

### Implementation notes

This contians a self-contained development of the free product of three copies of the two-element
group, by defining reduced words, a reduction function, and deriving enough API for it. In the
end we define our magma of interest directly, so this free product group is not explicitly defined.

The development can easily be generalized to more than three copies if needed, just swap out `Fin 3`.

-/

namespace ThreeC2

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
  -- A zipper processing helper function.
  go : (ys xs : W) → W
     | ys, []       => ys.reverse
     | [],    x::xs => go [x] xs
     | y::ys, x::xs =>
      if x = y then
        go ys xs
      else
        go (x::y::ys) xs

  -- Neat trick: We define a copy of that function that passes through the `IsRed` assumption.
  -- We do not use this function, but we can use its induction principle to do proofs about
  -- `red.go` without having to thread through this assumption manually, if we need that.
  go_aux : (ys xs : W) → (h : IsRed ys) → W
     | ys, [], _       => ys.reverse
     | [],    x::xs, _ => go_aux [x] xs (IsRed_singleton _)
     | y::ys, x::xs, h =>
      if heq : x = y then
        go_aux ys xs (IsRed_uncons h)
      else
        go_aux (x::y::ys) xs (IsRed_cons heq h)

def red.go_induct := @red.go_aux.induct

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
  go [] w IsRed_nil
where
  go (ys xs : W) (h : IsRed ys) : IsRed (red.go ys xs) := by
    induction ys, xs, h using red.go_induct
    next => simp [red.go, *]
    next ih => apply ih
    next ih => simpa [red.go] using ih
    next hne _ ih => simpa [red.go, hne] using ih

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
  go ys xs  (h : IsRed (ys⁻¹ ++ xs)) : red.go ys xs = ys ⁻¹ ++ xs := by
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
  go [] ys IsRed_nil
where
  go zs ys (h : IsRed zs) : red.go zs (ys ++ x :: x :: xs) = red.go zs (ys ++ xs) := by
    induction zs, ys, h using red.go_induct
    next ys _ _ =>
      cases ys
      next => simp [red.go]
      next y ys h _  =>
        simp [red.go, *]
        intro he
        subst he
        cases ys
        · simp [red.go]
        · simp [red.go]
          intro he
          subst he
          exfalso
          apply IsRed_not_repeated (ys := []) h
    next ih => exact ih
    next => simp [red.go, *]
    next => simp [red.go, *]

@[simp]
theorem rev_red (w : W) : (red w)⁻¹ = red (w⁻¹) := by
  simpa [red] using go [] w (by simp)
where
  go ys xs (h : IsRed ys) : (red.go ys xs)⁻¹ = red (xs⁻¹ ++ ys) := by
    induction ys, xs, h using red.go_induct
      <;> simp [red.go, red_eq_of_IsRed, red_reduce, *]

@[simp]
theorem red_append_red_right (w v : W) : red (w ++ red v) = red (w ++ v) := by
  simpa [red] using go [] v
where
  go ys xs : red (w ++ red.go ys xs) = red (w ++ (ys⁻¹) ++ xs) := by
    induction ys, xs using red.go.induct
    next ys => simp [red.go]
    next x xs ih => simpa [red.go] using ih
    next ys x xs ih =>
      simp [red.go]
      rw [ih]; clear ih
      symm
      simpa [List.append_assoc] using @red_reduce (w ++ (ys⁻¹)) x xs
    next ys y x xs hne ih => simpa [red.go, hne] using ih

@[simp]
theorem red_append_red_left (w v : W) : red (red w ++ v) = red (w ++ v) := by
  apply List.reverse_injective; simp

@[simp]
theorem red_append_inv (w v : W) : red (w⁻¹ ++ (w ++ v)) = red v := by
  induction w <;> simp [red_reduce, *]

@[simp]
theorem red_rev_self (w : W) : red (w⁻¹ ++ w) = [] := by
  simpa using red_append_inv w []

/--
The crucial step towards cancellation.
-/
theorem red_append_nil_iff_eq_inv (w v : W) (hw : IsRed w) (hv : IsRed v) :
    red (w ++ v) = [] ↔ w = v⁻¹ := by
  constructor
  · exact go [] w hw
  · intro h
    simp [h]
where
  -- This loop/induction moves `w` to the left argument of `red.go`. No reduction can happen.
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
      simp [IsRed_not_repeated] at hxs
    next ys y x xs hne ih =>
      simp [red.go, hne]
      simp at ih
      apply ih
      simpa using hxs
  -- This loop/induction now cancels the elements. Now the last case is impossible.
  go2 ys xs (hxs : IsRed xs) : red.go ys xs = [] → ys = xs := by
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
      rw [← ih (IsRed_uncons hxs) h] at hxs
      apply @IsRed_not_repeated [] x (y :: ys) hxs

theorem red_append_nil_iff (w v : W) :
    red (w ++ v) = [] ↔ red w = red v⁻¹ := by
  rw [← red_append_red_right, ← red_append_red_left]
  apply red_append_nil_iff_eq_inv
  exact red_IsRed w
  exact red_IsRed v

theorem red_eq_red_iff_red_append_nil (w v : W) :
  red w = red v ↔ red (w⁻¹ ++ v) = [] := by simp [← rev_red, red_append_nil_iff]

@[simp]
theorem red_append_inj (w v : W) (h : IsRed w):
    w = red (w ++ v) ↔ red v = [] := by
  rw [← red_eq_of_IsRed h]
  rw [red_append_red_left]
  rw [red_eq_red_iff_red_append_nil]
  rw [← List.append_assoc]
  rw [red_append_nil_iff]
  simp [-rev_red]

attribute [simp] List.reverse_append

/-- The `f` function that we use to define the monoid of interest -/
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

/-- The crucial relation of that function -/
theorem ff_fff (z : W) (h : IsRed z) : f (f z) = f (red (f (f z) ++ z)) := by
  match z with
  | [] => simp
  | [x] => simp [f]
  | x::y::zs =>
    have : IsRed ((x + 1) :: x :: y :: zs) := IsRed_cons (by simp; omega) h
    simp [f.eq_3, this]

/-- The carrier for our magma: reduced words -/
abbrev M := {x : W // IsRed x}

/-- The magma instance -/
instance inst : Magma M where
  op := fun ⟨x, _⟩ ⟨y, _⟩ =>
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

@[equational_result]
theorem Fact : ∃ (G : Type) (_ : Magma G), Facts G [206] [1684] :=
  ⟨_, _, M.Satisfies206, M.Refutes1684⟩


end ThreeC2
