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

This contains a self-contained development of the free product of three copies of the two-element
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
theorem IsRed_reverse_iff (w : W) : IsRed (w ⁻¹) ↔ IsRed w :=
  ⟨fun h ↦ IsRed_reverse _ h, fun h ↦ IsRed_reverse _ (by simp [h])⟩

theorem IsRed_uncons {x} {ys} (h : IsRed (x :: ys)) : IsRed ys :=
  fun _ hh ↦ h _ (Nat.add_lt_of_lt_sub hh)

theorem IsRed_cons {y} {x} {ys} (hne : y ≠ x) (h : IsRed (x :: ys)) : IsRed (y :: x :: ys) := by
  intro i hi
  match i with
  | 0 => exact hne
  | i+1 => exact h i (Nat.succ_lt_succ_iff.mp hi)

lemma IsRed_not_repeated {ys} {x} {xs} : ¬ IsRed (ys ++ x :: x :: xs) := by
  intro h
  specialize h ys.length (by simp)
  rw [List.getElem_append_right] at h
  rotate_left; · simp
  rw [List.getElem_append_right] at h
  rotate_left; · simp
  simp at h

/-!
The reduction function, nicely concrete and executable (for `by decide` later) and somewhat
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
    next ih => exact ih
    next ih => simpa [red.go] using ih
    next hne _ ih => simp_all [red.go]

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
    next ys _ =>
      cases ys
      next => simp [red.go]
      next y ys h =>
        simp [red.go, *]
        intro he
        subst he
        cases ys
        · simp [red.go]
        · simp only [red.go, ite_eq_right_iff]
          intro he
          subst he
          exfalso
          exact IsRed_not_repeated (ys := []) h
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

@[simp]
theorem red_append_inv_right (w v : W) : red (w ++ (v⁻¹ ++ v)) = red w := by
  rw [← red_append_red_right]
  simp

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
      rw [List.nil_append, List.append_nil, List.reverse_inj]
      exact go2 ys v hv
    next x xs ih => exact ih hxs
    next ys x xs _ =>
      exfalso
      simp [IsRed_not_repeated] at hxs
    next ys y x xs hne ih => simp_all [List.cons_append, red.go]
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
      simp only [List.cons.injEq, true_and]
      simp only [red.go] at h
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
  · exact red_IsRed w
  · exact red_IsRed v

theorem red_eq_red_iff_red_append_nil (w v : W) :
  red w = red v ↔ red (w⁻¹ ++ v) = [] := by rw [red_append_nil_iff, ← rev_red, List.reverse_inj]

@[simp]
theorem red_append_inj (w v : W) (h : IsRed w):
    w = red (w ++ v) ↔ red v = [] := by
  rw [← red_eq_of_IsRed h, red_append_red_left, red_eq_red_iff_red_append_nil, ← List.append_assoc,
    red_append_nil_iff, red_rev_self, List.nil_eq, List.reverse_eq_nil_iff]

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
  intro ⟨w, hw⟩ ⟨v, hv⟩
  simpa [Magma.op, hw, hv, red_append_nil_iff] using
    ff_fff (red (w⁻¹ ++ v)) (red_IsRed _)

theorem M.Refutes1648 : ¬ Equation1648 M := by
  unfold Equation1648
  push_neg
  use ⟨[1], by simp⟩, ⟨[3], by simp⟩
  decide

@[equational_result]
theorem Fact : ∃ (G : Type) (_ : Magma G), Facts G [206] [1648] :=
  ⟨_, _, M.Satisfies206, M.Refutes1648⟩

/-- We use a variant of the above construction to show that 1841 does not imply 203. We use as the
underlying magma M × Bool -/

def g : W → W
  | [] => [1]
  | x::__ => [x]

@[simp]
theorem g_nil : g [] = [1] := rfl

@[simp]
theorem gg_nil : g (g []) = [1] := rfl

theorem g_ne_nil (w : W) : g w ≠ [] := by
  induction w <;> simp [g]

@[simp]
theorem red_g (w : W) : red (g w) = g w := by
  unfold g; split <;> simp

@[simp]
theorem rev_g (w : W) : (g w)⁻¹ = g w := by
  unfold g; split <;> simp

@[simp]
theorem f_nil_iff (w : W) : f w = [] ↔ w = [] :=
match w with
| [] => by simp
| [x] => by simp
| x::_::_ => by simp [f]

/-- two variants of the main crucial relation -/
theorem ff_gff (z : W) (h : IsRed z) (ineq : z ≠ []) : f (f z) = g (red (f (f z) ++ z)) := by
  match z with
  | [] => tauto
  | [x] => simp [f, g]
  | x::y::zs =>
    have : IsRed ((x + 1) :: x :: y :: zs) := IsRed_cons (by simp; omega) h
    simp [f.eq_3, this, g]

theorem fg_gfg (z : W) (h : IsRed z) : f (g z) = g (red (f (g z) ++ z)) := by
  match z with
  | [] => tauto
  | [x] =>
    have : IsRed [x+1,x] := IsRed_cons (by simp; omega) h
    simp [f, g, this]
  | x::y::zs =>
    have : IsRed ((x + 1) :: x :: y :: zs) := IsRed_cons (by simp; omega) h
    simp [f.eq_3, this, g]

abbrev M2 := {x : W × Bool // IsRed x.1 }

instance inst2 : Magma M2 where
  op x y := match x, y with
  | ⟨(x, true), hx⟩ , _ => ⟨(x, true), hx⟩
  | ⟨(x, false), _⟩, ⟨(y, true), _⟩ => ⟨(red (x ++ g (red (x.reverse ++ y))),  false), red_IsRed _⟩
  | ⟨(x, false), hx⟩, ⟨(y,false), _⟩ =>
    if x = y then ⟨(x, true), hx⟩ else ⟨(red (x ++ f (red (x.reverse ++ y))), false), red_IsRed _⟩

theorem M2.Satisfies1841 : Equation1841 M2 := by
  intro ⟨(w,fw), hw⟩ ⟨(v,fv), hv⟩
  cases fw with
  | false =>
    cases fv with
    | false =>
      by_cases h : w = v
      · simp only [h, Magma.op, ↓reduceIte, red_rev_self, rev_red, List.reverse_append, rev_g,
        red_append_red_left, List.append_assoc, red_append_inv_right, red_g, Prod.mk.injEq,
        Subtype.mk.injEq, red_append_inj _ _ hv, and_true]
        decide
      · simpa [Magma.op, hw, hv, red_append_nil_iff, h] using
        ff_gff (red (w⁻¹ ++ v)) (red_IsRed _)
    | true =>
      simp only [Magma.op, hw, red_append_inj, red_g, red_append_red_right, red_append_inv]
      rw [ite_cond_eq_false _ _]
      simpa [Magma.op, hw, hv, red_append_nil_iff] using
        fg_gfg (red (w⁻¹ ++ v)) (red_IsRed _)
      simp [g_ne_nil]
  | true => simp only [Magma.op]

theorem M2.Refutes203 : ¬ Equation203 M2 := by
  unfold Equation203
  push_neg
  use ⟨([], false), by simp⟩
  decide

@[equational_result]
theorem Fact2 : ∃ (G : Type) (_ : Magma G), Facts G [1841] [203] :=
  ⟨_, _, M2.Satisfies1841, M2.Refutes203⟩

end ThreeC2
