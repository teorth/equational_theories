import equational_theories.Equations.All
import Mathlib.Data.Fintype.Card

/-!
# Equation 677: Chapter 13 Blueprint Lemmas

Formalizes lemmas from Chapter 13 of the Equational Theories Project blueprint
concerning the implication Equation 677 → Equation 255 for finite magmas.

**Equation 677:** `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`
**Equation 255:** `x = ((x ◇ x) ◇ x) ◇ x`

## Blueprint coverage

* **Lemma 13.1(i):** Left multiplication is bijective, with explicit inverse
  `L_y⁻¹(x) = x ◇ ((y ◇ x) ◇ y)` (`eq677_leftMul_surj`, `eq677_leftMul_inj`)
* **Lemma 13.1(ii):** Fixer uniqueness — if `y ◇ x = x` then `y = (x ◇ x) ◇ x`
  (`eq677_fixer_unique`)
* **Lemma 13.1(iii):** Backward recurrence `x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)`
  (`eq677_backward_recurrence`)
* **Lemma 13.2(ii↔iii):** 255 holds at x iff x has a fixer (`eq255_from_fixer_exists`)
* **Lemma 13.2(iv):** 255 at x ↔ ∃ z, (x ◇ z) ◇ x = x (`eq255_equiv_RxLx`)
* **Lemma 13.2(v):** 255 at x ↔ ∃ z, x ◇ (z ◇ x) = z (`eq255_equiv_LxRx`)

## Main theorem status

The implication Equation677 → Equation255 for finite magmas (ETP Problem 8.1)
remains open. These lemmas provide the algebraic infrastructure for a proof.
The key reduction: E255 holds iff every element has a fixer under right
multiplication. The fixer candidate `(x ◇ x) ◇ x` is unique (Lemma 13.1(ii)),
so E255 reduces to showing `((x ◇ x) ◇ x) ◇ x = x` for all x.

## References

* Tao et al., "Equational Theories Project", arXiv:2512.07087, Chapter 13
* Blueprint: https://teorth.github.io/equational_theories/blueprint/677-chapter.html
-/

namespace Eq677

variable {G : Type*} [Magma G]

/-! ### Section 1: Equational consequences (no finiteness needed)

These results follow from Equation 677 purely equationally, without
any finiteness hypothesis. -/

/-- E677 implies left multiplication is surjective: for each `y`, the map
`x ↦ y ◇ x` is surjective. The preimage of `x` under `L_y` is
`x ◇ ((y ◇ x) ◇ y)`. (Blueprint Lemma 13.1(i), surjectivity part.) -/
theorem eq677_leftMul_surj (h : Equation677 G) (y : G) :
    Function.Surjective (fun x => y ◇ x) := by
  intro x
  exact ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

/-- The explicit left-inverse formula: `L_y(x ◇ ((y ◇ x) ◇ y)) = x`.
This is a direct restatement of Equation 677. (Blueprint Lemma 13.1(i).) -/
theorem eq677_leftInv_formula (h : Equation677 G) (x y : G) :
    y ◇ (x ◇ ((y ◇ x) ◇ y)) = x :=
  (h x y).symm

/-- E677 at `(x, x)` gives `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`, which is
Equation 614. This means `L_x²((x ◇ x) ◇ x) = x`, so the fixer candidate
`(x ◇ x) ◇ x` is exactly `L_x⁻²(x)`. -/
theorem eq677_e614 (h : Equation677 G) (x : G) :
    x = x ◇ (x ◇ ((x ◇ x) ◇ x)) :=
  h x x

/-- E677 applied at `(y ◇ x, y)`: the key step for the backward recurrence.
Gives `y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y))`. -/
theorem eq677_at_Lyx (h : Equation677 G) (x y : G) :
    y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)) :=
  h (y ◇ x) y

/-- Blueprint Lemma 13.2(iv), no finiteness needed: 255 at x ↔ ∃ z, (x ◇ z) ◇ x = x.
The forward direction wraps `z` as `x ◇ z`; the reverse uses the inverse formula. -/
theorem eq255_equiv_RxLx (h : Equation677 G) (x : G) :
    (∃ z, (x ◇ z) ◇ x = x) ↔ (∃ y, y ◇ x = x) := by
  constructor
  · rintro ⟨z, hz⟩; exact ⟨x ◇ z, hz⟩
  · rintro ⟨y, hy⟩
    use y ◇ ((x ◇ y) ◇ x)
    have : x ◇ (y ◇ ((x ◇ y) ◇ x)) = y := eq677_leftInv_formula h y x
    rw [this]; exact hy

/-- The σ² identity: `σ_a(σ_a(b)) = σ_a(b) ◇ (b ◇ a)` where
`σ_a(b) = b ◇ ((a ◇ b) ◇ a)` is the inverse formula applied at `(b, a)`. -/
theorem eq677_sigma_squared (h : Equation677 G) (a b : G) :
    let s := b ◇ ((a ◇ b) ◇ a)
    s ◇ ((a ◇ s) ◇ a) = s ◇ (b ◇ a) := by
  simp only []
  have hab : a ◇ (b ◇ ((a ◇ b) ◇ a)) = b := (h b a).symm
  rw [hab]

/-! ### Section 2: Finiteness-dependent results

On finite magmas, surjectivity of L_y upgrades to bijectivity and
left cancellation, unlocking the backward recurrence and fixer uniqueness. -/

variable [Finite G]

/-- On a finite magma, left multiplication is injective (from surjectivity
via the pigeonhole principle). (Blueprint Lemma 13.1(i), injectivity part.) -/
theorem eq677_leftMul_inj (h : Equation677 G) (y : G) :
    Function.Injective (fun x => y ◇ x) :=
  (Finite.injective_iff_surjective).mpr (eq677_leftMul_surj h y)

/-- Left cancellation: `y ◇ a = y ◇ b → a = b`. (Consequence of 13.1(i).) -/
theorem eq677_left_cancel (h : Equation677 G) (y : G) {a b : G}
    (hab : y ◇ a = y ◇ b) : a = b :=
  eq677_leftMul_inj h y hab

/-- **Blueprint Lemma 13.1(iii).** The backward recurrence:
`x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)`.
Proof: apply E677 at `(y ◇ x, y)` and left-cancel `y`. -/
theorem eq677_backward_recurrence (h : Equation677 G) (x y : G) :
    x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) := by
  have h1 : y ◇ x = y ◇ ((y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)) := eq677_at_Lyx h x y
  exact eq677_left_cancel h y h1

/-- The backward recurrence in orbit notation: if `c = y ◇ x` and `d = y ◇ c`,
then `x = c ◇ (d ◇ y)`. This is `c_{k-1} = c_k ◇ d_{k+1}` in d-sequence form. -/
theorem eq677_orbit_step (h : Equation677 G) (x y : G) :
    let c := y ◇ x
    let d := y ◇ c
    x = c ◇ (d ◇ y) := by
  simp only []
  exact eq677_backward_recurrence h x y

/-- **Blueprint Lemma 13.1(ii).** Fixer uniqueness: if `y ◇ x = x`,
then `y = (x ◇ x) ◇ x`.

Proof: From `y ◇ x = x`, the inverse formula gives `x = x ◇ (x ◇ y)`.
From E614: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`. Left-cancel `x` twice to get
`y = (x ◇ x) ◇ x`. -/
theorem eq677_fixer_unique (h : Equation677 G) {x y : G}
    (hfix : y ◇ x = x) : y = (x ◇ x) ◇ x := by
  -- Step 1: inverse formula + hfix gives y ◇ (x ◇ (x ◇ y)) = x
  have inv_at_x : y ◇ (x ◇ (x ◇ y)) = x := by
    have h1 := eq677_leftInv_formula h x y
    rw [hfix] at h1; exact h1
  -- Step 2: y ◇ x = y ◇ (x ◇ (x ◇ y)), left-cancel y: x = x ◇ (x ◇ y)
  have step2 : y ◇ x = y ◇ (x ◇ (x ◇ y)) := by rw [hfix, inv_at_x]
  have hx_xy : x = x ◇ (x ◇ y) := eq677_left_cancel h y step2
  -- Step 3: E614 gives x = x ◇ (x ◇ ((x◇x)◇x))
  have h614 : x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := eq677_e614 h x
  -- Step 4: left-cancel x twice
  have step4 : x ◇ (x ◇ y) = x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    rw [← hx_xy]; exact h614
  have step5 : x ◇ y = x ◇ ((x ◇ x) ◇ x) := eq677_left_cancel h x step4
  exact eq677_left_cancel h x step5

/-- **Blueprint Lemma 13.2**, reduction (ii)↔(iii): 255 holds at `x` iff
`x` has a fixer, i.e., `∃ y, y ◇ x = x`. Combined with fixer uniqueness,
the fixer must be `(x ◇ x) ◇ x`. -/
theorem eq255_from_fixer_exists (h : Equation677 G) (x : G)
    (hfix : ∃ y : G, y ◇ x = x) : x = ((x ◇ x) ◇ x) ◇ x := by
  obtain ⟨y, hy⟩ := hfix
  have : y = (x ◇ x) ◇ x := eq677_fixer_unique h hy
  rw [← this]; exact hy.symm

/-- **Blueprint Lemma 13.2(v):** 255 at x ↔ `L_x ∘ R_x` has a fixed point,
i.e., ∃ z, x ◇ (z ◇ x) = z. -/
theorem eq255_equiv_LxRx (h : Equation677 G) (x : G) :
    (∃ z, x ◇ (z ◇ x) = z) ↔ (∃ y, y ◇ x = x) := by
  constructor
  · rintro ⟨z, hz⟩
    use x ◇ z
    have h677z : x ◇ (z ◇ ((x ◇ z) ◇ x)) = z := eq677_leftInv_formula h z x
    have step1 : x ◇ (z ◇ ((x ◇ z) ◇ x)) = x ◇ (z ◇ x) := by rw [h677z, hz]
    have step2 : z ◇ ((x ◇ z) ◇ x) = z ◇ x := eq677_left_cancel h x step1
    exact eq677_left_cancel h z step2
  · rintro ⟨y, hy⟩
    use y ◇ ((x ◇ y) ◇ x)
    set w := y ◇ ((x ◇ y) ◇ x)
    have hinv : x ◇ w = y := eq677_leftInv_formula h y x
    have h677w : x ◇ (w ◇ ((x ◇ w) ◇ x)) = w := eq677_leftInv_formula h w x
    rw [show x ◇ w = y from hinv] at h677w
    rw [hy] at h677w
    exact h677w

/-! ### Section 3: Additional algebraic infrastructure

Further identities that provide structure for the open problem. -/

/-- The fixer candidate factors: `(x◇x)◇x = (x◇((x◇x)◇x)) ◇ (x◇x)`.
Equivalently, `φ(x) = L_{ψ(x)}(x◇x)` where `ψ(x) = x ◇ φ(x)`. -/
theorem eq677_fixer_factorization (h : Equation677 G) (x : G) :
    (x ◇ x) ◇ x = (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) := by
  have h614 : x = x ◇ (x ◇ ((x ◇ x) ◇ x)) := eq677_e614 h x
  have h1 := eq677_at_Lyx h ((x ◇ x) ◇ x) x
  have h2 : x ◇ (x ◇ ((x ◇ x) ◇ x)) = x := h614.symm
  rw [h2] at h1
  exact eq677_left_cancel h x h1

/-- The orbit recurrence: `c_k = c_{k+1} ◇ (c_{k+2} ◇ x)` where `c_k = L_x^k(x)`.
This is the backward recurrence specialized to the L_x-orbit. -/
theorem eq677_orbit_recurrence (h : Equation677 G) (x : G) (k : ℕ) :
    (fun z => x ◇ z)^[k] x =
      ((fun z => x ◇ z)^[k + 1] x) ◇ (((fun z => x ◇ z)^[k + 2] x) ◇ x) := by
  simp only [Function.iterate_succ', Function.comp]
  exact eq677_backward_recurrence h ((fun z => x ◇ z)^[k] x) x

/-- Key identity (discovered with assistance from Aristotle [harmonic.fun]):
`(y ◇ (y ◇ x)) ◇ y = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x))`.
Proof: compare the backward recurrence at `(x, y)` with E677 at `(x, y ◇ x)`,
then left-cancel `(y ◇ x)`. -/
theorem eq677_key_identity (h : Equation677 G) (x y : G) :
    (y ◇ (y ◇ x)) ◇ y = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x)) := by
  have hbr := eq677_backward_recurrence h x y
  have he677 := h x (y ◇ x)
  exact eq677_left_cancel h (y ◇ x) (hbr.symm.trans he677)

/-- The Star equation: if `a ◇ x = b ◇ x`, then `(a ◇ (a ◇ x)) ◇ a = (b ◇ (b ◇ x)) ◇ b`.
This shows that right-cancellation failure at x propagates to the next level.
It is the algebraic barrier: every manipulation of E677 with `a ◇ x = b ◇ x`
reduces to right cancellation. -/
theorem eq677_star_eq (h : Equation677 G) (x : G) {a b : G}
    (heq : a ◇ x = b ◇ x) :
    (a ◇ (a ◇ x)) ◇ a = (b ◇ (b ◇ x)) ◇ b := by
  have h1 := eq677_backward_recurrence h x a
  have h2 := eq677_backward_recurrence h x b
  rw [heq]
  conv at h1 => rw [show a ◇ x = b ◇ x from heq]
  have h3 : (b ◇ x) ◇ ((a ◇ (b ◇ x)) ◇ a) =
      (b ◇ x) ◇ ((b ◇ (b ◇ x)) ◇ b) := by
    rw [← h1, ← h2]
  exact eq677_left_cancel h (b ◇ x) h3

/-- Uniqueness of the `L_x²`-preimage: if `x ◇ (x ◇ z) = x`, then `z = (x◇x)◇x`. -/
theorem eq677_phi_unique_Lx2_preimage (h : Equation677 G) (x z : G)
    (hz : x ◇ (x ◇ z) = x) : z = (x ◇ x) ◇ x := by
  have h1 : x ◇ (x ◇ z) = x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    rw [hz]; exact eq677_e614 h x
  exact eq677_left_cancel h x (eq677_left_cancel h x h1)

end Eq677
