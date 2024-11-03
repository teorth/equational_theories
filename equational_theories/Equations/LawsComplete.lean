import equational_theories.RArray
import equational_theories.MagmaLaw
import equational_theories.Equations.All

/-!
This module proves that are actually looking at at the laws we claim to be looking at.

See `laws_complete` for the main result.
-/


open Lean Elab in
/--
An elaborator to assemble all the separate `Law{n}` definitions into one data structure.
-/
elab "defineLaws%" : term => do
  let consts : RArray Expr := RArray.ofFn (h := by omega) fun (⟨i, _⟩ : Fin 4694) =>
    mkConst (.mkSimple s!"Law{i+1}")
  return consts.toExpr (mkConst ``Law.NatMagmaLaw) id

/--
All the separate `Law{n}` definitions in one data structure.

```
example : laws[1000] = Law1001 := rfl
```
-/
def laws : RArray Law.NatMagmaLaw := defineLaws%

theorem laws.wf : laws.WF := by decide

example : laws[1000] = Law1001 := rfl

/-!
The laws are in order, so we can use binary search to find it.
-/


/-- An ordering on `FreeMagma` that coincides with the order we put the laws in.  -/
def FreeMagma.comp {α} [LinearOrder α] (m1 m2 : FreeMagma α) : Ordering :=
  (compare m1.forks m2.forks).then <|
    match m1, m2 with
    | .Leaf n,     .Leaf m     => compare n m
    | .Leaf _,     .Fork _ _   => .lt
    | .Fork _ _,   .Leaf _     => .gt
    | .Fork l1 r1, .Fork l2 r2 => (l1.comp l2).then (r1.comp r2)

theorem FreeMagma.comp_swap {α} [LinearOrder α] (l1 l2 : FreeMagma α) :
    (l1.comp l2).swap = l2.comp l1 := by
  rw [FreeMagma.comp.eq_def, FreeMagma.comp.eq_def]
  simp [FreeMagma.comp, Ordering.swap_then, Nat.compare_swap]; congr
  split
  · apply Batteries.OrientedCmp.symm
  · rfl
  · rfl
  · rw [Ordering.swap_then, FreeMagma.comp_swap, FreeMagma.comp_swap]

/-- The number of forks in a magma law. -/
def Law.MagmaLaw.forks {α} (l : Law.MagmaLaw α) : Nat :=
  l.lhs.forks + l.rhs.forks

/-- An ordering on `NatMagmaLaw` that coincides with the order we put the laws in.  -/
def Law.MagmaLaw.comp {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) : Ordering :=
  let l1' := l1.map (fun _ => 0)
  let l2' := l2.map (fun _ => 0)
  Ordering.then (compare l1.forks l2.forks) <|
  Ordering.then (FreeMagma.comp l1'.lhs l2'.lhs) <|
  Ordering.then (FreeMagma.comp l1'.rhs l2'.rhs) <|
  Ordering.then (FreeMagma.comp l1.lhs l2.lhs) <|
  (FreeMagma.comp l1.rhs l2.rhs)

theorem Law.MagmaLaw.comp_swap {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) :
    (l1.comp l2).swap = l2.comp l1 := by
  simp [MagmaLaw.comp, Ordering.swap_then, Nat.compare_swap, FreeMagma.comp_swap]

/--
Binary search on `laws` for a given law. If the given law is not in `laws`, an arbitrary value is
returned.
-/
def findMagmaLaw (l : Law.NatMagmaLaw) : Nat :=
  go 0 laws.size
where
  go lb w :=
    if w ≤ 1 then
      lb
    else
      let w' := w/2
      let mid := lb + w'
      let l' := laws[mid]
      if l.comp l' = .lt then
        go lb w'
      else
        go mid (w-w')

/-- The largest used variable. -/
def FreeMagma.max : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork l r => Nat.max l.max r.max

/-- The largest used variable. -/
def Law.MagmaLaw.max (l : Law.MagmaLaw Nat) : Nat := Nat.max l.lhs.max l.rhs.max

/-- Canonically reorders variables -/
def FreeMagma.canonicalize {α} [DecidableEq α] (m : FreeMagma α) : FreeMagma Nat :=
  (go m #[]).1
where
  go : FreeMagma α → StateM (Array α) (FreeMagma Nat)
  | .Leaf v => do
    let xs ← get
    match xs.indexOf? v with
    | some i => return .Leaf i
    | none =>
      set (xs.push v)
      return .Leaf xs.size
  | .Fork l r => do
    let l ← go l
    let r ← go r
    return .Fork l r

/-- Canonically reorders variables -/
def Law.MagmaLaw.canonicalize {α} [DecidableEq α] (l : Law.MagmaLaw α) : Law.MagmaLaw Nat :=
  (go #[]).1
where
  go : StateM (Array α) Law.NatMagmaLaw := do
    let lhs' ← FreeMagma.canonicalize.go l.lhs
    let rhs' ← FreeMagma.canonicalize.go l.rhs
    return ⟨lhs', rhs'⟩

/-- Checks whether variables are canonically ordered -/
def FreeMagma.isCanonical (next : Nat) : FreeMagma Nat → Option Nat
  | .Leaf i => do
    if i < next then
      return next
    else if i = next then
      return next + 1
    else
      none
  | .Fork l r => do (← l.isCanonical next) |> r.isCanonical

def Law.MagmaLaw.IsCanonicalLabel (l : Law.MagmaLaw Nat) : Prop :=
  ∃ n n', l.lhs.isCanonical 0 = some n ∧ l.rhs.isCanonical n = some n'

/--
Checks whether a magma law is canonical:
* Variables are canonically labeled
* `lhs < rhs` (with the exception of `0 ≃ 0`)
* The symmetric law did not come first
-/
def Law.MagmaLaw.IsCanonical (l : Law.MagmaLaw Nat) : Prop :=
  l.IsCanonicalLabel ∧
  (l.lhs = l.rhs → l.lhs = .Leaf 0) ∧
  l.symm.canonicalize.comp l ≠ .lt

theorem Array.indexOf?_eq {α} [BEq α] (arr : Array α) (a : α) :
    (arr.indexOf? a).map (·.1) = arr.toList.indexOf? a :=
  (aux [] _ rfl).trans (by simp [List.indexOf?])
where
  aux (l r) (hi : arr.toList = l ++ r) :
      (arr.indexOfAux a l.length).map (·.1) = (r.findIdx? (· == a)).map (· + l.length) := by
    cases r <;> rw [indexOfAux] <;> simp
    · simp at hi; simp [← hi]
    · split
      · next b r h =>
        have IH := aux (l ++ [b]) r
        simp [hi] at IH
        have : arr[l.length] = b := by
          simp [Array.getElem_eq_getElem_toList, hi]
          rw [List.getElem_append_right] <;> simp
        simp [this]
        split <;> simp
        apply IH.trans; congr; ext; simp; omega
      · next h => rw [Array.size, hi] at h; simp at h

theorem FreeMagma.canonicalize.go_leaf {α} [DecidableEq α] (xs : List α) (v) :
    FreeMagma.canonicalize.go (Lf v) ⟨xs⟩ =
    match xs.indexOf? v with
    | some i => (.Leaf i, ⟨xs⟩)
    | none => (.Leaf xs.length, ⟨xs ++ [v]⟩) := by
  simp [go, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, ← Array.indexOf?_eq ⟨xs⟩]
  cases Array.indexOf? ⟨xs⟩ v <;> rfl

theorem List.getElem?_of_indexOf? {α} [DecidableEq α] {v : α} {xs i} :
    List.indexOf? v xs = some i → xs[i]? = some v := by
  simp [indexOf?]
  induction' xs with _ _ ih generalizing i <;> simp; split <;> simp
  · rintro rfl; simp [*]
  · rintro _ e rfl; simp [ih e]

theorem List.lt_len_of_getElem? {α} {v : α} {xs i} (H : xs[i]? = some v) : i < length xs :=
  lt_of_not_le fun h => by simp [getElem?_len_le h] at H

theorem FreeMagma.canonicalize_prop {α} [DecidableEq α]
    {m : FreeMagma α} {xs : Array α}
    {m' arr} (H : FreeMagma.canonicalize.go m xs = (m', arr)) :
    m'.isCanonical xs.size = some arr.size ∧
    (xs.toList.Nodup →
      arr.toList.Nodup ∧
      (∀ i : Fin xs.size, ∃ h, xs[i] = arr[i.1]'h) ∧
      (∀ f, (∀ i : Fin arr.size, f arr[i] = i.1) → fmapHom f m = m') ∧
      (∀ f, (∀ i : Fin arr.size, f i.1 = arr[i]) → fmapHom f m' = m)) := by
  induction m generalizing xs m' arr with
  | Leaf v =>
    cases' xs with xs
    simp [canonicalize.go_leaf, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get] at H
    revert H; cases' e : xs.indexOf? v with i <;> rintro ⟨⟩ <;>
      simp only [isCanonical, Array.size_toArray, lt_self_iff_false, ↓reduceIte, pure, Array.size,
        List.length_append, List.length_singleton, Fin.getElem_fin, Array.getElem_mk, true_and,
        ite_eq_left_iff, not_lt, Option.ite_none_right_eq_some, Option.some.injEq,
        Nat.succ_ne_self, and_false, imp_false, not_le, Fin.is_lt, exists_const, implies_true]
    · intro H
      refine ⟨?_, fun i => ⟨by omega, by rw [List.getElem_append_left]⟩, ?_⟩
      · simp [List.nodup_append, H]
        simpa using List.indexOf?_eq_none_iff.1 e v
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · simp [fmapHom, evalInMagma]
        convert hf ⟨xs.length, ?_⟩ <;> simp
      · simp [fmapHom, evalInMagma]
        convert hf ⟨xs.length, ?_⟩ <;> simp
    · have := List.getElem?_of_indexOf? e
      have ⟨hi, this⟩ := List.getElem?_eq_some.1 this
      refine ⟨hi, fun H => ⟨H,
        fun f hf => congrArg Lf (this ▸ hf ⟨i, hi⟩),
        fun f hf => congrArg Lf (this ▸ hf ⟨i, hi⟩)⟩⟩
  | Fork l r ihl ihr =>
    simp [canonicalize.go, bind, StateT.bind] at H
    split at H; split at H; cases H; rename_i m1 arr1 eq1 _ m2 eq2
    let ⟨ihl1, ihl2⟩ := ihl eq1
    let ⟨ihr1, ihr2⟩ := ihr eq2
    refine ⟨?_, fun H => ?_⟩
    · rw [isCanonical, Option.bind_eq_bind, ihl1, Option.some_bind, ihr1]
    let ⟨H, ihl3, ihl4, ihl5⟩ := ihl2 H
    let ⟨H, ihr3, ihr4, ihr5⟩ := ihr2 H
    refine ⟨H,
      fun i => let ⟨h, hl⟩ := ihl3 i; let ⟨h, hr⟩ := ihr3 ⟨i, h⟩; ⟨h, hl.trans hr⟩,
      fun f hf => congr (congrArg Fork (ihl4 _ ?_)) (ihr4 _ hf),
      fun f hf => congr (congrArg Fork (ihl5 _ ?_)) (ihr5 _ hf)⟩ <;>
    · intro i; let ⟨h, hl⟩ := ihr3 i; rw [hl]; exact hf ⟨i, h⟩

theorem FreeMagma.canonicalize_self
    {m : FreeMagma ℕ} {k n} (can : m.isCanonical k = some n) :
    FreeMagma.canonicalize.go m (Array.range k) = (m, Array.range n) := by
  induction m generalizing k n with
  | Leaf v =>
    rw [canonicalize.go_leaf, Array.toList_range]
    let _ := instBEqOfDecidableEq (α := Nat)
    have : (List.range k).indexOf? v = if v < k then some v else none := by
      cases' e : (List.range k).indexOf? v with i
      · have := List.indexOf?_eq_none_iff.1 e
        simp at this; rw [if_neg]
        exact fun h => this _ h rfl
      · have := List.getElem?_of_indexOf? e
        have ⟨hi, e⟩ := List.getElem?_eq_some.1 this
        simp [List.getElem_range] at e; simp_all
    simp [isCanonical] at can; split at can
    · cases can; rw [this]; split_ifs; simp [pure, StateT.pure]
    · simp at can; obtain ⟨rfl, rfl⟩ := can
      simp [this]; congr 2; simp; exact (Array.toList_range _).symm
  | Fork l r ihl ihr =>
    simp [isCanonical, Option.bind_eq_some] at can
    obtain ⟨n', h1, h2⟩ := can
    simp [canonicalize.go, bind, StateT.bind, ihl h1, ihr h2]; rfl

theorem Law.MagmaLaw.canonicalize_self {m : Law.MagmaLaw ℕ} (H : m.IsCanonicalLabel) :
    m.canonicalize = m := by
  let ⟨a, b, h1, h2⟩ := H
  simp [canonicalize, canonicalize.go, bind, StateT.bind, show #[] = Array.range 0 by rfl,
    FreeMagma.canonicalize_self h1, FreeMagma.canonicalize_self h2]
  rfl

theorem FreeMagma.canonicalize_relabelling {α β} [DecidableEq α] [DecidableEq β]
    {m₁ : FreeMagma α} {m₂ : FreeMagma β}
    {f g} (h1 : fmapHom f m₁ = m₂) (h2 : fmapHom g m₂ = m₁)
    {m₁' xs₁ xs₁'} (e1 : canonicalize.go m₁ xs₁ = (m₁', xs₁'))
    {m₂' xs₂ xs₂'} (e2 : canonicalize.go m₂ xs₂ = (m₂', xs₂'))
    (H : xs₁.toList.Forall₂ (fun a b => f a = b ∧ g b = a) xs₂.toList) :
    m₁' = m₂' ∧ xs₁'.toList.Forall₂ (fun a b => f a = b ∧ g b = a) xs₂'.toList := by
  cases h1
  induction m₁ generalizing m₁' xs₁' m₂' xs₂' xs₁ xs₂ with
  | Leaf v =>
    injection h2 with h2; have ⟨xs₁⟩ := xs₁; have ⟨xs₂⟩ := xs₂
    simp [fmapHom, evalInMagma, canonicalize.go_leaf] at e1 e2 H
    have : List.indexOf? (f v) xs₂ = List.indexOf? v xs₁ := by
      simp [List.indexOf?]; clear e1 e2
      induction' H with a b xs₁ xs₂ H _ ih <;> simp [List.indexOf?]
      congr 1
      · simp; refine ⟨fun h => ?_, fun h => ?_⟩
        · rwa [← h, H.2] at h2
        · rw [← h, H.1]
      · rw [ih]
    revert e1 e2; rw [this]; cases xs₁.indexOf? v <;> simp <;> rintro ⟨⟩ ⟨⟩
    · refine ⟨by rw [H.length_eq], ?_⟩
      rw [← List.forall₂_reverse_iff]; simp [h2, H]
    · simp [H]
  | Fork l r ihl ihr =>
    revert e1 e2
    injection h2 with hl2 hr2
    simp [canonicalize.go, bind, StateT.bind]
    split; split; split; split; rename_i l1 _ _ _ r1 _ _ _ l2 _ _ _ r2
    rintro ⟨⟩ ⟨⟩
    obtain ⟨rfl, H⟩ := ihl l1 H hl2 l2
    obtain ⟨rfl, H⟩ := ihr r1 H hr2 r2
    exact ⟨rfl, H⟩

theorem Law.MagmaLaw.canonicalize_relabelling {α β} [DecidableEq α] [DecidableEq β]
    {m : Law.MagmaLaw α} {m' : Law.MagmaLaw β}
    {f g} (h1 : m.map f = m') (h2 : m'.map g = m) :
    m.canonicalize = m'.canonicalize := by
  let ⟨l₁, r₁⟩ := m; let ⟨l₂, r₂⟩ := m'; simp [map] at h1 h2
  simp [canonicalize, canonicalize.go, bind, StateT.bind]
  split; split; split; split; rename_i l1 _ _ _ r1 _ _ _ l2 _ _ _ r2
  obtain ⟨rfl, H⟩ := FreeMagma.canonicalize_relabelling h1.1 h2.1 l1 l2 .nil
  obtain ⟨rfl, _⟩ := FreeMagma.canonicalize_relabelling h1.2 h2.2 r1 r2 H
  rfl

theorem Law.MagmaLaw.canonicalize_is_relabelling {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    (∃ f : α → ℕ, m.map f = m.canonicalize) ∧ (∃ g : ℕ → α, m.canonicalize.map g = m) := by
  cases' m with l r; simp [canonicalize, canonicalize.go, bind, StateT.bind]
  split; split; rename_i m1 arr1 eq1 _ m2 arr eq2
  simp [pure, StateT.pure, map]
  obtain ⟨l1, -, l2, l3⟩ := (l.canonicalize_prop eq1).2 .nil
  obtain ⟨r1, h, r2, r3⟩ := (r.canonicalize_prop eq2).2 l1
  have ⟨g, hg⟩ : ∃ (g : ℕ → α), ∀ (i : Fin arr.size), g i.1 = arr[i] := by
    have : Inhabited α := ⟨l.first⟩
    exact ⟨fun i => arr[i]!, fun i => by simp [getElem!_pos]⟩
  have ⟨f, hf⟩ : ∃ (f : α → ℕ), ∀ (i : Fin arr.size), f arr[i] = ↑i := by
    have (i j : Fin arr.size) (eq : g i = g j) : i.1 = j.1 :=
      Fin.val_eq_of_eq <| List.nodup_iff_injective_getElem.1 r1 (by simpa [hg] using eq)
    have : Set.InjOn g {i | i < arr.size} := fun i hi j hj => this ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨Function.invFunOn g {i | i < arr.size}, fun i => ?_⟩
    convert Set.InjOn.leftInvOn_invFunOn this i.2; rw [hg]
  refine ⟨
    ⟨f, l2 _ fun i => (h i).2 ▸ hf ⟨_, (h i).1⟩, r2 _ hf⟩,
    ⟨g, l3 _ fun i => (h i).2 ▸ hg ⟨_, (h i).1⟩, r3 _ hg⟩⟩

theorem Law.MagmaLaw.canonicalize_iff {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    m.canonicalize.iff m := by
  let ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := m.canonicalize_is_relabelling
  exact reindex_iff _ _ hg hf

theorem Law.MagmaLaw.canonicalize_symm_canonicalize {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    m.canonicalize.symm.canonicalize = m.symm.canonicalize := by
  have ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := m.canonicalize_is_relabelling
  apply canonicalize_relabelling (f := g) (g := f)
  · rw [map_symm, hg]
  · rw [map_symm, hf]

theorem Law.MagmaLaw.canonicalize_isCanonicalLabel {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    m.canonicalize.IsCanonicalLabel := by
  cases' m with l r; simp [canonicalize, canonicalize.go, bind, StateT.bind]
  split; split; rename_i l' arr1 eq1 _ r' arr eq2
  simp [pure, StateT.pure, map]
  obtain hl := (l.canonicalize_prop eq1).1
  obtain hr := (r.canonicalize_prop eq2).1
  simp at hl; simp [IsCanonicalLabel, hl, hr]

theorem FreeMagma.map_forks {α β} (m : FreeMagma α) (f : α → β) :
    (fmapHom f m).forks = m.forks := by simp [fmapHom]; induction m <;> simp [forks, *]

theorem Law.MagmaLaw.map_forks {α β} (m : Law.MagmaLaw α) (f : α → β) :
    (m.map f).forks = m.forks := by cases m; simp [map, forks, FreeMagma.map_forks]

theorem Law.MagmaLaw.canonicalize_forks {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    m.canonicalize.forks = m.forks := by
  let ⟨h, hf⟩ := m.canonicalize_is_relabelling.1
  rw [← hf, map_forks]

theorem Law.MagmaLaw.symm_forks {α} (m : Law.MagmaLaw α) :
    m.symm.forks = m.forks := by cases m; simp [symm, forks, Nat.add_comm]

-- theorem ordering_stuff (l r : FreeMagma ℕ) (h1 : l.comp r = .gt) :
--     (l ≃ r).symm.canonicalize.comp (l ≃ r) = .lt := by
--   -- is this even true?

theorem Law.MagmaLaw.exists_canonical {α} (m : Law.MagmaLaw α) :
    ∃ m', m'.IsCanonical ∧ m'.forks ≤ m.forks ∧ m.iff m' := by
  classical
  have (m : Law.MagmaLaw α) (e : m.symm.canonicalize.comp m.canonicalize = .gt) :
      ∃ m', m'.IsCanonical ∧ m'.forks ≤ m.forks ∧ m.iff m' := by
    refine ⟨m.canonicalize, ⟨m.canonicalize_isCanonicalLabel, fun h => ?_, ?_⟩, ?_, ?_⟩
    · rw [← canonicalize_symm_canonicalize] at e
      have := m.canonicalize_isCanonicalLabel
      generalize m.canonicalize = m' at e h this
      rw [show m'.symm = m' by cases m'; simp_all [symm], canonicalize_self this] at e
      cases e ▸ (Law.MagmaLaw.comp_swap _ _).trans e
    · rw [canonicalize_symm_canonicalize, e]; nofun
    · rw [canonicalize_forks]
    · exact m.canonicalize_iff.symm
  cases e : m.symm.canonicalize.comp m.canonicalize with
  | gt => exact this _ e
  | lt =>
    specialize this m.symm
    rw [symm_symm, ← comp_swap, e] at this
    let ⟨m', h1, h2, h3⟩ := this rfl
    exact ⟨m', h1, symm_forks m ▸ h2, (symm_iff _).trans h3⟩
  | eq =>
    by_cases h : m.canonicalize.lhs = m.canonicalize.rhs
    · have : (Lf 0 ≃ Lf 0).IsCanonicalLabel := ⟨_, _, rfl, rfl⟩
      have can : (Lf 0 ≃ Lf 0).IsCanonical :=
        ⟨this, fun _ => rfl, by simp [symm, canonicalize_self this]; nofun⟩
      refine ⟨Lf 0 ≃ Lf 0, can, Nat.zero_le _, m.canonicalize_iff.symm.trans ?_⟩
      refine fun G _ => ⟨fun _ _ => rfl, fun _ _ => by simp [satisfiesPhi, h]⟩
    · refine ⟨m.canonicalize, ⟨m.canonicalize_isCanonicalLabel, h.elim, ?_⟩, ?_, ?_⟩
      · rw [canonicalize_symm_canonicalize, e]; nofun
      · rw [canonicalize_forks]
      · let ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := m.canonicalize_is_relabelling
        exact reindex_iff _ _ hf hg

/-!
A decision procedure for checking a predicate for all canonical magma laws of a certain size.

The proofs are rather unpretty; maybe phrasing everything in terms of `Decidable` would
have made that easier. But what works works.
-/

open Lean Qq

def TestNat (n : Nat) (P : Nat → Prop) : Prop := ∀ i < n, P i

theorem TestNat.zero {P} : TestNat 0 P := by simp [TestNat]
theorem TestNat.succ {n P} (h1 : TestNat n P) (h2 : P n) : TestNat (n+1) P := by
  simpa only [TestNat, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq, and_true, h2]

def proveTestNat (n : Nat) {P : Q(Nat → Prop)} (hP : (i : Nat) → Q($P $i)) : Q(TestNat $n $P) :=
  match n with
  | 0 => q(TestNat.zero)
  | n+1 => q(TestNat.succ $(proveTestNat n hP) $(hP n))

def TestAllSplits (n : Nat) (P : Nat → Nat → Prop) : Prop := ∀ i j, i + j = n → P i j
def TestAllSplits' (i j : Nat) (P : Nat → Nat → Prop) : Prop :=
  ∀ i' < i, P i' (j + (i - i'))

theorem TestAllSplits'.zero {n P} : TestAllSplits' 0 n P := by simp [TestAllSplits', *]
theorem TestAllSplits'.succ {i j P}
    (h1 : TestAllSplits' i (j+1) P) (h2 : P i (j+1)) : TestAllSplits' (i+1) j P := by
  simp only [TestAllSplits', Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq,
    Nat.add_sub_cancel_left] at *
  exact ⟨fun i' h => by convert h1 i' h using 1; omega, h2⟩

theorem TestAllSplits.start {n P} (h1 : TestAllSplits' n 0 P) (h2 : P n 0) : TestAllSplits n P := by
  have : ∀ i ≤ n, P i (n - i) := by
    simpa [TestAllSplits', Nat.le_iff_lt_or_eq, or_imp, forall_and, h2] using h1
  intro i j eq
  cases Nat.eq_sub_of_add_eq' eq
  exact this _ (by omega)

def proveTestAllSplits (n : Nat) {P : Q(Nat → Nat → Prop)} (hP : (i j : Nat) → Q($P $i $j)) :
    Q(TestAllSplits $n $P) :=
  let rec go (i j : Nat) : Q(TestAllSplits' $i $j $P) :=
    match i with
    | 0 => q(TestAllSplits'.zero)
    | i + 1 => q(TestAllSplits'.succ $(go i (j+1)) $(hP i (j+1)))
  q(TestAllSplits.start $(go n 0) $(hP n 0))

def TestFreeMagmas (s n : Nat) (P : Nat → FreeMagma Nat → Prop) :=
  ∀ m n', m.forks = s → m.isCanonical n = some n' → P n' m

theorem TestFreeMagmas.zero {n P}
    (H : TestNat (n+1) fun i => P (if i < n then n else n+1) (.Leaf i))
    : TestFreeMagmas 0 n P := by
  intro
  | .Leaf i, n, _, eq =>
    simp (config := {contextual := true}) [TestFreeMagmas, TestNat, FreeMagma.isCanonical] at *
    specialize H i
    split at eq
    · simp_all; apply H; omega
    · split at eq <;> simp_all

theorem TestFreeMagmas.succ {s n P}
    (H : TestAllSplits s fun s1 s2 =>
      TestFreeMagmas s1 n fun n l =>
        TestFreeMagmas s2 n fun n r =>
          P n (.Fork l r))
    : TestFreeMagmas (s+1) n P := by
  intro
  | .Fork l r, n, hadd =>
    simp (config := {contextual := true}) [TestFreeMagmas, FreeMagma.isCanonical,
        TestAllSplits, Option.bind_eq_some, FreeMagma.forks] at *
    rintro n'' hcan1
    exact H _ _ hadd _ _ rfl hcan1 _ _ rfl

partial def proveTestFreeMagmas (s n : Nat) (P : Q(Nat → FreeMagma Nat → Prop))
    (hP : (i : Nat) → FreeMagma Nat → (m : Q(FreeMagma Nat)) → Q($P $i $m)) :
    Q(TestFreeMagmas $s $n $P) :=
  match s with
  | 0 =>
    let h := proveTestNat (n+1) fun i : Nat => hP (if i < n then n else n+1) (.Leaf i) q(.Leaf $i)
    q(TestFreeMagmas.zero $h)
  | s + 1 =>
    let h := proveTestAllSplits s fun s1 s2 : Nat =>
      proveTestFreeMagmas s1 n q(fun n l => TestFreeMagmas $s2 n fun n r => $P n (.Fork l r))
        fun n l l' => proveTestFreeMagmas s2 n q(fun n r => $P n (.Fork $l' r))
          fun n r r' => hP n (.Fork l r) q(.Fork $l' $r')
    q(TestFreeMagmas.succ $h)

def TestLawsBody (l r : FreeMagma Nat) (P : Law.NatMagmaLaw → Prop) :=
  (l = r → l = Lf 0) →
  ¬(l ≃ r).symm.canonicalize.comp (l ≃ r) = .lt → P (l ≃ r)

theorem TestLawsBody.mk1 {l r P}
    (H : (l ≃ r).symm.canonicalize.comp (l ≃ r) = .lt) : TestLawsBody l r P :=
  fun _ h => h.elim H

theorem TestLawsBody.mk2 {l r P} (H : P (l ≃ r)) : TestLawsBody l r P :=
  fun _ _ => H

theorem TestLawsBody.mk3 {l P} (h1 : decide (l = Lf 0) = false) : TestLawsBody l l P :=
  fun h => by simp at h1; cases h1 (h rfl)

partial def proveTestLawsBody (l r : FreeMagma Nat) (l' r' : Q(FreeMagma Nat))
    (P : Q(Law.NatMagmaLaw → Prop))
    (hP : (l : Law.NatMagmaLaw) → (l : Q(Law.NatMagmaLaw)) → Q($P $l)) :
    Q(TestLawsBody $l' $r' $P) :=
  let law := (l ≃ r)
  let e := l.comp r
  if l = .Leaf 0 || e ≠ .eq then
    if law.symm.canonicalize.comp law = .lt then
      let e : Q(($l' ≃ $r').symm.canonicalize.comp ($l' ≃ $r') = .lt) := (q(Eq.refl Ordering.lt) :)
      q(TestLawsBody.mk1 $e)
    else
      q(TestLawsBody.mk2 $(hP law q($l' ≃ $r')))
  else
    have : $l' =Q $r' := ⟨⟩
    let h1 : Q(decide ($l' = Lf 0) = false) := (q(Eq.refl false) :)
    q(TestLawsBody.mk3 $h1)

def TestLaws (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks = s → l.IsCanonical → P l

theorem TestLaws.mk {s P}
    (H : TestAllSplits s fun s1 s2 =>
    TestFreeMagmas s1 0 fun n l =>
      TestFreeMagmas s2 n fun _ r =>
        TestLawsBody l r P)
    : TestLaws s P := by
  unfold TestLaws
  simp [TestAllSplits, TestFreeMagmas] at *
  rintro ⟨l, r⟩ hs hcan
  obtain ⟨⟨n'', n', hcan1, hcan2⟩, hcomp, hsymm⟩ := hcan
  exact H _ _ hs _ _ rfl hcan1 _ _ rfl hcan2 hcomp hsymm

partial def proveTestLaws (s : Nat) (P : Q(Law.NatMagmaLaw → Prop))
    (hP : Law.NatMagmaLaw → (m : Q(Law.NatMagmaLaw)) → Q($P $m)) :
    Q(TestLaws $s $P) :=
  let h := proveTestAllSplits s fun s1 s2 : Nat =>
    proveTestFreeMagmas s1 0 q(fun n l => TestFreeMagmas $s2 n fun _ r => TestLawsBody l r $P)
      fun n l l' => proveTestFreeMagmas s2 n q(fun _ r => TestLawsBody $l' r $P)
        fun _ r r' => proveTestLawsBody l r l' r' P hP
  q(TestLaws.mk $h)

def TestLawsUpto (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks ≤ s → l.IsCanonical → P l

theorem TestLawsUpto.mk {s P}
    (H : TestNat (s+1) fun s' => TestLaws s' P)
    : TestLawsUpto s P := by
  simp [TestLawsUpto, TestLaws, TestNat, Nat.lt_succ_iff] at *
  intro i his hcanon
  exact H _ his _ rfl hcanon

partial def proveTestLawsUpto (s : Nat) (P : Q(Law.NatMagmaLaw → Prop))
    (hP : Law.NatMagmaLaw → (m : Q(Law.NatMagmaLaw)) → Q($P $m)) :
    Q(TestLawsUpto $s $P) :=
  let h := proveTestNat (s+1) fun s' : Nat => proveTestLaws s' P hP
  q(TestLawsUpto.mk $h)

/--
This theorem demonstrates that `laws`, the list of laws considered in this project, indeed
contains all (canonically represented) magma laws up to 4 operations.
-/
theorem laws_complete :
    ∀ l : Law.MagmaLaw Nat, l.forks ≤ 4 → l.IsCanonical → ∃ (i : Nat), laws[i] = l :=
  by_elab pure <| proveTestLawsUpto 4 q(fun l => ∃ i : Nat, laws[i] = l) fun l l' =>
    let i : Nat := findMagmaLaw l
    let h : Q(laws[$i] = $l') := (q(Eq.refl $l') :)
    q(⟨$i, $h⟩)

/--
This theorem demonstrates that `laws`, the list of laws considered in this project, indeed
contains all magma laws up to equivalence, up to 4 operations.
-/
theorem laws_complete' (l : Law.MagmaLaw Nat) (hl : l.forks ≤ 4) : ∃ (i : Nat), laws[i].iff l := by
  have ⟨l', h1, h2, h3⟩ := l.exists_canonical
  obtain ⟨i, rfl⟩ := laws_complete l' (h2.trans hl) h1
  exact ⟨i, h3.symm⟩
