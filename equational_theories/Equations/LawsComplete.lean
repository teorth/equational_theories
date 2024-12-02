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
  let consts : _root_.RArray Expr := RArray.ofFn (h := by omega) fun (⟨i, _⟩ : Fin 4694) =>
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

@[simp] theorem Ordering.lt_then (o) : Ordering.lt.then o = .lt := rfl
@[simp] theorem Ordering.eq_then (o) : Ordering.eq.then o = o := rfl
@[simp] theorem Ordering.gt_then (o) : Ordering.gt.then o = .gt := rfl
@[simp] theorem Ordering.then_swap_self (o : Ordering) : o.then o.swap = o := by cases o <;> rfl

theorem Ordering.then_assoc (o₁ o₂ o₃ : Ordering) :
    (o₁.then o₂).then o₃ = o₁.then (o₂.then o₃) := by cases o₁ <;> rfl

def FreeMagma.cmpShape {α β} (l1 : FreeMagma α) (l2 : FreeMagma β) : Ordering :=
  (compare l1.forks l2.forks).then <|
    match l1, l2 with
    | .Leaf _,     .Leaf _     => .eq
    | .Leaf _,     .Fork _ _   => .lt
    | .Fork _ _,   .Leaf _     => .gt
    | .Fork l1 r1, .Fork l2 r2 => (l1.cmpShape l2).then (r1.cmpShape r2)

theorem FreeMagma.cmpShape_swap {α β} (l1 : FreeMagma α) (l2 : FreeMagma β) :
    (l1.cmpShape l2).swap = l2.cmpShape l1 := by
  rw [FreeMagma.cmpShape.eq_def, FreeMagma.cmpShape.eq_def]
  simp [Ordering.swap_then, Nat.compare_swap]
  split <;> first | rfl | rw [Ordering.swap_then, FreeMagma.cmpShape_swap, FreeMagma.cmpShape_swap]

theorem FreeMagma.cmpShape_map_left {α β γ} (l1 : FreeMagma α) (l2 : FreeMagma γ) (f : α → β) :
    (fmapHom f l1).cmpShape l2 = l1.cmpShape l2 := by
  induction l1 generalizing l2 <;> rw [cmpShape.eq_def, cmpShape.eq_def, map_forks] <;> congr <;>
    cases l2 <;> simp [fmapHom] at * <;> simp [evalInMagma, cmpShape, *]

theorem FreeMagma.cmpShape_map_right {α β γ} (l1 : FreeMagma α) (l2 : FreeMagma β) (f : β → γ) :
    l1.cmpShape (fmapHom f l2) = l1.cmpShape l2 := by
  rw [← cmpShape_swap, cmpShape_map_left, cmpShape_swap]

def List.cmp {α} [Ord α] : List α → List α → Ordering
  | [], [] => .eq
  | [], _::_ => .lt
  | _::_, [] => .gt
  | a::as, b::bs => (compare a b).then (List.cmp as bs)

instance {α} [Ord α] : Ord (List α) := ⟨List.cmp⟩

theorem List.cmp_eq_eq {α} [LinearOrder α] {l1 l2 : List α} :
    l1.cmp l2 = .eq ↔ l1 = l2 := by
  induction l1 generalizing l2 <;> cases l2 <;>
    simp [List.cmp, Ordering.then_eq_eq, compare_eq_iff_eq, *]

theorem List.cmp_swap {α} [LinearOrder α] (l1 l2 : List α) :
    (l1.cmp l2).swap = l2.cmp l1 := by
  rw [List.cmp.eq_def, List.cmp.eq_def]
  split <;> first | rfl | rw [Ordering.swap_then, Batteries.OrientedCmp.symm, List.cmp_swap]

theorem List.cmp_append {α} [LinearOrder α] : ∀ {l1 l2 r1 r2 : List α}, l1.length = r1.length →
    (l1 ++ l2).cmp (r1 ++ r2) = (l1.cmp r1).then (l2.cmp r2)
  | [], l2, [], r2, _ => by simp [List.cmp]
  | a::l1, l2, b::r1, r2, h => by
    simp [List.cmp, Ordering.then_assoc, List.cmp_append (Nat.succ_inj.1 h)]


/-- An ordering on `FreeMagma` that coincides with the order we put the laws in.  -/
def FreeMagma.cmp {α} [LinearOrder α] (m1 m2 : FreeMagma α) : Ordering :=
  (m1.cmpShape m2).then (m1.toList.cmp m2.toList)

theorem FreeMagma.cmp_swap {α} [LinearOrder α] (l1 l2 : FreeMagma α) :
    (l1.cmp l2).swap = l2.cmp l1 := by
  simp [cmp, Ordering.swap_then, Nat.compare_swap, cmpShape_swap, List.cmp_swap]

theorem FreeMagma.cmpShape_length_eq.{u} {α β : Type u} [DecidableEq α]
    {m : FreeMagma α} {m' : FreeMagma β} (h : m.cmpShape m' = .eq) : m.length = m'.length := by
  induction' m with _ _ _ ih1 ih2 generalizing m' <;> cases m' <;>
    simp [cmpShape, Ordering.then_eq_eq] at h <;> simp
  rw [ih1 h.2.1, ih2 h.2.2]

theorem FreeMagma.eq_of_cmpShape_toList_eq {α} [LinearOrder α] {l1 l2 : FreeMagma α}
    (h1 : l1.cmpShape l2 = .eq) (h2 : l1.toList = l2.toList) : l1 = l2 := by
  induction' l1 with _ l1 r1 ih1 ih2 generalizing l2 <;> cases' l2 with _ l2 r2 <;>
    simp_all [evalInMagma, cmpShape, Ordering.then_eq_eq]
  have := List.append_inj h2 (by simpa [toList_length] using cmpShape_length_eq h1.2.1)
  simp [ih1 h1.2.1 this.1, ih2 h1.2.2 this.2]

theorem FreeMagma.cmp_eq_eq {α} [LinearOrder α] (l1 l2 : FreeMagma α) :
    l1.cmp l2 = .eq ↔ l1 = l2 := by
  cases e : l1.cmp l2 with
  | lt | gt => simp; rintro rfl; cases e ▸ FreeMagma.cmp_swap l1 l1
  | eq =>
    simp; simp [cmp, Ordering.then_eq_eq] at e
    exact FreeMagma.eq_of_cmpShape_toList_eq e.1 (List.cmp_eq_eq.1 e.2)

/-- The number of forks in a magma law. -/
def Law.MagmaLaw.forks {α} (l : Law.MagmaLaw α) : Nat :=
  l.lhs.forks + l.rhs.forks

def Law.MagmaLaw.cmpShape {α β} (l1 : Law.MagmaLaw α) (l2 : Law.MagmaLaw β) : Ordering :=
 (FreeMagma.cmpShape l1.lhs l2.lhs).then (FreeMagma.cmpShape l1.rhs l2.rhs)

/-- An ordering on `NatMagmaLaw` that coincides with the order we put the laws in.  -/
def Law.MagmaLaw.cmp {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) : Ordering :=
  (compare l1.forks l2.forks).then <| (l1.cmpShape l2).then (l1.toList.cmp l2.toList)

theorem Law.MagmaLaw.cmpShape_swap {α β} (l1 : Law.MagmaLaw α) (l2 : Law.MagmaLaw β) :
    (l1.cmpShape l2).swap = l2.cmpShape l1 := by
  simp [cmpShape, Ordering.swap_then, FreeMagma.cmpShape_swap]

theorem Law.MagmaLaw.cmpShape_map_left {α β γ}
    (l1 : Law.MagmaLaw α) (l2 : Law.MagmaLaw γ) (f : α → β) :
    (l1.map f).cmpShape l2 = l1.cmpShape l2 := by
  simp [map, cmpShape, FreeMagma.cmpShape_map_left]

theorem Law.MagmaLaw.cmpShape_map_right {α β γ}
    (l1 : Law.MagmaLaw α) (l2 : Law.MagmaLaw β) (f : β → γ) :
    l1.cmpShape (l2.map f) = l1.cmpShape l2 := by
  rw [← cmpShape_swap, cmpShape_map_left, cmpShape_swap]

theorem Law.MagmaLaw.cmp_swap {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) :
    (l1.cmp l2).swap = l2.cmp l1 := by
  simp [cmp, Ordering.swap_then, Nat.compare_swap, cmpShape_swap, List.cmp_swap]

theorem Law.MagmaLaw.cmp_eq_eq {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) :
    l1.cmp l2 = .eq ↔ l1 = l2 := by
  cases e : l1.cmp l2 with
  | lt | gt => simp; rintro rfl; cases e ▸ Law.MagmaLaw.cmp_swap l1 l1
  | eq =>
    simp; simp [cmp, cmpShape, Ordering.then_eq_eq, List.cmp_eq_eq, toList] at e
    have := List.append_inj e.2.2 <| by
      simpa [FreeMagma.toList_length] using FreeMagma.cmpShape_length_eq e.2.1.1
    ext <;> apply FreeMagma.eq_of_cmpShape_toList_eq <;> simp [*]

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
      if l.cmp l' = .lt then
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
  go : FreeMagma α → Array α → FreeMagma Nat × Array α
  | .Leaf v, xs =>
    match xs.indexOf? v with
    | some i => (.Leaf i, xs)
    | none =>
      (.Leaf xs.size, xs.push v)
  | .Fork l r, xs =>
    let (l, xs) := go l xs
    let (r, xs) := go r xs
    (.Fork l r, xs)

def List.canonicalize {α} [DecidableEq α] (l : List α) : List Nat :=
  (go l []).1
where
  go : List α → List α → List Nat × List α
  | [], xs => ([], xs)
  | v :: l, xs =>
    match xs.indexOf? v with
    | some i => let (l', xs) := go l xs; (i::l', xs)
    | none => let (l', xs') := go l (xs ++ [v]); (xs.length :: l', xs')

theorem List.canonicalize.go_append {α} [DecidableEq α]
    {l₁ l₂ : List α} {l₁' l₂' xs₁ xs₂ xs₃}
    (H₁ : go l₁ xs₁ = (l₁', xs₂)) (H₂ : go l₂ xs₂ = (l₂', xs₃)) :
    go (l₁ ++ l₂) xs₁ = (l₁' ++ l₂', xs₃) := by
  induction' l₁ with _ _ ih generalizing xs₁ l₁' xs₂ <;> simp [List.canonicalize.go] at H₁ ⊢
  · simp [H₁, H₂]
  · revert H₁; split <;> (cases e : go (α := α) ..; rintro ⟨⟩; rw [ih e H₂]; rfl)

/-- Canonically reorders variables -/
def Law.MagmaLaw.canonicalize {α} [DecidableEq α] (l : Law.MagmaLaw α) : Law.MagmaLaw Nat :=
  (go #[]).1
where
  go (arr : Array α) : Law.NatMagmaLaw × Array α :=
    let (lhs', arr) := FreeMagma.canonicalize.go l.lhs arr
    let (rhs', arr) := FreeMagma.canonicalize.go l.rhs arr
    (⟨lhs', rhs'⟩, arr)

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
  (l.lhs.cmp l.rhs = .lt ∨ l.lhs = .Leaf 0) ∧
  l.symm.canonicalize.cmp l ≠ .lt

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
  lt_of_not_le fun h => by simp [List.getElem?_eq_none h] at H

theorem FreeMagma.canonicalize_prop {α} [DecidableEq α]
    {m : FreeMagma α} {xs : List α}
    {m' xs'} (H : FreeMagma.canonicalize.go m ⟨xs⟩ = (m', ⟨xs'⟩)) :
    m'.isCanonical xs.length = some xs'.length ∧
    List.canonicalize.go m.toList xs = (m'.toList, xs') ∧
    (xs.Nodup → xs'.Nodup) ∧
    (∀ (i:Nat) a, xs[i]? = some a → xs'[i]? = some a) ∧
    (∀ f, (∀ i a, xs'[i]? = some a → f a = i) → fmapHom f m = m') ∧
    (∀ f, (∀ i a, xs'[i]? = some a → f i = a) → fmapHom f m' = m) := by
  induction m generalizing xs m' xs' with
  | Leaf v =>
    simp [canonicalize.go_leaf, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get] at H
    revert H; cases' e : xs.indexOf? v with i <;> rintro ⟨⟩ <;>
      simp only [isCanonical, Array.size_toArray, lt_self_iff_false, ↓reduceIte, pure, Array.size,
        List.length_append, List.length_singleton, Fin.getElem_fin, List.getElem_toArray, true_and,
        ite_eq_left_iff, not_lt, Option.ite_none_right_eq_some, Option.some.injEq,
        Nat.succ_ne_self, and_false, imp_false, not_le, Fin.is_lt, exists_const, implies_true]
    · refine ⟨?_, fun H => ?_, fun i a h => ?_, ?_⟩
      · simp [List.canonicalize.go, e]
      · simp [List.nodup_append, H]
        simpa using List.indexOf?_eq_none_iff.1 e v
      · rwa [List.getElem?_append_left (List.lt_len_of_getElem? h)]
      · constructor <;> (intro _ hf; simp [fmapHom, evalInMagma]; apply hf; simp)
    · have := List.getElem?_of_indexOf? e
      exact ⟨List.lt_len_of_getElem? this, by simp [List.canonicalize.go, e], id, fun _ _ => id,
        fun f hf => congrArg Lf (hf _ _ this), fun f hf => congrArg Lf (hf _ _ this)⟩
  | Fork l r ihl ihr =>
    simp (config := {iota := false}) only [canonicalize.go] at H
    split at H; split at H; cases H; rename_i m1 arr1 eq1 _ m2 eq2
    let ⟨ihl1, ihl2, ihl3, ihl4, ihl5, ihl6⟩ := ihl eq1
    let ⟨ihr1, ihr2, ihr3, ihr4, ihr5, ihr6⟩ := ihr eq2
    refine ⟨?_, List.canonicalize.go_append ihl2 ihr2, ihr3 ∘ ihl3,
      fun _ _ => ihr4 _ _ ∘ ihl4 _ _, fun f hf => ?_, fun f hf => ?_⟩
    · rw [isCanonical, Option.bind_eq_bind, ihl1, Option.some_bind, ihr1]
    · exact congr (congrArg Fork (ihl5 _ fun _ _ => hf _ _ ∘ ihr4 _ _)) (ihr5 _ hf)
    · exact congr (congrArg Fork (ihl6 _ fun _ _ => hf _ _ ∘ ihr4 _ _)) (ihr6 _ hf)

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
        have ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 this
        simp [List.getElem_range] at e; simp_all
    simp [isCanonical] at can; split at can
    · cases can; rw [this]; split_ifs; simp [pure, StateT.pure]
    · simp at can; obtain ⟨rfl, rfl⟩ := can
      simp [this]; congr 2; simp; exact (Array.toList_range _).symm
  | Fork l r ihl ihr =>
    simp [isCanonical, Option.bind_eq_some] at can
    obtain ⟨n', h1, h2⟩ := can
    simp [canonicalize.go, bind, StateT.bind, ihl h1, ihr h2]

theorem Law.MagmaLaw.canonicalize_self {m : Law.MagmaLaw ℕ} (H : m.IsCanonicalLabel) :
    m.canonicalize = m := by
  let ⟨a, b, h1, h2⟩ := H
  simp [canonicalize, canonicalize.go, bind, StateT.bind, show #[] = Array.range 0 by rfl,
    FreeMagma.canonicalize_self h1, FreeMagma.canonicalize_self h2]

theorem Law.MagmaLaw.canonicalize_toList {α} [DecidableEq α] {m : Law.MagmaLaw α} :
    m.canonicalize.toList = m.toList.canonicalize := by
  simp (config := {iota := false, proj := false}) [canonicalize, canonicalize.go]
  split; split; rename_i eq1 _ _ _ eq2
  obtain ⟨-, h1, -⟩ := FreeMagma.canonicalize_prop eq1
  obtain ⟨-, h2, -⟩ := FreeMagma.canonicalize_prop eq2
  simp [pure, StateT.pure, List.canonicalize, toList, List.canonicalize.go_append h1 h2]

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
    revert e1 e2; rw [this]; cases xs₁.indexOf? v <;> simp <;> rintro rfl rfl rfl rfl
    · refine ⟨by rw [H.length_eq], ?_⟩
      rw [← List.forall₂_reverse_iff]; simp [h2, H]
    · simp [H]
  | Fork l r ihl ihr =>
    revert e1 e2
    injection h2 with hl2 hr2
    rw [canonicalize.go]; split; split
    simp (config := {iota := false}) [canonicalize.go]; split; split
    rename_i l1 _ _ _ r1 _ _ _ l2 _ _ _ r2; rintro rfl rfl ⟨⟩
    obtain ⟨rfl, H⟩ := ihl l1 H hl2 l2
    obtain ⟨rfl, H⟩ := ihr r1 H hr2 r2
    exact ⟨rfl, H⟩

theorem Law.MagmaLaw.canonicalize_relabelling {α β} [DecidableEq α] [DecidableEq β]
    {m : Law.MagmaLaw α} {m' : Law.MagmaLaw β}
    {f g} (h1 : m.map f = m') (h2 : m'.map g = m) :
    m.canonicalize = m'.canonicalize := by
  let ⟨l₁, r₁⟩ := m; let ⟨l₂, r₂⟩ := m'; simp [map] at h1 h2
  rw [canonicalize, canonicalize.go]; split; split
  simp (config := {iota := false, proj := false}) [canonicalize, canonicalize.go]; split; split
  rename_i l1 _ _ _ r1 _ _ _ l2 _ _ _ r2
  obtain ⟨rfl, H⟩ := FreeMagma.canonicalize_relabelling h1.1 h2.1 l1 l2 .nil
  obtain ⟨rfl, _⟩ := FreeMagma.canonicalize_relabelling h1.2 h2.2 r1 r2 H
  rfl

theorem Law.MagmaLaw.canonicalize_is_relabelling {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    (∃ f : α → ℕ, m.map f = m.canonicalize) ∧ (∃ g : ℕ → α, m.canonicalize.map g = m) := by
  cases' m with l r; simp (config := {iota := false, proj := false}) [canonicalize, canonicalize.go]
  split; split; rename_i m1 arr1 eq1 _ m2 arr eq2; let ⟨xs1⟩ := arr1; let ⟨xs⟩ := arr
  simp [pure, StateT.pure, map]
  obtain ⟨_, _, l1, -,  l3, l4⟩ := l.canonicalize_prop eq1
  obtain ⟨_, _, r1, r2, r3, r4⟩ := r.canonicalize_prop eq2
  have ⟨g, hg⟩ : ∃ (g : ℕ → α), ∀ i a, xs[i]? = some a → g i = a := by
    have : Inhabited α := ⟨l.first⟩
    exact ⟨fun i => xs[i]!, fun _ _ => List.getElem!_of_getElem?⟩
  have ⟨f, hf⟩ : ∃ (f : α → ℕ), ∀ i a, xs[i]? = some a → f a = i := by
    have (i) (hi : i < xs.length) : g i = xs[Fin.mk i hi] := hg _ _ (List.getElem?_eq_getElem hi)
    have : Set.InjOn g {i | i < xs.length} := fun i hi j hj eq =>
      Fin.val_eq_of_eq <| List.nodup_iff_injective_getElem.1 (r1 (l1 .nil)) <|
        (this i hi).symm.trans <| eq.trans (this j hj)
    refine ⟨Function.invFunOn g {i | i < xs.length}, fun i a h => ?_⟩
    convert Set.InjOn.leftInvOn_invFunOn this (List.lt_len_of_getElem? h); rw [hg _ _ h]
  exact ⟨
    ⟨f, l3 _ fun _ _ => hf _ _ ∘ r2 _ _, r3 _ hf⟩,
    ⟨g, l4 _ fun _ _ => hg _ _ ∘ r2 _ _, r4 _ hg⟩⟩

theorem List.lt_of_lt_canonicalize
    {l r : List ℕ} (H : l.cmp r.canonicalize = .lt) : l.cmp r = .lt :=
  (go (n := 0) rfl).1 H
where
  go {r r' n xs'} (eq : canonicalize.go r (range n) = (r', xs')) :
      (l.cmp r' = .lt → l.cmp r = .lt) ∧
      (l.cmp r = .gt → l.cmp r' = .gt) := by
    clear H; induction r generalizing l r' n xs' with simp [canonicalize.go] at eq
    | nil => obtain ⟨rfl, rfl⟩ := eq; exact ⟨id, id⟩
    | cons a r ih =>
      cases' e : canonicalize.go r (range n) with r₁ xs₁
      split at eq <;> cases eq <;> (cases l <;> [exact ⟨fun _ => rfl, nofun⟩; rename_i i eq v l])
      · have := getElem?_of_indexOf? eq
        simp [List.cmp, Ordering.then_eq_lt, Ordering.then_eq_gt, Nat.compare_eq_lt,
          Nat.compare_eq_gt, Nat.compare_eq_eq]
        have hi := List.lt_len_of_getElem? this; simp at hi
        cases this.symm.trans (getElem?_range hi)
        constructor <;> refine Or.imp_right <| And.imp_right fun h2 => ?_
        · rw [e] at h2; exact (ih e).1 h2
        · rw [e]; exact (ih e).2 h2
      · simp [List.cmp, Ordering.then_eq_lt, Ordering.then_eq_gt, Nat.compare_eq_lt,
          Nat.compare_eq_gt, Nat.compare_eq_eq]
        have := let _ := instBEqOfDecidableEq (α := ℕ); indexOf?_eq_none_iff.1 eq
        simp at this
        have := Nat.le_of_not_lt fun h => this _ h rfl
        constructor <;> rintro (h | ⟨rfl, h⟩)
        · exact .inl <| h.trans_le this
        · refine (lt_or_eq_of_le this).imp_right fun h' => ⟨h', ?_⟩
          exact (ih (n := v+1) rfl).1 (by simpa [h', range_succ] using h)
        · exact .inl <| this.trans_lt h
        · refine (lt_or_eq_of_le this).imp_right fun h' => ⟨h'.symm, ?_⟩
          simpa [h', range_succ] using (ih (n := v+1) rfl).2 h


theorem List.gt_canonicalize_of_gt
    {l r : List ℕ} (H : l.cmp r = .gt) : l.cmp r.canonicalize = .gt :=
  (List.lt_of_lt_canonicalize.go (n := 0) rfl).2 H

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
  cases' m with l r; simp (config := {iota := false, proj := false}) [canonicalize, canonicalize.go]
  split; split; rename_i l' arr1 eq1 _ r' arr eq2
  simp [pure, StateT.pure, map]
  obtain hl := (l.canonicalize_prop eq1).1
  obtain hr := (r.canonicalize_prop eq2).1
  simp at hl; simp [IsCanonicalLabel, hl, hr]

@[simp] theorem Law.MagmaLaw.map_forks {α β} (m : Law.MagmaLaw α) (f : α → β) :
    (m.map f).forks = m.forks := by cases m; simp [map, forks, FreeMagma.map_forks]

@[simp] theorem Law.MagmaLaw.canonicalize_forks {α} [DecidableEq α] (m : Law.MagmaLaw α) :
    m.canonicalize.forks = m.forks := by
  let ⟨h, hf⟩ := m.canonicalize_is_relabelling.1
  rw [← hf, map_forks]

@[simp] theorem Law.MagmaLaw.cmpShape_canonicalize_left {α β} [DecidableEq α]
    (m : Law.MagmaLaw α) (m' : Law.MagmaLaw β) :
    m.canonicalize.cmpShape m' = m.cmpShape m' := by
  let ⟨h, hf⟩ := m.canonicalize_is_relabelling.1
  rw [← hf, cmpShape_map_left]

@[simp] theorem Law.MagmaLaw.cmpShape_canonicalize_right {α β} [DecidableEq β]
    (m : Law.MagmaLaw α) (m' : Law.MagmaLaw β) :
    m.cmpShape m'.canonicalize = m.cmpShape m' := by
  rw [← cmpShape_swap, cmpShape_canonicalize_left, cmpShape_swap]

@[simp] theorem Law.MagmaLaw.symm_forks {α} (m : Law.MagmaLaw α) :
    m.symm.forks = m.forks := by cases m; simp [symm, forks, Nat.add_comm]

theorem Law.MagmaLaw.exists_canonical {α} (m : Law.MagmaLaw α) :
    ∃ m', m'.IsCanonical ∧ m'.forks ≤ m.forks ∧ m.iff m' := by
  classical
  suffices ∀ (m : Law.MagmaLaw α), m.symm.canonicalize.cmp m.canonicalize ≠ .lt →
      ∃ m', m'.IsCanonical ∧ m'.forks ≤ m.forks ∧ m.iff m' by
    by_cases e : m.symm.canonicalize.cmp m.canonicalize = .lt
    · specialize this m.symm
      rw [symm_symm, ← cmp_swap, e] at this
      let ⟨m', h1, h2, h3⟩ := this nofun
      exact ⟨m', h1, symm_forks m ▸ h2, (symm_iff _).trans h3⟩
    · exact this _ e
  intro m e
  by_cases triv : m.canonicalize.lhs = m.canonicalize.rhs
  · have : (Lf 0 ≃ Lf 0).IsCanonicalLabel := ⟨_, _, rfl, rfl⟩
    have can : (Lf 0 ≃ Lf 0).IsCanonical :=
      ⟨this, .inr rfl, by simp [symm, canonicalize_self this]; nofun⟩
    refine ⟨Lf 0 ≃ Lf 0, can, Nat.zero_le _, m.canonicalize_iff.symm.trans ?_⟩
    refine fun G _ => ⟨fun _ _ => rfl, fun _ _ => by simp [satisfiesPhi, triv]⟩
  refine ⟨m.canonicalize, ⟨m.canonicalize_isCanonicalLabel, .inl ?_, ?_⟩, ?_, ?_⟩
  · rw [← canonicalize_symm_canonicalize] at e
    have := m.canonicalize_isCanonicalLabel
    generalize m.canonicalize = m' at e this triv
    replace e := mt (Ordering.swap_eq_iff_eq_swap (o' := .gt)).1 e; rw [cmp_swap] at e
    simp [cmp, Nat.compare_eq_eq.2] at e
    simp [FreeMagma.cmp, Ordering.then_eq_lt]
    let ⟨g, hg⟩ := m'.symm.canonicalize_is_relabelling.1
    simp [Ordering.swap, Ordering.then_eq_gt] at e; obtain ⟨le, e⟩ := e
    cases e1 : m'.cmpShape m'.symm with
    | gt => cases le e1
    | lt =>
      simp [cmpShape, symm] at e1
      rw [← FreeMagma.cmpShape_swap m'.lhs, Ordering.then_swap_self] at e1
      exact .inl e1
    | eq =>
      specialize e e1
      simp [cmpShape, Ordering.then_eq_eq, symm] at e1; simp [e1]
      rw [MagmaLaw.toList, MagmaLaw.toList, List.cmp_append] at e
      · injection id hg with hg1 hg2
        obtain ⟨-, h1, -⟩ := FreeMagma.canonicalize_prop
          (Eq.refl (FreeMagma.canonicalize.go m'.symm.lhs #[]))
        rw [← hg1, FreeMagma.map_toList] at h1
        have : m'.rhs.toList.canonicalize = m'.rhs.toList.map g := congrArg (·.1) h1
        simp [Ordering.then_eq_gt] at e
        have ⟨le, e'⟩ := e
        rw [← hg, map] at le e'; simp [symm, ← this] at le e'
        · cases eq3 : m'.lhs.toList.cmp m'.rhs.toList with
          | lt => rfl
          | eq => cases triv (FreeMagma.eq_of_cmpShape_toList_eq e1.1 ((List.cmp_eq_eq ..).1 eq3))
          | gt => cases le (List.gt_canonicalize_of_gt eq3)
      · simp [FreeMagma.toList_length, ← hg, map]; simp [symm]
        refine FreeMagma.cmpShape_length_eq e1.1
  · rwa [canonicalize_symm_canonicalize]
  · rw [canonicalize_forks]
  · exact m.canonicalize_iff.symm

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
  l.cmp r = .lt ∨ l = Lf 0 →
  ¬(l ≃ r).symm.canonicalize.cmp (l ≃ r) = .lt → P (l ≃ r)

theorem TestLawsBody.mk1 {l r P}
    (H : (l ≃ r).symm.canonicalize.cmp (l ≃ r) = .lt) : TestLawsBody l r P :=
  fun _ h => h.elim H

theorem TestLawsBody.mk2 {l r P} (H : P (l ≃ r)) : TestLawsBody l r P :=
  fun _ _ => H

theorem TestLawsBody.mk3 {l r P}
    (h1 : decide (l = Lf 0) = false) (h2 : decide (l.cmp r = .lt) = false) : TestLawsBody l r P :=
  fun h => by simp at h1 h2; cases h.elim h2 h1

partial def proveTestLawsBody (l r : FreeMagma Nat) (l' r' : Q(FreeMagma Nat))
    (P : Q(Law.NatMagmaLaw → Prop))
    (hP : (l : Law.NatMagmaLaw) → (l : Q(Law.NatMagmaLaw)) → Q($P $l)) :
    Q(TestLawsBody $l' $r' $P) :=
  let law := (l ≃ r)
  if l = .Leaf 0 || l.cmp r = .lt then
    if law.symm.canonicalize.cmp law = .lt then
      let e : Q(($l' ≃ $r').symm.canonicalize.cmp ($l' ≃ $r') = .lt) := (q(Eq.refl Ordering.lt) :)
      q(TestLawsBody.mk1 $e)
    else
      q(TestLawsBody.mk2 $(hP law q($l' ≃ $r')))
  else
    let h1 : Q(decide ($l' = Lf 0) = false) := (q(Eq.refl false) :)
    let h2 : Q(decide (($l').cmp $r' = .lt) = false) := (q(Eq.refl false) :)
    q(TestLawsBody.mk3 $h1 $h2)

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
  obtain ⟨⟨n'', n', hcan1, hcan2⟩, hcmp, hsymm⟩ := hcan
  exact H _ _ hs _ _ rfl hcan1 _ _ rfl hcan2 hcmp hsymm

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
