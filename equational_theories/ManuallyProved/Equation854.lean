import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import equational_theories.Completeness
import equational_theories.Generated.All4x4Tables.Refutation870
import equational_theories.Generated.FinitePoly.Refutation82
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.Prod.Lex

namespace Refutation_854

def G := FreeMagmaWithLaws ℕ {Law854}
instance : Magma G := inferInstanceAs (Magma (FreeMagmaWithLaws ..))

theorem law : ∀ (x y z : G), x = x ◇ ((y ◇ z) ◇ (x ◇ z)) :=
  Law854.models_iff.1 <| FreeMagmaWithLaws.isModel _ _ _ rfl

theorem l378 (x y : G) : x ◇ y = (x ◇ y) ◇ y := by
  have yy := (law y y ((y ◇ y) ◇ (y ◇ y))).symm; rw [← law y y y] at yy
  exact (law _ y (y ◇ y)).trans (by rw [yy, ← law])

def Rel (x y : G) := ∃ z, y = z ◇ x
local infix:50 " ⇝ " => Rel

theorem rel_iff {x y} : x ⇝ y ↔ y = y ◇ x := ⟨fun ⟨_, H⟩ => H ▸ l378 .., fun H => ⟨_, H⟩⟩

theorem not_l1038' : ∃ (G : Type) (_ : Magma G), Equation854 G ∧ ¬Equation1038 G :=
  let ⟨G, _, _, h⟩ := «Facts from FinitePoly [[2,3,0,4,0,10,0,10,0,7,7],[1,5,6,1,8,1,8,8,6,1,6],[2,9,6,2,2,2,2,2,9,2,6],[2,3,3,2,3,9,3,9,3,7,7],[4,5,4,4,8,4,5,8,4,4,4],[2,5,5,2,5,9,5,2,5,5,5],[6,5,6,6,8,6,5,8,6,6,6],[4,3,7,4,5,4,5,8,7,7,7],[8,9,6,8,8,8,8,8,9,8,6],[2,9,9,2,9,9,9,9,9,4,4],[2,9,9,2,10,10,10,10,9,2,6]]»
  ⟨G, _, h.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem not_l307' : ∃ (G : Type) (_ : Magma G), Equation854 G ∧ ¬Equation307 G :=
  let ⟨G, _, _, h⟩ := «Facts from FinitePoly x² + x * y % 2»
  have h := h.2.2.2.2.2.2.2.2.2.2.2
  ⟨G, _, h.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

prefix:max "↟" => embed (singleton Law854)

def X : G := ↟(.Leaf 0)
def Y : G := ↟(.Leaf 1)

theorem not_l4 : X ≠ X ◇ Y := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l1038'; h2 fun x y => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun | 0 => x | _ => (y ◇ (x ◇ y)) ◇ x) <|
    Law.satisfiesSet_singleton.2 <| Law854.models_iff.2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l10 : X ≠ X ◇ (Y ◇ X) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l1038'; h2 fun x y => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun | 0 => x | _ => y ◇ (x ◇ y)) <|
    Law.satisfiesSet_singleton.2 <| Law854.models_iff.2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l10_2 : Y ≠ Y ◇ (X ◇ Y) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l1038'; h2 fun x y => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun | 1 => x | _ => y ◇ (x ◇ y)) <|
    Law.satisfiesSet_singleton.2 <| Law854.models_iff.2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l325 : X ◇ Y ≠ X ◇ (Y ◇ X) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l307'; h2 fun x => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun _:ℕ => x) <|
    Law.satisfiesSet_singleton.2 <| Law854.models_iff.2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

inductive Invariant (a b : G) : FreeMagma ℕ → Prop
  | base {a' b'} : a = ↟a' → b = ↟b' → Invariant a b (a' ◇ b')
  | succ {x w} : ↟w ⇝ ↟x → Invariant a b x → Invariant a b (x ◇ w)

theorem unique_factorization {a b c d : G}
    (h1 : a ◇ b = c ◇ d) (h2 : ¬b ⇝ a) (h3 : ¬d ⇝ c) : a = c ∧ b = d := by
  have {L} : {Law854} ⊢' L → (Invariant a b L.lhs ↔ Invariant a b L.rhs) := by
    intro H; induction H with
    | SubstAx h σ =>
      have {x y z} : Invariant a b x ↔ Invariant a b (x ◇ ((y ◇ z) ◇ (x ◇ z))) := by
        constructor <;> intro H
        · exact H.succ ⟨_, law ↟x ↟y ↟z⟩
        · cases H with
          | succ _ h2 => exact h2
          | base ha hb => rw [ha, hb] at h2; cases h2 ⟨_, law ↟x ↟y ↟z⟩
      cases h; apply this
    | Ref => rfl
    | Sym _ ih => exact ih.symm
    | Trans _ _ ih1 ih2 => exact ih1.trans ih2
    | Cong h₁ h₂ ih1 =>
      have {x x' y y'} (hx : ↟x = ↟x') (hy : ↟y = ↟y')
          (h1 : Invariant a b x ↔ Invariant a b x') :
          Invariant a b (x ◇ y) → Invariant a b (x' ◇ y')
      | .base ha hb => .base (ha.trans hx) (hb.trans hy)
      | .succ hl ih => .succ (hx ▸ hy ▸ hl) (h1.1 ih)
      have hx := FreeMagmaWithLaws.eq.2 ⟨h₁⟩
      have hy := FreeMagmaWithLaws.eq.2 ⟨h₂⟩
      exact ⟨this hx hy ih1, this hx.symm hy.symm ih1.symm⟩
  revert h1 h2 h3 this
  refine FreeMagmaWithLaws.inductionOn a fun a => ?_
  refine FreeMagmaWithLaws.inductionOn b fun b => ?_
  refine FreeMagmaWithLaws.inductionOn c fun c => ?_
  refine FreeMagmaWithLaws.inductionOn d fun d h1 h2 h3 this => ?_
  rw [← embed_fork, ← embed_fork, FreeMagmaWithLaws.eq] at h1
  obtain ⟨h1⟩ := h1
  cases (this h1).1 (.base rfl rfl) with
  | base h1 h2 => exact ⟨h1, h2⟩
  | succ h1 h2 => cases h3 h1

@[equational_result]
theorem not_3316_3925 : ∃ (G : Type) (_ : Magma G), Facts G [854] [3316, 3925] := by
  refine ⟨G, inferInstance, law, fun h => ?_, fun h => ?_⟩
  · have := h X Y
    refine not_l10_2 (unique_factorization this (fun h => ?_) (fun h => ?_)).2
    · exact not_l4 (rel_iff.1 h)
    · exact not_l4 ((rel_iff.1 h).trans this.symm)
  · have := h X Y
    refine not_l10 (unique_factorization this (fun h => ?_) (fun h => ?_)).1
    · exact not_l4 (rel_iff.1 h)
    · exact not_l325 (this.trans (rel_iff.1 h).symm)

namespace Greedy
noncomputable section

variable (G) in
abbrev PreExtension := ℕ → ℕ → Set ℕ

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : (ℕ × ℕ) × ℕ | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq854 {x y z xz yz yzxz} : xz ∈ E x z → yz ∈ E y z → yzxz ∈ E yz xz → x ∈ E x yzxz
  eq8 {x xx} : xx ∈ E x x → x ∈ E x xx
  eq101 {x y xy xyx} : xy ∈ E x y → xyx ∈ E xy x → x ∈ E x xyx
  eq46155 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → xy ∈ E xy xxy
  eq378 {x y xy} : xy ∈ E x y → xy ∈ E xy y
  no_idem {x} : x ∉ E x x
  aux {x y xy} : xy ∈ E x y → x ∈ E x xy → x = y
  uniq_fac {x y x' y' xy} : xy ∈ E x y → xy ∈ E x' y' → xy = x ∨ xy = x' ∨ (x, y) = (x', y')
  mono {x y xy} : xy ∈ E x y → xy = x ∨ x < xy ∧ y < xy

variable (G) in
abbrev Extension := {E : PreExtension // E.OK}

class Extension1 where
  E : PreExtension
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace Extension1
variable [Extension1]
local infix:80 " ◯ " => E
def dom : Finset Nat :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

theorem mem_dom {a b c x}
    (h1 : c ∈ a ◯ b) (h2 : x ∈ ({a, b, c} : Finset ℕ)) : x ∈ dom := by
  refine Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem ?_
  simp only [dom, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨_, _, _, h1, h2⟩

theorem dom_l {a b c} (h : c ∈ a ◯ b) : a ∈ dom := mem_dom h (by simp)
theorem dom_r {a b c} (h : c ∈ a ◯ b) : b ∈ dom := mem_dom h (by simp)
theorem dom_o {a b c} (h : c ∈ a ◯ b) : c ∈ dom := mem_dom h (by simp)

theorem dom_a : a ∈ dom := Finset.mem_insert_self ..
theorem dom_b : b ∈ dom := Finset.mem_insert_of_mem <| Finset.mem_insert_self ..

def c : Nat := dom.sup id + 1

theorem lt_c {x} (h : x ∈ dom) : x < c := Nat.lt_succ.2 <| dom.le_sup (f := id) h

local notation x:51 " ≫ " y:51 => y ∈ y ◯ x

inductive Relevant : ℕ → Prop
  | mk {b1 b2} : b ∈ b1 ◯ b2 → b1 ≠ b → b2 ≫ a → Relevant b1

theorem Relevant.unique : ∀ {b1 b1'}, Relevant b1 → Relevant b1' → b1 = b1'
  | _, _, .mk h1 h2 _, .mk h1' h2' _ => by
    cases ok.uniq_fac h1 h1' |>.resolve_left h2.symm |>.resolve_left h2'.symm; rfl

theorem Relevant.lt_b : ∀ {b1}, Relevant b1 → b1 < b
  | _, .mk h1 h2 _ => ((ok.mono h1).resolve_left h2.symm).1

theorem Relevant.ne_a : ∀ {b1}, Relevant b1 → b1 ≠ a
  | _, .mk h1 h2 h3, rfl => h2 (ok.func h3 h1)

inductive Target (p : Prop) : ℕ → Prop
  | protected b : Target p b
  | rel {b1} : p → Relevant b1 → Target p b1

theorem Target.dom {p x} : Target p x → x ∈ dom
  | .b => dom_b
  | .rel _ ⟨h, _, _⟩ => dom_l h

theorem Target.b_nlt {p} : ∀ {x}, Target p x → ¬b < x
  | _, .b => lt_irrefl _
  | _, .rel _ h => h.lt_b.asymm

@[mk_iff]
inductive Extra : ℕ → ℕ → Prop
  | left {b1} : Target (b ≫ b1) b1 → Extra c b1
  | right {x} : Target True x → Extra x c

inductive Next : ℕ → ℕ → ℕ → Prop
  | base {x y z} : z ∈ x ◯ y → Next x y z
  | new : Next a b c
  | extra {x y} : Extra x y → Next x y x

abbrev next : PreExtension := fun a b => {c | Next a b c}

theorem Next.eq8 {x xx : ℕ} (h : Next x x xx) : Next x xx x := by
  let ⟨x', eq, h⟩ : ∃ x', x = x' ∧ Next x x' xx := ⟨_, rfl, h⟩
  match h with
  | .base h => exact .base (ok.eq8 (eq ▸ h))
  | .extra h => assumption
  | .new => exact .extra (eq ▸ .right .b)

theorem Next.ne_c {x y z} : Next x y z → x = c → y ≠ c
  | .base h, h1, _ => (lt_c (dom_l h)).ne h1
  | .new, h1, _ => (lt_c dom_a).ne h1
  | .extra (.left h), _, h1
  | .extra (.right h), h1, _ => (lt_c h.dom).ne h1

theorem Next.no_idem {x} : ¬Next x x x := by
  suffices ∀ y z, Next x y z → x = y → z ≠ x from (this _ _ · rfl rfl)
  rintro y z (h|_|h|h) e1 e2
  · exact ok.no_idem (e1 ▸ e2 ▸ h)
  · cases (lt_c dom_a).ne' e2
  · cases (lt_c h.dom).ne' e1
  · cases (lt_c h.dom).ne e1

theorem next_ok : next.OK where
  finite := by
    have : {b | Relevant b}.Subsingleton := fun _ h1 _ h2 => h1.unique h2
    have : {b | ∃ p, Target p b}.Finite :=
      (this.finite.insert b).subset fun b => by simp; rintro _ ⟨⟩ <;> simp [*]
    refine (ok.finite.union <| .insert ((a, b), c) (this.biUnion fun b _ =>
      Finset.finite_toSet {((b, c), b), ((c, b), c)})).subset fun ((x,y),z) hx => ?_
    simp at hx ⊢; cases hx with
    | extra hx => right; right; cases hx <;> exact ⟨_, ⟨_, ‹_›⟩, by simp⟩
    | _ => simp [*]
  func {x y xy} hxy {xy'} hxy' := by
    match hxy, hxy' with
    | .base hxy, .base hxy' => exact ok.func hxy hxy'
    | .new, .new | .extra _, .extra _ => rfl
    | .new, .base h | .base h, .new => cases not_def h
    | .new, .extra h | .extra h, .new =>
      obtain ⟨_, h⟩ | ⟨_, h⟩ := (extra_iff ..).1 h
      · cases (lt_c dom_a).ne h
      · cases (lt_c dom_b).ne h
    | .base h1, .extra h2 | .extra h2, .base h1 =>
      obtain ⟨_, h2⟩ | ⟨_, h2⟩ := (extra_iff ..).1 h2
      · cases (lt_c (dom_l h1)).ne h2
      · cases (lt_c (dom_r h1)).ne h2
  mono := by
    rintro _ _ _ (h|_|h)
    · exact ok.mono h
    · exact .inr ⟨lt_c dom_a, lt_c dom_b⟩
    · exact .inl rfl
  uniq_fac {x y x' y' xy} h h' := by
    match h, h' with
    | .base h, .base h' => exact ok.uniq_fac h h'
    | .base h, .new | .new, .base h => cases (lt_c (dom_o h)).ne rfl
    | .new, .new => exact .inr <| .inr rfl
    | .extra h, _ => exact .inl rfl
    | _, .extra h => exact .inr <| .inl rfl
  no_idem := Next.no_idem
  eq8 := Next.eq8
  eq101 {x y xy xyx} h1 h2 := by
    obtain h1 | _ | h1 := h1
    · obtain h2 | _ | _ | _ := h2
      · exact .base (ok.eq101 h1 h2)
      · exact .extra (.right .b)
      · cases (lt_c (dom_o h1)).ne rfl
      · cases (lt_c (dom_l h1)).ne rfl
    · generalize ec : c = c', ea : a = a' at h2
      obtain h | _ | (_ | ⟨_, h⟩) | h := h2
      · cases (lt_c (dom_l h)).ne' ec
      · exact .extra (.right .b)
      · exact .extra (.right .b)
      · cases h.ne_a ea.symm
      · cases (lt_c h.dom).ne' ec
    · exact h2.eq8
  eq46155 {x y xy xxy} h1 h2 := by
    obtain h1 | _ | h1 := h1
    · obtain h2 | _ | _ | _ := h2
      · exact .base (ok.eq46155 h1 h2)
      · exact .extra (.right .b)
      · cases (lt_c (dom_l h1)).ne rfl
      · cases (lt_c (dom_o h1)).ne rfl
    · generalize ec : c = c', ea : a = a' at h2
      obtain h | _ | (_ | h) | _ | ⟨-, h⟩ := h2
      · cases (lt_c (dom_r h)).ne' ec
      · exact .extra (.right .b)
      · cases (lt_c dom_a).ne ea
      · cases (lt_c (dom_o h)).ne' ec
      · exact .extra (.left .b)
      · cases h.ne_a ea.symm
    · exact h2.eq8
  eq378 {x y xy} h := by
    obtain h | _ | h := h
    · exact .base (ok.eq378 h)
    · exact .extra (.left .b)
    · exact .extra h
  aux {x y xy} h1 h2 := by
    obtain ⟨x₁, x₂, xy', ex₁, ex₂, exy, h2'⟩ :
      ∃ x₁ x₂ xy', x = x₁ ∧ x = x₂ ∧ xy = xy' ∧ Next x₂ xy' x₁ := ⟨_, _, _, rfl, rfl, rfl, h2⟩
    obtain h1 | _ | h1 | h1 := h1
    · obtain h2 | _ | h2 | h2 := h2'
      · exact ok.aux h1 (ex₁.symm ▸ ex₂ ▸ exy ▸ h2 :)
      · cases (lt_c (dom_l h1)).ne ex₁
      · cases (lt_c (dom_l h1)).ne ex₁
      · cases (lt_c (dom_o h1)).ne exy
    · obtain h2 | _ | h2 | _ | ⟨-, h2⟩ := h2'
      · cases (lt_c (dom_r h2)).ne' exy
      · cases (lt_c dom_b).ne' exy
      · cases (lt_c dom_a).ne ex₁
      · exact ex₁
      · cases h2.ne_a ex₁.symm
    · cases h2.ne_c rfl rfl
    · cases h2.no_idem
  eq854 {x y z xz yz yzxz} h1 h2 h3 := by
    obtain h1 | _ | h1 | h1 := h1
    · obtain h2 | _ | h2 | h2 := h2
      · obtain h3 | _ | h3 | h3 := h3
        · exact .base (ok.eq854 h1 h2 h3)
        · by_cases h : x = b
          · exact .extra (.right (h ▸ .b))
          · exact .extra (.right (.rel trivial ⟨h1, h, ok.eq378 h2⟩))
        · cases (lt_c (dom_o h2)).ne rfl
        · cases (lt_c (dom_o h1)).ne rfl
      · generalize ec : c = c' at h3
        obtain h3 | _ | (_ | ⟨h3, h4⟩) | h3 := h3
        · cases (lt_c (dom_l h3)).ne' ec
        · cases (lt_c dom_a).ne' ec
        · cases ok.no_idem (ok.eq378 h1)
        · cases (ok.mono h1).resolve_right (h4.lt_b.asymm ·.2)
          exact .extra (.right (.rel trivial h4))
        · cases (lt_c (dom_o h1)).ne rfl
      · generalize ec : c = c' at h3
        obtain h3 | _ | (_ | ⟨h3, h4⟩) | h3 := h3
        · cases (lt_c (dom_l h3)).ne' ec
        · cases (lt_c dom_a).ne' ec
        · have := ok.eq378 h1
          obtain _ | ⟨h21, h22, h23, h24⟩ := h2
          · cases ok.no_idem this
          · obtain rfl | h5 := ok.uniq_fac h1 h22
            · exact .extra (.right .b)
            · cases h5.resolve_left h23.symm
              exact .extra (.right (.rel trivial ⟨h22, h23, h24⟩))
        · obtain rfl | ⟨_, hl⟩ := ok.mono h1
          · exact .extra (.right (.rel trivial h4))
          · obtain _ | ⟨_, h2⟩ := h2
            · cases h4.lt_b.asymm hl
            · cases hl.ne (h2.unique h4)
        · cases (lt_c (dom_o h1)).ne rfl
      · cases (lt_c (dom_r h1)).ne rfl
    · obtain h2 | _ | h2 := h2
      · generalize ec : c = c' at h3
        obtain h3 | _ | h3 | h3 := h3
        · cases (lt_c (dom_r h3)).ne' ec
        · cases (lt_c dom_b).ne' ec
        · cases (lt_c h3.dom).ne' ec
        · cases (ok.mono h2).resolve_right (h3.b_nlt ·.2)
          obtain h3 | ⟨-, h31, _, h33⟩ := h3
          · cases ok.no_idem h2
          · cases ok.aux h31 h2; exact .base h33
      · cases h3.ne_c rfl rfl
      · generalize ec : b = b' at h2
        obtain h2 | h2 := h2
        · cases h3.ne_c rfl rfl
        · cases (lt_c dom_b).ne ec
    · obtain h2 | _ | h2 | h2 := h2
      · generalize ec : c = c' at h3
        obtain h3 | _ | h3 | _ | ⟨-, h3⟩ := h3
        · cases (lt_c (dom_r h3)).ne' ec
        · cases (lt_c dom_b).ne' ec
        · cases (lt_c (dom_o h2)).ne rfl
        · exact .extra (.left .b)
        · have := ok.eq378 h2
          obtain _ | ⟨_, h1⟩ := h1
          · exact .extra (.left (.rel this h3))
          · cases h1.unique h3; cases ok.no_idem this
      · cases h3.ne_c rfl rfl
      · cases h3.ne_c rfl rfl
      · cases (lt_c h1.dom).ne rfl
    · generalize ec : c = c' at h2
      obtain h2 | _ | h2 | h2 := h2
      · cases (lt_c (dom_r h2)).ne' ec
      · cases (lt_c dom_b).ne' ec
      · cases (lt_c h2.dom).ne' ec
      · obtain h3 | _ | h3 | h3 := h3
        · match h1, h2 with
          | .b, .b => exact .base (ok.eq8 h3)
          | .rel _ h1, .rel _ h2 => cases h1.unique h2; exact .base (ok.eq8 h3)
          | .rel _ ⟨h1, _, _⟩, .b => exact .base (ok.eq101 h1 h3)
          | .b, .rel _ ⟨h2, _, _⟩ => exact .base (ok.eq46155 h2 h3)
        · exact .extra (.right .b)
        · cases (lt_c h2.dom).ne' ec
        · cases (lt_c h1.dom).ne' ec

end Extension1

variable (e₀ : Extension)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y z, x = op x (op (op y z) (op x z))) ∧
    (∀ {x y}, op x (op x y) = x → x = y) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
      let E1 : Extension1 := { E, ok, a, b, not_def := fun h' => h ⟨_, h'⟩ }
      exact ⟨⟨E1.next, E1.next_ok⟩, fun _ _ _ => (.base ·), _, .new⟩
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y z => ?_, fun {x y} h => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x,z), (y,z), (op y z, op x z), (x, op (op y z) (op x z))}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xz, yz, yzxz, xyzxz⟩ := le
    exact e.2.func (e.2.eq854 xz yz yzxz) xyzxz
  · let S : Finset _ := {(x,y), (x, op x y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, xxy⟩ := le
    rw [h] at xxy
    exact e.2.aux xy xxy
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem Extension.eq854 : Equation854 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1

theorem Extension.aux : ∀ {x y : GreedyMagma e₀}, x ◇ (x ◇ y) = x → x = y :=
  (exists_extension e₀).choose_spec.2.1

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq854 : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 →
      ∀ c ∈ S, c.1 = (b.2, a.2) → ((a.1.1, c.2), a.1.1) ∈ S := by decide)
    (eq8 : ∀ a ∈ S, a.1.1 = a.1.2 → ((a.1.1, a.2), a.1.1) ∈ S := by decide)
    (eq101 : ∀ a ∈ S, ∀ b ∈ S, a.2 = b.1.1 → a.1.1 = b.1.2 → ((a.1.1, b.2), a.1.1) ∈ S := by decide)
    (eq46155 : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a.2 = b.1.2 → ((a.2, b.2), a.2) ∈ S := by decide)
    (eq378 : ∀ a ∈ S, ((a.2, a.1.2), a.2) ∈ S := by decide)
    (no_idem : ∀ a ∈ S, a.1.1 = a.2 → a.1.2 ≠ a.2 := by decide)
    (aux : ∀ a ∈ S, a.1.1 ≠ a.1.2 → ((a.1.1, a.2), a.1.1) ∉ S := by decide)
    (uniq_fac : ∀ a ∈ S, a.2 ≠ a.1.1 → ∀ b ∈ S, a.2 = b.2 → a.2 = b.1.1 ∨ a.1 = b.1 := by decide)
    (mono : ∀ a ∈ S, a.2 = a.1.1 ∨ a.1.1 < a.2 ∧ a.1.2 < a.2 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  eq854 h1 h2 h3 := eq854 _ h1 _ h2 rfl _ h3 rfl
  eq8 h1 := eq8 _ h1 rfl
  eq101 h1 h2 := eq101 _ h1 _ h2 rfl rfl
  eq46155 h1 h2 := eq46155 _ h1 _ h2 rfl rfl
  eq378 h1 := eq378 _ h1
  no_idem h1 := no_idem _ h1 rfl rfl
  aux h1 h2 := Decidable.by_contra (aux _ h1 · h2)
  uniq_fac h1 h2 := Decidable.or_iff_not_imp_left.2 fun h => uniq_fac _ h1 h _ h2 rfl
  mono h1 := mono _ h1


theorem fromList_eval {e : Extension} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (a b c : Nat) (h : ((a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Extension.base e (hS ▸ h)).symm

end
end Greedy

open Greedy

@[equational_result]
theorem not_413_1045 : ∃ (G : Type) (_ : Magma G), Facts G [854] [413, 1045] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    [((0,0),2), ((0,1),0), ((0,2),0), ((1,2),3), ((2,0),2), ((2,1),2), ((2,3),2), ((3,2),3)] :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq854, fun h => ?_, fun h => ?_⟩
  · have := h 1 2
    rw [fromList_eval he 2 1 2, fromList_eval he 1 2 3] at this
    cases e.aux this.symm
  · have := h 1 0
    rw [fromList_eval he 0 1 0, fromList_eval he 0 0 2,
        fromList_eval he 2 1 2, fromList_eval he 1 2 3] at this
    cases this
