import equational_theories.Completeness
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.Generated.All4x4Tables.Refutation870
import equational_theories.Generated.FinitePoly.Refutation82

namespace Refutation_854

def G := FreeMagmaWithLaws ℕ {Law854}
instance : Magma G := inferInstanceAs (Magma (FreeMagmaWithLaws ..))

theorem law : ∀ (x y z : G), x = x ◇ ((y ◇ z) ◇ (x ◇ z)) :=
  (Law854.models_iff _).1 <| FreeMagmaWithLaws.isModel _ _ _ rfl

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
    Law.satisfiesSet_singleton.2 <| (Law854.models_iff _).2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l10 : X ≠ X ◇ (Y ◇ X) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l1038'; h2 fun x y => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun | 0 => x | _ => y ◇ (x ◇ y)) <|
    Law.satisfiesSet_singleton.2 <| (Law854.models_iff _).2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l10_2 : Y ≠ Y ◇ (X ◇ Y) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l1038'; h2 fun x y => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun | 1 => x | _ => y ◇ (x ◇ y)) <|
    Law.satisfiesSet_singleton.2 <| (Law854.models_iff _).2 h1
  simpa [MagmaHom.map_op, X, Y, φ] using congrArg φ h

theorem not_l325 : X ◇ Y ≠ X ◇ (Y ◇ X) := by
  refine fun h => let ⟨G, _, h1, h2⟩ := not_l307'; h2 fun x => ?_
  let φ := FreeMagmaWithLaws.evalHom (fun _:ℕ => x) <|
    Law.satisfiesSet_singleton.2 <| (Law854.models_iff _).2 h1
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
