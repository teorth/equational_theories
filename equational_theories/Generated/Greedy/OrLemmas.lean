variable {p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q : Prop}

theorem Or.assoc2 (h : (p1 ∨ p2) ∨ q) : p1 ∨ p2 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc3 (h : (p1 ∨ p2 ∨ p3) ∨ q) : p1 ∨ p2 ∨ p3 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc4 (h : (p1 ∨ p2 ∨ p3 ∨ p4) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc5 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc6 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc7 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc8 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc9 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ p9) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ p9 ∨ q := Eq.mp (by ac_rfl) h

theorem Or.assoc10 (h : (p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ p9 ∨ p10) ∨ q) : p1 ∨ p2 ∨ p3 ∨ p4 ∨ p5 ∨ p6 ∨ p7 ∨ p8 ∨ p9 ∨ p10 ∨ q := Eq.mp (by ac_rfl) h

open scoped Classical in
theorem trans_resol.{u} {α : Type u} (a b c : α) : a ≠ b ∨ b ≠ c ∨ a = c := by
  simp [← Decidable.imp_iff_not_or]
  exact Eq.trans
