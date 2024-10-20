import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq476

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq129 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 86,87
  have eq130 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 86,88
  have eq159 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk2 := resolve eq129 rule_def_2_2 -- resolution 129,82
  have eq160 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq129 rule_def_2_1 -- resolution 129,81
  have eq162 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq159 rule_def_1_1 -- subsumption resolution 159,76
  have eq163 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq160 rule_def_1_0 -- subsumption resolution 160,75
  have eq164 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq162 rule_def_0_2 -- resolution 162,73
  have eq165 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk1 := resolve eq162 rule_def_0_1 -- resolution 162,72
  have eq169 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ a = sk3 := resolve eq130 rule_def_2_2 -- resolution 130,82
  have eq170 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ c = sk1 := resolve eq130 rule_def_2_1 -- resolution 130,81
  have eq172 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := resolve eq169 rule_def_1_1 -- subsumption resolution 169,76
  have eq173 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq170 rule_def_1_0 -- subsumption resolution 170,75
  have eq177 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ a = sk2 := resolve eq164 old_0 -- resolution 164,64
  have eq196 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq163 rule_def_0_2 -- resolution 163,73
  have eq204 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq196 old_0 -- resolution 196,64
  have eq222 : (old sk0 sk1 sk3) ∨ a = sk3 ∨ c = sk3 := resolve eq172 rule_def_0_2 -- resolution 172,73
  have eq223 : (old sk0 sk1 sk3) ∨ a = sk3 ∨ b = sk1 := resolve eq172 rule_def_0_1 -- resolution 172,72
  have eq245 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq173 rule_def_0_1 -- resolution 173,72
  have eq246 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq173 rule_def_0_0 -- resolution 173,71
  have eq278 : c = sk2 ∨ sk2 = sk3 ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq177 eq246 -- resolution 177,246
  have eq279 : c = sk2 ∨ sk2 = sk3 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq177 eq245 -- resolution 177,245
  have eq288 : c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq278 preserve_2 -- subsumption resolution 278,89
  have eq289 : c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq279 preserve_2 -- subsumption resolution 279,89
  have eq303 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := Or.assoc4 (eq288.imp_left (fun h : c = sk2 ↦ superpose h eq129)) -- superposition 129,288, 288 into 129, unify on (0).2 in 288 and (0).3 in 129
  have eq316 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq303 p4XY -- subsumption resolution 303,61
  have eq317 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq316 rule_def_1_0 -- subsumption resolution 316,75
  have eq318 : (sP0 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq317 rule_def_2_1 -- subsumption resolution 317,81
  have eq319 : a = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq318 rule_def_0_0 -- subsumption resolution 318,71
  have eq372 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := Or.assoc4 (eq289.imp_left (fun h : c = sk2 ↦ superpose h eq129)) -- superposition 129,289, 289 into 129, unify on (0).2 in 289 and (0).3 in 129
  have eq388 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq372 p4XY -- subsumption resolution 372,61
  have eq389 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq388 rule_def_0_1 -- subsumption resolution 388,72
  have eq390 : (sP2 sk0 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq389 rule_def_1_0 -- subsumption resolution 389,75
  have eq391 : a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq390 rule_def_2_1 -- subsumption resolution 390,81
  have eq667 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq204 eq246 -- resolution 204,246
  have eq668 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq204 eq245 -- resolution 204,245
  have eq678 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq668 rfl -- duplicate literal removal 668
  have eq679 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq667 rfl -- duplicate literal removal 667
  have eq684 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq679 preserve_2 -- subsumption resolution 679,89
  have eq685 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq678 preserve_2 -- subsumption resolution 678,89
  have eq688 : a = c ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 ∨ a = sk0 := Or.assoc3 (eq319.imp_left (fun h : a = sk2 ↦ superpose h eq684)) -- superposition 684,319, 319 into 684, unify on (0).2 in 319 and (0).2 in 684
  have eq709 : a = c ∨ c = sk1 ∨ a = sk0 := resolve eq688 rfl -- duplicate literal removal 688
  have eq712 : c = sk1 ∨ a = sk0 := resolve eq709 ac -- subsumption resolution 709,58
  have eq719 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ a = sk2 ∨ a = sk0 := Or.assoc3 (eq712.imp_left (fun h : c = sk1 ↦ superpose h eq162)) -- superposition 162,712, 712 into 162, unify on (0).2 in 712 and (0).2 in 162
  have eq725 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ a = sk3 ∨ a = sk0 := Or.assoc3 (eq712.imp_left (fun h : c = sk1 ↦ superpose h eq172)) -- superposition 172,712, 712 into 172, unify on (0).2 in 712 and (0).2 in 172
  have eq750 : (sP0 sk0 c sk2) ∨ a = sk2 ∨ a = sk0 := resolve eq719 p4XZ -- subsumption resolution 719,62
  have eq751 : a = sk2 ∨ a = sk0 := resolve eq750 rule_def_0_0 -- subsumption resolution 750,71
  have eq756 : (sP0 sk0 c sk3) ∨ a = sk3 ∨ a = sk0 := resolve eq725 p4XZ -- subsumption resolution 725,62
  have eq757 : a = sk3 ∨ a = sk0 := resolve eq756 rule_def_0_0 -- subsumption resolution 756,71
  have eq786 : a ≠ sk2 ∨ a = sk0 := eq757.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 89,757, 757 into 89, unify on (0).2 in 757 and (0).2 in 89
  have eq798 : a = sk0 := resolve eq786 eq751 -- subsumption resolution 786,751
  have eq807 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq163 -- backward demodulation 163,798
  have eq809 : (old a sk1 sk2) ∨ a = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq165 -- backward demodulation 165,798
  have eq815 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq173 -- backward demodulation 173,798
  have eq837 : (old a sk1 sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq222 -- backward demodulation 222,798
  have eq838 : (old a sk1 sk3) ∨ a = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq223 -- backward demodulation 223,798
  have eq952 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq807 -- forward demodulation 807,798
  have eq962 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq798, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq815 -- forward demodulation 815,798
  have eq1142 : a = c ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq391.imp_left (fun h : a = sk2 ↦ superpose h eq685)) -- superposition 685,391, 391 into 685, unify on (0).2 in 391 and (0).2 in 685
  have eq1146 : a = c ∨ c = sk1 ∨ b = sk1 := resolve eq1142 rfl -- duplicate literal removal 1142
  have eq1147 : b = sk1 ∨ c = sk1 := resolve eq1146 ac -- subsumption resolution 1146,58
  have eq1201 : (sP0 a b sk2) ∨ (old a b sk2) ∨ c = b ∨ c = sk1 := Or.assoc3 (eq1147.imp_left (fun h : b = sk1 ↦ superpose h eq952)) -- superposition 952,1147, 1147 into 952, unify on (0).2 in 1147 and (0).2 in 952
  have eq1208 : (sP0 a b sk2) ∨ c = b ∨ c = sk1 := resolve eq1201 p3 -- subsumption resolution 1201,60
  have eq1209 : (sP0 a b sk2) ∨ c = sk1 := resolve eq1208 bc -- subsumption resolution 1208,59
  have eq1210 : c = sk2 ∨ c = sk1 := resolve eq1209 rule_def_0_2 -- resolution 1209,73
  have eq1245 : (sP0 a b sk3) ∨ (old a b sk3) ∨ c = b ∨ c = sk1 := Or.assoc3 (eq1147.imp_left (fun h : b = sk1 ↦ superpose h eq962)) -- superposition 962,1147, 1147 into 962, unify on (0).2 in 1147 and (0).2 in 962
  have eq1251 : (sP0 a b sk3) ∨ c = b ∨ c = sk1 := resolve eq1245 p3 -- subsumption resolution 1245,60
  have eq1252 : (sP0 a b sk3) ∨ c = sk1 := resolve eq1251 bc -- subsumption resolution 1251,59
  have eq1253 : c = sk3 ∨ c = sk1 := resolve eq1252 rule_def_0_2 -- resolution 1252,73
  have eq1276 : c ≠ sk2 ∨ c = sk1 := eq1253.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 89,1253, 1253 into 89, unify on (0).2 in 1253 and (0).2 in 89
  have eq1288 : c = sk1 := resolve eq1276 eq1210 -- subsumption resolution 1276,1210
  have eq1294 : c = b ∨ (old a sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq1288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq809 -- backward demodulation 809,1288
  have eq1297 : (old a c sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq1288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq837 -- backward demodulation 837,1288
  have eq1298 : c = b ∨ (old a sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq1288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq838 -- backward demodulation 838,1288
  have eq1381 : (old a sk1 sk2) ∨ a = sk2 := resolve eq1294 bc -- subsumption resolution 1294,59
  have eq1382 : (old a c sk2) ∨ a = sk2 := Eq.mp (by simp only [eq1288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1381 -- forward demodulation 1381,1288
  have eq1383 : a = sk2 := resolve eq1382 p4XZ -- subsumption resolution 1382,62
  have eq1384 : a ≠ sk3 := Eq.mp (by simp only [eq1383, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 89,1383
  have eq1386 : a = sk3 ∨ c = sk3 := resolve eq1297 p4XZ -- subsumption resolution 1297,62
  have eq1387 : c = sk3 := resolve eq1386 eq1384 -- subsumption resolution 1386,1384
  have eq1389 : (old a sk1 sk3) ∨ a = sk3 := resolve eq1298 bc -- subsumption resolution 1298,59
  have eq1390 : (old a sk1 sk3) := resolve eq1389 eq1384 -- subsumption resolution 1389,1384
  have eq1391 : (old a sk1 c) := Eq.mp (by simp only [eq1387, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1390 -- forward demodulation 1390,1387
  subsumption p4XY eq1391 -- subsumption resolution 1391,61

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ ¬ old X1 X3 X4 ∨ old X0 X4 X1)) (old_3 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X1 X3 X2 ∨ old X0 X0 X1)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X2 X0 X3 ∨ old X0 X3 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ a ≠ Z ∨ ¬ old X a X2 ∨ ¬ old X X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ ¬ new X1 X3 X4 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq98 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old X0 X3 b) ∨ ¬(old X0 a X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 77
  have eq99 (X0 X3 : G) : ¬(old X0 a X3) ∨ ¬(old X0 X3 b) ∨ (new X0 c a) := resolve eq98 rfl -- equality resolution 98
  have eq105 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 80,66
  have eq113 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := resolve prev_0 preserve_0 -- resolution 90,91
  have eq118 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) b) ∨ (new X0 c a) ∨ ¬(sP1 X0 X1 X2) := resolve eq99 rule_def_1_2 -- resolution 99,80
  have eq119 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c a) := resolve eq118 rule_def_1_3 -- subsumption resolution 118,81
  have eq130 (X0 X1 X2 X3 : G) : ¬(old X1 X0 (sF0 X1 X2 X3)) ∨ (old X0 X0 X1) ∨ ¬(old X0 X1 b) ∨ ¬(sP1 X1 X2 X3) := resolve old_3 rule_def_1_3 -- resolution 70,81
  have eq137 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 89,91
  have eq138 : (sP2 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) := resolve new_imp preserve_1 -- resolution 89,92
  have eq139 : (sP2 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) := resolve new_imp preserve_2 -- resolution 89,93
  have eq177 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk2 := resolve eq137 rule_def_2_2 -- resolution 137,85
  have eq178 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq137 rule_def_2_1 -- resolution 137,84
  have eq180 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq177 rule_def_1_1 -- subsumption resolution 177,79
  have eq181 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq178 rule_def_1_0 -- subsumption resolution 178,78
  have eq182 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq180 rule_def_0_2 -- resolution 180,76
  have eq183 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk1 := resolve eq180 rule_def_0_1 -- resolution 180,75
  have eq187 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ a = sk3 := resolve eq138 rule_def_2_2 -- resolution 138,85
  have eq188 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ c = sk2 := resolve eq138 rule_def_2_1 -- resolution 138,84
  have eq189 : (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ b = sk0 := resolve eq138 rule_def_2_0 -- resolution 138,83
  have eq190 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk3 := resolve eq187 rule_def_1_1 -- subsumption resolution 187,79
  have eq191 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk2 := resolve eq188 rule_def_1_0 -- subsumption resolution 188,78
  have eq199 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ a = sk4 := resolve eq139 rule_def_2_2 -- resolution 139,85
  have eq200 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ c = sk3 := resolve eq139 rule_def_2_1 -- resolution 139,84
  have eq201 : (sP1 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ b = sk1 := resolve eq139 rule_def_2_0 -- resolution 139,83
  have eq202 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ a = sk4 := resolve eq199 rule_def_1_1 -- subsumption resolution 199,79
  have eq203 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 := resolve eq200 rule_def_1_0 -- subsumption resolution 200,78
  have eq218 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq181 rule_def_0_2 -- resolution 181,76
  have eq219 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq181 rule_def_0_1 -- resolution 181,75
  have eq244 (X0 X1 X2 : G) : (old a a X0) ∨ ¬(old a X0 b) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := resolve eq130 rule_def_1_2 -- resolution 130,80
  have eq245 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old a X0 b) ∨ (old a a X0) := resolve eq244 rfl -- duplicate literal removal 244
  have eq246 : (old sk0 sk2 sk3) ∨ a = sk3 ∨ c = sk3 := resolve eq190 rule_def_0_2 -- resolution 190,76
  have eq247 : (old sk0 sk2 sk3) ∨ a = sk3 ∨ b = sk2 := resolve eq190 rule_def_0_1 -- resolution 190,75
  have eq248 : (old sk0 sk2 sk3) ∨ a = sk3 ∨ a = sk0 := resolve eq190 rule_def_0_0 -- resolution 190,74
  have eq270 : (old sk0 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq191 rule_def_0_2 -- resolution 191,76
  have eq279 : (old sk1 sk3 sk4) ∨ a = sk4 ∨ b = sk3 := resolve eq202 rule_def_0_1 -- resolution 202,75
  have eq280 : (old sk1 sk3 sk4) ∨ a = sk4 ∨ a = sk1 := resolve eq202 rule_def_0_0 -- resolution 202,74
  have eq286 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq203 rule_def_0_2 -- resolution 203,76
  have eq323 (X0 X1 : G) : ¬(old X0 sk1 X1) ∨ c = sk4 ∨ (old X0 sk4 sk1) ∨ ¬(old X0 X1 sk3) ∨ c = sk3 := resolve eq286 old_1 -- resolution 286,68
  have eq407 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ b = sk1 ∨ (new sk1 c a) := resolve eq201 eq119 -- resolution 201,119
  have eq585 : (new sk1 c a) ∨ b = sk1 ∨ (old sk1 sk3 sk4) ∨ a = sk1 := resolve eq407 rule_def_0_0 -- resolution 407,74
  have eq639 : b = sk1 ∨ (old sk1 sk3 sk4) ∨ a = sk1 ∨ (sP1 sk1 c a) ∨ (sP0 sk1 c a) ∨ (old sk1 c a) ∨ (sP2 sk1 c a) := resolve eq585 new_imp -- resolution 585,89
  have eq641 : b = sk1 ∨ (old sk1 sk3 sk4) ∨ a = sk1 ∨ (sP1 sk1 c a) ∨ (sP0 sk1 c a) ∨ (sP2 sk1 c a) := resolve eq639 p4XZ -- subsumption resolution 639,65
  have eq642 : b = sk1 ∨ (old sk1 sk3 sk4) ∨ a = sk1 ∨ (sP1 sk1 c a) ∨ (sP2 sk1 c a) := resolve eq641 rule_def_0_0 -- subsumption resolution 641,74
  have eq643 : (sP1 sk1 c a) ∨ (old sk1 sk3 sk4) ∨ a = sk1 ∨ b = sk1 := resolve eq642 rule_def_2_0 -- subsumption resolution 642,83
  have eq1016 : c = sk4 ∨ (old sk0 sk4 sk1) ∨ ¬(old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq323 eq219 -- resolution 323,219
  have eq1017 : c = sk4 ∨ (old sk0 sk4 sk1) ∨ ¬(old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq323 eq218 -- resolution 323,218
  have eq1021 : (old sk0 sk4 sk1) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1017 eq270 -- subsumption resolution 1017,270
  have eq1033 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ (new sk0 sk4 sk1) := resolve eq1021 imp_new_0 -- resolution 1021,72
  have eq1038 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1033 preserve_3 -- subsumption resolution 1033,94
  have eq1040 : ¬(new sk0 c sk1) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := eq1038.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 94,1038, 1038 into 94, unify on (0).2 in 1038 and (0).2 in 94
  have eq1046 : (old sk1 sk3 c) ∨ a = c ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1038.imp_left (fun h : c = sk4 ↦ superpose h eq279)) -- superposition 279,1038, 1038 into 279, unify on (0).2 in 1038 and (0).3 in 279
  have eq1047 : (old sk1 sk3 c) ∨ a = c ∨ a = sk1 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1038.imp_left (fun h : c = sk4 ↦ superpose h eq280)) -- superposition 280,1038, 1038 into 280, unify on (0).2 in 1038 and (0).3 in 280
  have eq1058 : a = c ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1046 p4XY -- subsumption resolution 1046,64
  have eq1059 : b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1058 ac -- subsumption resolution 1058,61
  have eq1060 : a = c ∨ a = sk1 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1047 p4XY -- subsumption resolution 1047,64
  have eq1061 : c = sk3 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1060 ac -- subsumption resolution 1060,61
  have eq1078 : (old sk0 sk2 b) ∨ c = sk2 ∨ c = b ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1059.imp_left (fun h : b = sk3 ↦ superpose h eq270)) -- superposition 270,1059, 1059 into 270, unify on (0).2 in 1059 and (0).3 in 270
  have eq1117 : (old sk0 sk2 b) ∨ c = sk2 ∨ c = b ∨ c = sk3 ∨ c = sk1 := resolve eq1078 rfl -- duplicate literal removal 1078
  have eq1123 : (old sk0 sk2 b) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq1117 bc -- subsumption resolution 1117,62
  have eq1144 : (sP1 sk1 c sk4) ∨ (old sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc4 (eq1061.imp_left (fun h : c = sk3 ↦ superpose h eq201)) -- superposition 201,1061, 1061 into 201, unify on (0).2 in 1061 and (0).2 in 201
  have eq1145 : (sP0 sk1 c sk4) ∨ (old sk1 c sk4) ∨ a = sk4 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1061.imp_left (fun h : c = sk3 ↦ superpose h eq202)) -- superposition 202,1061, 1061 into 202, unify on (0).2 in 1061 and (0).2 in 202
  have eq1146 : (old sk0 sk2 c) ∨ a = c ∨ b = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1061.imp_left (fun h : c = sk3 ↦ superpose h eq247)) -- superposition 247,1061, 1061 into 247, unify on (0).2 in 1061 and (0).3 in 247
  have eq1147 : (old sk0 sk2 c) ∨ a = c ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1061.imp_left (fun h : c = sk3 ↦ superpose h eq248)) -- superposition 248,1061, 1061 into 248, unify on (0).2 in 1061 and (0).3 in 248
  have eq1192 : (sP1 sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1144 p4XZ -- subsumption resolution 1144,65
  have eq1193 : (sP1 sk1 c sk4) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1192 rule_def_0_0 -- subsumption resolution 1192,74
  have eq1194 : (sP0 sk1 c sk4) ∨ a = sk4 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1145 p4XZ -- subsumption resolution 1145,65
  have eq1195 : a = sk4 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1194 rule_def_0_0 -- subsumption resolution 1194,74
  have eq1196 : a = c ∨ b = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1146 p4XY -- subsumption resolution 1146,64
  have eq1197 : b = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1196 ac -- subsumption resolution 1196,61
  have eq1198 : a = c ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1147 p4XY -- subsumption resolution 1147,64
  have eq1199 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq1198 ac -- subsumption resolution 1198,61
  have eq1207 : ¬(new sk0 a sk1) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := eq1195.imp_left (fun h : a = sk4 ↦ superpose h preserve_3) -- superposition 94,1195, 1195 into 94, unify on (0).2 in 1195 and (0).2 in 94
  have eq1243 : (old sk0 sk1 b) ∨ c = sk1 ∨ c = b ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1197.imp_left (fun h : b = sk2 ↦ superpose h eq218)) -- superposition 218,1197, 1197 into 218, unify on (0).2 in 1197 and (0).3 in 218
  have eq1269 : (old sk0 sk1 b) ∨ c = sk1 ∨ c = b ∨ a = sk1 ∨ c = sk2 := resolve eq1243 rfl -- duplicate literal removal 1243
  have eq1275 : (old sk0 sk1 b) ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq1269 bc -- subsumption resolution 1269,62
  have eq1287 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := Or.assoc4 (eq1199.imp_left (fun h : c = sk2 ↦ superpose h eq137)) -- superposition 137,1199, 1199 into 137, unify on (0).2 in 1199 and (0).3 in 137
  have eq1325 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq1287 p4XY -- subsumption resolution 1287,64
  have eq1326 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq1325 rule_def_1_0 -- subsumption resolution 1325,78
  have eq1327 : (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq1326 rule_def_2_1 -- subsumption resolution 1326,84
  have eq1328 : c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1327 rule_def_0_0 -- subsumption resolution 1327,74
  have eq1420 : (sP1 c c a) ∨ (old c sk3 sk4) ∨ a = c ∨ c = b ∨ a = sk1 ∨ a = sk0 := Or.assoc4 (eq1328.imp_left (fun h : c = sk1 ↦ superpose h eq643)) -- superposition 643,1328, 1328 into 643, unify on (0).2 in 1328 and (0).1 in 643
  have eq1474 : (old c sk3 sk4) ∨ a = c ∨ c = b ∨ a = sk1 ∨ a = sk0 := resolve eq1420 eq105 -- subsumption resolution 1420,105
  have eq1475 : a = c ∨ c = b ∨ a = sk1 ∨ a = sk0 := resolve eq1474 p4YZ -- subsumption resolution 1474,66
  have eq1476 : c = b ∨ a = sk1 ∨ a = sk0 := resolve eq1475 ac -- subsumption resolution 1475,61
  have eq1477 : a = sk1 ∨ a = sk0 := resolve eq1476 bc -- subsumption resolution 1476,62
  have eq1505 : (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ a = c ∨ a = sk0 := Or.assoc3 (eq1477.imp_left (fun h : a = sk1 ↦ superpose h eq181)) -- superposition 181,1477, 1477 into 181, unify on (0).2 in 1477 and (0).2 in 181
  have eq1596 : (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ a = sk0 := resolve eq1505 ac -- subsumption resolution 1505,61
  have eq1597 : (old sk0 a sk2) ∨ a = sk0 := resolve eq1596 rule_def_0_0 -- subsumption resolution 1596,74
  have eq1701 : ¬(old sk0 sk2 b) ∨ a = sk0 ∨ (new sk0 c a) := resolve eq1597 eq99 -- resolution 1597,99
  have eq3057 : ¬(new sk0 c a) ∨ c = sk3 ∨ a = c ∨ c = sk2 ∨ a = sk0 := Or.assoc4 (eq1477.imp_left (fun h : a = sk1 ↦ superpose h eq1040)) -- superposition 1040,1477, 1477 into 1040, unify on (0).2 in 1477 and (0).3 in 1040
  have eq3058 : ¬(new sk0 c a) ∨ c = sk3 ∨ c = sk2 ∨ a = sk0 := resolve eq3057 ac -- subsumption resolution 3057,61
  have eq3252 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ (new sk0 c a) := resolve eq1123 eq1701 -- resolution 1123,1701
  have eq3272 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq3252 eq3058 -- subsumption resolution 3252,3058
  have eq3296 : (sP2 sk0 sk2 c) ∨ (sP0 sk0 sk2 c) ∨ (old sk0 sk2 c) ∨ (sP1 sk0 sk2 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := Or.assoc4 (eq3272.imp_left (fun h : c = sk3 ↦ superpose h eq138)) -- superposition 138,3272, 3272 into 138, unify on (0).2 in 3272 and (0).3 in 138
  have eq3370 : (sP2 sk0 sk2 c) ∨ (sP0 sk0 sk2 c) ∨ (sP1 sk0 sk2 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq3296 p4XY -- subsumption resolution 3296,64
  have eq3371 : (sP2 sk0 sk2 c) ∨ (sP1 sk0 sk2 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq3370 rule_def_0_0 -- subsumption resolution 3370,74
  have eq3372 : (sP2 sk0 sk2 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq3371 rule_def_1_0 -- subsumption resolution 3371,78
  have eq3373 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq3372 rule_def_2_1 -- subsumption resolution 3372,84
  have eq3397 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := Or.assoc4 (eq3373.imp_left (fun h : c = sk2 ↦ superpose h eq137)) -- superposition 137,3373, 3373 into 137, unify on (0).2 in 3373 and (0).3 in 137
  have eq3449 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq3397 p4XY -- subsumption resolution 3397,64
  have eq3450 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq3449 rule_def_0_0 -- subsumption resolution 3449,74
  have eq3451 : (sP2 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq3450 rule_def_1_0 -- subsumption resolution 3450,78
  have eq3452 : c = sk1 ∨ a = sk0 := resolve eq3451 rule_def_2_1 -- subsumption resolution 3451,84
  have eq3470 : a = c ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq1477.imp_left (fun h : a = sk1 ↦ superpose h eq3452)) -- superposition 3452,1477, 1477 into 3452, unify on (0).2 in 1477 and (0).2 in 3452
  have eq3580 : a = c ∨ a = sk0 := resolve eq3470 rfl -- duplicate literal removal 3470
  have eq3581 : a = sk0 := resolve eq3580 ac -- subsumption resolution 3580,61
  have eq3582 : (new a sk1 sk2) := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_0 -- backward demodulation 91,3581
  have eq3583 : (new a sk2 sk3) := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 92,3581
  have eq3584 : ¬(new a sk4 sk1) := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 94,3581
  have eq3585 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ sk2 = X0 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq113 -- backward demodulation 113,3581
  have eq3594 : (old a sk1 sk2) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq182 -- backward demodulation 182,3581
  have eq3595 : (old a sk1 sk2) ∨ a = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq183 -- backward demodulation 183,3581
  have eq3599 : (sP1 a sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ b = sk0 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq189 -- backward demodulation 189,3581
  have eq3610 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq218 -- backward demodulation 218,3581
  have eq3611 : (old a sk1 sk2) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq219 -- backward demodulation 219,3581
  have eq3623 : (old a sk2 sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq246 -- backward demodulation 246,3581
  have eq3624 : (old a sk2 sk3) ∨ a = sk3 ∨ b = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq247 -- backward demodulation 247,3581
  have eq3634 : (old a sk2 sk3) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq270 -- backward demodulation 270,3581
  have eq3784 : (old a sk4 sk1) ∨ c = sk4 ∨ ¬(old sk0 sk2 sk3) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1016 -- backward demodulation 1016,3581
  have eq3794 : ¬(new a c sk1) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1040 -- backward demodulation 1040,3581
  have eq3798 : (old a sk2 b) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1123 -- backward demodulation 1123,3581
  have eq3806 : ¬(new a a sk1) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1207 -- backward demodulation 1207,3581
  have eq3817 : (old a sk1 b) ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1275 -- backward demodulation 1275,3581
  have eq4014 : (old a sk2 sk3) ∨ (sP1 a sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ b = sk0 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3599 -- forward demodulation 3599,3581
  have eq4015 : (sP0 a sk2 sk3) ∨ (old a sk2 sk3) ∨ (sP1 a sk2 sk3) ∨ b = sk0 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4014 -- forward demodulation 4014,3581
  have eq4016 : (sP1 a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old a sk2 sk3) ∨ a = b := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4015 -- forward demodulation 4015,3581
  have eq4289 : ¬(old a sk2 sk3) ∨ (old a sk4 sk1) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3581, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3784 -- forward demodulation 3784,3581
  have eq5425 : b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old a sk1 b) ∨ (old a a sk1) := resolve eq1193 eq245 -- resolution 1193,245
  have eq5437 : (old a a sk1) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 := resolve eq5425 eq3817 -- subsumption resolution 5425,3817
  have eq5857 : a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ b = sk1 ∨ (new a a sk1) := resolve eq5437 imp_new_0 -- resolution 5437,72
  have eq5870 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq5857 eq3806 -- subsumption resolution 5857,3806
  have eq5900 : (old a sk1 c) ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := Or.assoc3 (eq5870.imp_left (fun h : c = sk2 ↦ superpose h eq3595)) -- superposition 3595,5870, 5870 into 3595, unify on (0).2 in 5870 and (0).3 in 3595
  have eq5925 : (old a sk1 c) ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5900 rfl -- duplicate literal removal 5900
  have eq5928 : a = c ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5925 p4XY -- subsumption resolution 5925,64
  have eq5929 : b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5928 ac -- subsumption resolution 5928,61
  have eq6022 : ¬(new a sk4 b) ∨ c = sk1 ∨ a = sk1 := eq5929.imp_left (fun h : b = sk1 ↦ superpose h eq3584) -- superposition 3584,5929, 5929 into 3584, unify on (0).2 in 5929 and (0).3 in 3584
  have eq6026 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5929.imp_left (fun h : b = sk1 ↦ superpose h eq3610)) -- superposition 3610,5929, 5929 into 3610, unify on (0).2 in 5929 and (0).2 in 3610
  have eq6053 : a ≠ b ∨ c = sk1 ∨ a = sk1 := resolve eq5929 trans_resol -- equality factoring 5929
  have eq6064 : c = b ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq6026 p3 -- subsumption resolution 6026,63
  have eq6065 : c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq6064 bc -- subsumption resolution 6064,62
  have eq6138 : (old a c sk3) ∨ a = sk3 ∨ c = b ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq6065.imp_left (fun h : c = sk2 ↦ superpose h eq3624)) -- superposition 3624,6065, 6065 into 3624, unify on (0).2 in 6065 and (0).2 in 3624
  have eq6148 : (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ (old a c sk3) ∨ a = b ∨ c = sk1 ∨ a = sk1 := Or.assoc4 (eq6065.imp_left (fun h : c = sk2 ↦ superpose h eq4016)) -- superposition 4016,6065, 6065 into 4016, unify on (0).2 in 6065 and (0).2 in 4016
  have eq6163 : a = sk3 ∨ c = b ∨ c = sk1 ∨ a = sk1 := resolve eq6138 p4XZ -- subsumption resolution 6138,65
  have eq6164 : a = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq6163 bc -- subsumption resolution 6163,62
  have eq6170 : (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ a = b ∨ c = sk1 ∨ a = sk1 := resolve eq6148 p4XZ -- subsumption resolution 6148,65
  have eq6171 : (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq6170 eq6053 -- subsumption resolution 6170,6053
  have eq6184 : (sP0 sk1 a sk4) ∨ (old sk1 a sk4) ∨ a = c ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq6164.imp_left (fun h : a = sk3 ↦ superpose h eq203)) -- superposition 203,6164, 6164 into 203, unify on (0).2 in 6164 and (0).2 in 203
  have eq6268 : (sP0 sk1 a sk4) ∨ (old sk1 a sk4) ∨ c = sk1 ∨ a = sk1 := resolve eq6184 ac -- subsumption resolution 6184,61
  have eq6269 : (old sk1 a sk4) ∨ c = sk1 ∨ a = sk1 := resolve eq6268 rule_def_0_0 -- subsumption resolution 6268,74
  have eq6513 : (old b a sk4) ∨ c = b ∨ a = b ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5929.imp_left (fun h : b = sk1 ↦ superpose h eq6269)) -- superposition 6269,5929, 5929 into 6269, unify on (0).2 in 5929 and (0).1 in 6269
  have eq6524 : (old b a sk4) ∨ a = b ∨ c = sk1 ∨ a = sk1 := resolve eq6513 bc -- subsumption resolution 6513,62
  have eq6525 : (old b a sk4) ∨ c = sk1 ∨ a = sk1 := resolve eq6524 eq6053 -- subsumption resolution 6524,6053
  have eq6578 (X0 : G) : ¬(old a a X0) ∨ a = sk1 ∨ (old a sk4 b) ∨ ¬(old a X0 b) ∨ c = sk1 := resolve eq6525 old_4 -- resolution 6525,71
  have eq7881 : (old a sk4 sk1) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 ∨ c = sk3 := resolve eq4289 eq3623 -- resolution 4289,3623
  have eq7900 : (old a sk4 sk1) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq7881 rfl -- duplicate literal removal 7881
  have eq10567 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 ∨ (new a sk4 sk1) := resolve eq7900 imp_new_0 -- resolution 7900,72
  have eq10577 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq10567 eq3584 -- subsumption resolution 10567,3584
  have eq10588 : (old sk1 sk3 c) ∨ a = c ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := Or.assoc3 (eq10577.imp_left (fun h : c = sk4 ↦ superpose h eq279)) -- superposition 279,10577, 10577 into 279, unify on (0).2 in 10577 and (0).3 in 279
  have eq10609 : ¬(new a c sk1) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := eq10577.imp_left (fun h : c = sk4 ↦ superpose h eq3584) -- superposition 3584,10577, 10577 into 3584, unify on (0).2 in 10577 and (0).2 in 3584
  have eq10722 : a = c ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq10588 p4XY -- subsumption resolution 10588,64
  have eq10723 : b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq10722 ac -- subsumption resolution 10722,61
  have eq10942 : (old a sk2 b) ∨ a = b ∨ c = b ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := Or.assoc3 (eq10723.imp_left (fun h : b = sk3 ↦ superpose h eq3623)) -- superposition 3623,10723, 10723 into 3623, unify on (0).2 in 10723 and (0).3 in 3623
  have eq11138 : (old a sk2 b) ∨ a = b ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq10942 bc -- subsumption resolution 10942,62
  have eq12903 (X0 X1 : G) : a = sk1 ∨ (old a sk4 b) ∨ ¬(old a (sF0 a X0 X1) b) ∨ c = sk1 ∨ ¬(sP1 a X0 X1) := resolve eq6578 rule_def_1_2 -- resolution 6578,80
  have eq12910 (X0 X1 : G) : ¬(sP1 a X0 X1) ∨ (old a sk4 b) ∨ c = sk1 ∨ a = sk1 := resolve eq12903 rule_def_1_3 -- subsumption resolution 12903,81
  have eq12924 : (old a sk4 b) ∨ c = sk1 ∨ a = sk1 ∨ (sP0 a c sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq12910 eq6171 -- resolution 12910,6171
  have eq12946 : (sP0 a c sk3) ∨ c = sk1 ∨ a = sk1 ∨ (old a sk4 b) := resolve eq12924 rfl -- duplicate literal removal 12924
  have eq12956 : c = sk1 ∨ a = sk1 ∨ (old a sk4 b) ∨ c = b := resolve eq12946 rule_def_0_1 -- resolution 12946,75
  have eq12972 : (old a sk4 b) ∨ a = sk1 ∨ c = sk1 := resolve eq12956 bc -- subsumption resolution 12956,62
  have eq12988 : a = sk1 ∨ c = sk1 ∨ (new a sk4 b) := resolve eq12972 imp_new_0 -- resolution 12972,72
  have eq13011 : c = sk1 ∨ a = sk1 := resolve eq12988 eq6022 -- subsumption resolution 12988,6022
  have eq13069 : (sP1 c c a) ∨ (old c sk3 sk4) ∨ a = c ∨ c = b ∨ a = sk1 := Or.assoc4 (eq13011.imp_left (fun h : c = sk1 ↦ superpose h eq643)) -- superposition 643,13011, 13011 into 643, unify on (0).2 in 13011 and (0).1 in 643
  have eq13252 : (old c sk3 sk4) ∨ a = c ∨ c = b ∨ a = sk1 := resolve eq13069 eq105 -- subsumption resolution 13069,105
  have eq13253 : a = c ∨ c = b ∨ a = sk1 := resolve eq13252 p4YZ -- subsumption resolution 13252,66
  have eq13254 : c = b ∨ a = sk1 := resolve eq13253 ac -- subsumption resolution 13253,61
  have eq13255 : a = sk1 := resolve eq13254 bc -- subsumption resolution 13254,62
  have eq13256 : (new a sk3 sk4) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 93,13255
  have eq13258 : (sP1 a sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq139 -- backward demodulation 139,13255
  have eq13266 : (old a sk3 sk4) ∨ a = sk4 ∨ b = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq279 -- backward demodulation 279,13255
  have eq13268 : (old a sk3 sk4) ∨ c = sk3 ∨ c = sk4 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq286 -- backward demodulation 286,13255
  have eq13403 : (new a a sk2) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3582 -- backward demodulation 3582,13255
  have eq13404 : ¬(new a sk4 a) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3584 -- backward demodulation 3584,13255
  have eq13405 : ∀ (X0 : G) , ¬(new a a X0) ∨ sk2 = X0 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3585 -- backward demodulation 3585,13255
  have eq13406 : (old a a sk2) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3594 -- backward demodulation 3594,13255
  have eq13410 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3610 -- backward demodulation 3610,13255
  have eq13411 : a = c ∨ (old a sk1 sk2) ∨ b = sk1 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3611 -- backward demodulation 3611,13255
  have eq13414 : a = c ∨ ¬(new a c sk1) ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3794 -- backward demodulation 3794,13255
  have eq13417 : a = c ∨ (old a sk2 b) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3798 -- backward demodulation 3798,13255
  have eq14127 : a = c ∨ ¬(new a c sk1) ∨ c = sk3 ∨ b = sk1 ∨ a = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10609 -- backward demodulation 10609,13255
  have eq14150 : a = c ∨ (old a sk2 b) ∨ a = b ∨ c = sk3 ∨ b = sk1 ∨ a = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq11138 -- backward demodulation 11138,13255
  have eq14326 : (sP2 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13258 -- forward demodulation 13258,13255
  have eq14327 : (sP0 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14326 -- forward demodulation 14326,13255
  have eq14328 : (sP2 a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP1 a sk3 sk4) := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14327 -- forward demodulation 14327,13255
  have eq14567 : (old a sk1 sk2) ∨ c = sk2 := resolve eq13410 ac -- subsumption resolution 13410,61
  have eq14568 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14567 -- forward demodulation 14567,13255
  have eq14569 : (old a sk1 sk2) ∨ b = sk1 := resolve eq13411 ac -- subsumption resolution 13411,61
  have eq14570 : (old a a sk2) ∨ b = sk1 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14569 -- forward demodulation 14569,13255
  have eq14571 : (old a a sk2) ∨ a = b := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14570 -- forward demodulation 14570,13255
  have eq14577 : ¬(new a c sk1) ∨ c = sk3 ∨ c = sk2 := resolve eq13414 ac -- subsumption resolution 13414,61
  have eq14578 : ¬(new a c a) ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14577 -- forward demodulation 14577,13255
  have eq14581 : (old a sk2 b) ∨ c = sk2 ∨ c = sk3 := resolve eq13417 ac -- subsumption resolution 13417,61
  have eq15572 : ¬(new a c sk1) ∨ c = sk3 ∨ b = sk1 ∨ a = sk3 := resolve eq14127 ac -- subsumption resolution 14127,61
  have eq15573 : ¬(new a c a) ∨ c = sk3 ∨ b = sk1 ∨ a = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15572 -- forward demodulation 15572,13255
  have eq15574 : ¬(new a c a) ∨ a = b ∨ c = sk3 ∨ a = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15573 -- forward demodulation 15573,13255
  have eq15617 : (old a sk2 b) ∨ a = b ∨ c = sk3 ∨ b = sk1 ∨ a = sk3 := resolve eq14150 ac -- subsumption resolution 14150,61
  have eq15618 : a = b ∨ (old a sk2 b) ∨ a = b ∨ c = sk3 ∨ a = sk3 := Eq.mp (by simp only [eq13255, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15617 -- forward demodulation 15617,13255
  have eq15619 : (old a sk2 b) ∨ a = b ∨ c = sk3 ∨ a = sk3 := resolve eq15618 rfl -- duplicate literal removal 15618
  have eq15861 : ¬(old a sk2 b) ∨ c = sk2 ∨ (new a c a) := resolve eq14568 eq99 -- resolution 14568,99
  have eq15894 : ¬(old a sk2 b) ∨ a = b ∨ (new a c a) := resolve eq14571 eq99 -- resolution 14571,99
  have eq16200 : c = sk2 ∨ (new a c a) ∨ c = sk2 ∨ c = sk3 := resolve eq15861 eq14581 -- resolution 15861,14581
  have eq16205 : c = sk2 ∨ (new a c a) ∨ c = sk3 := resolve eq16200 rfl -- duplicate literal removal 16200
  have eq16206 : c = sk3 ∨ c = sk2 := resolve eq16205 eq14578 -- subsumption resolution 16205,14578
  have eq16220 : (old a sk2 c) ∨ a = c ∨ b = sk2 ∨ c = sk2 := Or.assoc3 (eq16206.imp_left (fun h : c = sk3 ↦ superpose h eq3624)) -- superposition 3624,16206, 16206 into 3624, unify on (0).2 in 16206 and (0).3 in 3624
  have eq16232 : (old a c sk4) ∨ a = sk4 ∨ c = b ∨ c = sk2 := Or.assoc3 (eq16206.imp_left (fun h : c = sk3 ↦ superpose h eq13266)) -- superposition 13266,16206, 16206 into 13266, unify on (0).2 in 16206 and (0).2 in 13266
  have eq16245 : a = c ∨ b = sk2 ∨ c = sk2 := resolve eq16220 p4XY -- subsumption resolution 16220,64
  have eq16246 : b = sk2 ∨ c = sk2 := resolve eq16245 ac -- subsumption resolution 16245,61
  have eq16251 : a = sk4 ∨ c = b ∨ c = sk2 := resolve eq16232 p4XZ -- subsumption resolution 16232,65
  have eq16252 : a = sk4 ∨ c = sk2 := resolve eq16251 bc -- subsumption resolution 16251,62
  have eq16285 : (new a a b) ∨ c = sk2 := eq16246.imp_left (fun h : b = sk2 ↦ superpose h eq13403) -- superposition 13403,16246, 16246 into 13403, unify on (0).2 in 16246 and (0).3 in 13403
  have eq16315 : ¬(new a a a) ∨ c = sk2 := eq16252.imp_left (fun h : a = sk4 ↦ superpose h eq13404) -- superposition 13404,16252, 16252 into 13404, unify on (0).2 in 16252 and (0).2 in 13404
  have eq17467 : a = b ∨ c = sk3 ∨ a = sk3 ∨ a = b ∨ (new a c a) := resolve eq15619 eq15894 -- resolution 15619,15894
  have eq17486 : a = b ∨ c = sk3 ∨ a = sk3 ∨ (new a c a) := resolve eq17467 rfl -- duplicate literal removal 17467
  have eq17487 : c = sk3 ∨ a = b ∨ a = sk3 := resolve eq17486 eq15574 -- subsumption resolution 17486,15574
  have eq17532 : (old a sk2 c) ∨ a = c ∨ b = sk2 ∨ a = b ∨ a = sk3 := Or.assoc3 (eq17487.imp_left (fun h : c = sk3 ↦ superpose h eq3624)) -- superposition 3624,17487, 17487 into 3624, unify on (0).2 in 17487 and (0).3 in 3624
  have eq17594 : a = c ∨ b = sk2 ∨ a = b ∨ a = sk3 := resolve eq17532 p4XY -- subsumption resolution 17532,64
  have eq17595 : a = sk3 ∨ a = b ∨ b = sk2 := resolve eq17594 ac -- subsumption resolution 17594,61
  have eq17627 : (new a sk2 a) ∨ a = b ∨ b = sk2 := eq17595.imp_left (fun h : a = sk3 ↦ superpose h eq3583) -- superposition 3583,17595, 17595 into 3583, unify on (0).2 in 17595 and (0).3 in 3583
  have eq17636 : (new a a sk4) ∨ a = b ∨ b = sk2 := eq17595.imp_left (fun h : a = sk3 ↦ superpose h eq13256) -- superposition 13256,17595, 17595 into 13256, unify on (0).2 in 17595 and (0).2 in 13256
  have eq17876 : sk2 = sk4 ∨ b = sk2 ∨ a = b := resolve eq17636 eq13405 -- resolution 17636,13405
  have eq17920 : ¬(new a sk2 a) ∨ b = sk2 ∨ a = b := eq17876.imp_left (fun h : sk2 = sk4 ↦ superpose h eq13404) -- superposition 13404,17876, 17876 into 13404, unify on (0).2 in 17876 and (0).2 in 13404
  have eq17982 : b = sk2 ∨ a = b := resolve eq17920 eq17627 -- subsumption resolution 17920,17627
  have eq17988 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ a = b := Or.assoc3 (eq17982.imp_left (fun h : b = sk2 ↦ superpose h eq3634)) -- superposition 3634,17982, 17982 into 3634, unify on (0).2 in 17982 and (0).2 in 3634
  have eq18010 : (old a a b) ∨ a = b ∨ c = b ∨ a = b := Or.assoc3 (eq17982.imp_left (fun h : b = sk2 ↦ superpose h eq13406)) -- superposition 13406,17982, 17982 into 13406, unify on (0).2 in 17982 and (0).3 in 13406
  have eq18056 : (old a a b) ∨ a = b ∨ c = b := resolve eq18010 rfl -- duplicate literal removal 18010
  have eq18065 : c = b ∨ c = sk3 ∨ a = b := resolve eq17988 p3 -- subsumption resolution 17988,63
  have eq18066 : c = sk3 ∨ a = b := resolve eq18065 bc -- subsumption resolution 18065,62
  have eq18072 : (old a a b) ∨ a = b := resolve eq18056 bc -- subsumption resolution 18056,62
  have eq18123 : (sP2 a c sk4) ∨ (sP0 a c sk4) ∨ (old a c sk4) ∨ (sP1 a c sk4) ∨ a = b := Or.assoc4 (eq18066.imp_left (fun h : c = sk3 ↦ superpose h eq14328)) -- superposition 14328,18066, 18066 into 14328, unify on (0).2 in 18066 and (0).2 in 14328
  have eq18179 : (sP2 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ a = b := resolve eq18123 p4XZ -- subsumption resolution 18123,65
  have eq18180 : (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ a = b := resolve eq18179 rule_def_2_0 -- subsumption resolution 18179,83
  have eq19227 : (sP0 a c sk4) ∨ a = b ∨ ¬(old a a b) ∨ (old a a a) := resolve eq18180 eq245 -- resolution 18180,245
  have eq19249 : (sP0 a c sk4) ∨ a = b ∨ ¬(old a a b) := resolve eq19227 old_0 -- subsumption resolution 19227,67
  have eq19250 : (sP0 a c sk4) ∨ a = b := resolve eq19249 eq18072 -- subsumption resolution 19249,18072
  have eq19264 : a = b ∨ c = b := resolve eq19250 rule_def_0_1 -- resolution 19250,75
  have eq19284 : a = b := resolve eq19264 bc -- subsumption resolution 19264,62
  have eq19286 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq19284, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 63,19284
  have eq19325 : a = sk2 ∨ (old a sk2 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq19284, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3624 -- backward demodulation 3624,19284
  have eq19529 : (new a a a) ∨ c = sk2 := Eq.mp (by simp only [eq19284, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16285 -- backward demodulation 16285,19284
  have eq19643 : c = sk2 := resolve eq19529 eq16315 -- subsumption resolution 19529,16315
  have eq19645 : (new a c sk3) := Eq.mp (by simp only [eq19643, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3583 -- backward demodulation 3583,19643
  have eq19682 : a = c ∨ (old a sk2 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq19643, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19325 -- backward demodulation 19325,19643
  have eq19729 : (old a sk2 sk3) ∨ a = sk3 := resolve eq19682 ac -- subsumption resolution 19682,61
  have eq19730 : (old a c sk3) ∨ a = sk3 := Eq.mp (by simp only [eq19643, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19729 -- forward demodulation 19729,19643
  have eq19731 : a = sk3 := resolve eq19730 p4XZ -- subsumption resolution 19730,65
  have eq19735 : a = c ∨ (old a sk3 sk4) ∨ c = sk4 := Eq.mp (by simp only [eq19731, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13268 -- backward demodulation 13268,19731
  have eq19754 : (new a c a) := Eq.mp (by simp only [eq19731, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19645 -- backward demodulation 19645,19731
  have eq19758 : (old a sk3 sk4) ∨ c = sk4 := resolve eq19735 ac -- subsumption resolution 19735,61
  have eq19759 : (old a a sk4) ∨ c = sk4 := Eq.mp (by simp only [eq19731, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19758 -- forward demodulation 19758,19731
  have eq19760 : c = sk4 := resolve eq19759 eq19286 -- subsumption resolution 19759,19286
  have eq19761 : ¬(new a c a) := Eq.mp (by simp only [eq19760, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13404 -- backward demodulation 13404,19760
  subsumption eq19761 eq19754 -- subsumption resolution 19754,19761

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1, ¬ old X0 X1 X0 ∨ ¬ old X1 X0 X0 ∨ old X0 X0 X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X0 ∨ ¬ new X1 X0 X0 ∨ new X0 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq149 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 90,93
  have eq150 : (sP2 sk1 sk0 sk0) ∨ (sP0 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ (sP1 sk1 sk0 sk0) := resolve new_imp preserve_1 -- resolution 90,94
  have eq188 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ a = sk0 := resolve eq149 rule_def_2_2 -- resolution 149,86
  have eq189 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ c = sk1 := resolve eq149 rule_def_2_1 -- resolution 149,85
  have eq191 : (old sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ a = sk0 := resolve eq188 rule_def_0_0 -- subsumption resolution 188,75
  have eq192 : (old sk0 sk1 sk0) ∨ a = sk0 := resolve eq191 rule_def_1_1 -- subsumption resolution 191,80
  have eq193 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq189 rule_def_1_0 -- subsumption resolution 189,79
  have eq201 : (sP0 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ (sP1 sk1 sk0 sk0) ∨ a = sk0 := resolve eq150 rule_def_2_2 -- resolution 150,86
  have eq202 : (sP0 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ (sP1 sk1 sk0 sk0) ∨ c = sk0 := resolve eq150 rule_def_2_1 -- resolution 150,85
  have eq204 : (sP0 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ a = sk0 := resolve eq201 rule_def_1_1 -- subsumption resolution 201,80
  have eq205 : (old sk1 sk0 sk0) ∨ (sP1 sk1 sk0 sk0) ∨ c = sk0 := resolve eq202 rule_def_0_2 -- subsumption resolution 202,77
  have eq206 : (old sk1 sk0 sk0) ∨ c = sk0 := resolve eq205 rule_def_1_0 -- subsumption resolution 205,79
  have eq212 : c = sk0 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq206 old_2 -- resolution 206,70
  have eq224 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq193 rule_def_0_2 -- resolution 193,77
  have eq246 : (old sk1 sk0 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq204 rule_def_0_1 -- resolution 204,76
  have eq247 : (old sk1 sk0 sk0) ∨ a = sk0 ∨ a = sk1 := resolve eq204 rule_def_0_0 -- resolution 204,75
  have eq251 : a = sk0 ∨ b = sk0 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq246 old_2 -- resolution 246,70
  have eq257 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = sk0 := resolve eq251 eq192 -- subsumption resolution 251,192
  have eq261 : a = sk0 ∨ a = sk1 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq247 old_2 -- resolution 247,70
  have eq267 : (old sk0 sk0 sk1) ∨ a = sk1 ∨ a = sk0 := resolve eq261 eq192 -- subsumption resolution 261,192
  have eq274 : b = sk0 ∨ a = sk0 ∨ (new sk0 sk0 sk1) := resolve eq257 imp_new_0 -- resolution 257,73
  have eq275 : b = sk0 ∨ a = sk0 := resolve eq274 preserve_2 -- subsumption resolution 274,95
  have eq289 : (old sk1 b b) ∨ c = b ∨ a = sk0 := Or.assoc2 (eq275.imp_left (fun h : b = sk0 ↦ superpose h eq206)) -- superposition 206,275, 275 into 206, unify on (0).2 in 275 and (0).2 in 206
  have eq295 : (old sk1 b b) ∨ a = sk0 := resolve eq289 bc -- subsumption resolution 289,63
  have eq330 : a = sk1 ∨ a = sk0 ∨ (new sk0 sk0 sk1) := resolve eq267 imp_new_0 -- resolution 267,73
  have eq332 : a = sk1 ∨ a = sk0 := resolve eq330 preserve_2 -- subsumption resolution 330,95
  have eq356 : (old a b b) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq332.imp_left (fun h : a = sk1 ↦ superpose h eq295)) -- superposition 295,332, 332 into 295, unify on (0).2 in 332 and (0).1 in 295
  have eq357 : (old a b b) ∨ a = sk0 := resolve eq356 rfl -- duplicate literal removal 356
  have eq371 : a = sk0 := resolve eq357 p3 -- subsumption resolution 357,64
  have eq374 : ¬(new a a sk1) := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 95,371
  have eq393 : (old sk1 a a) ∨ c = sk0 := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq206 -- backward demodulation 206,371
  have eq398 : a = c ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq212 -- backward demodulation 212,371
  have eq401 : (old a sk1 a) ∨ c = sk1 ∨ c = sk0 := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq224 -- backward demodulation 224,371
  have eq451 : a = c ∨ (old sk1 a a) := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq393 -- forward demodulation 393,371
  have eq452 : (old sk1 a a) := resolve eq451 ac -- subsumption resolution 451,62
  have eq466 : (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq398 ac -- subsumption resolution 398,62
  have eq467 : (old a a sk1) ∨ ¬(old sk0 sk1 sk0) := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq466 -- forward demodulation 466,371
  have eq468 : ¬(old a sk1 a) ∨ (old a a sk1) := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq467 -- forward demodulation 467,371
  have eq475 : a = c ∨ (old a sk1 a) ∨ c = sk1 := Eq.mp (by simp only [eq371, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq401 -- forward demodulation 401,371
  have eq476 : (old a sk1 a) ∨ c = sk1 := resolve eq475 ac -- subsumption resolution 475,62
  have eq550 : (old a a sk1) ∨ c = sk1 := resolve eq468 eq476 -- resolution 468,476
  have eq556 : c = sk1 ∨ (new a a sk1) := resolve eq550 imp_new_0 -- resolution 550,73
  have eq557 : c = sk1 := resolve eq556 eq374 -- subsumption resolution 556,374
  have eq573 : (old c a a) := Eq.mp (by simp only [eq557, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq452 -- backward demodulation 452,557
  subsumption p4YZ eq573 -- subsumption resolution 573,67

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ ¬ new X1 X3 X4 ∨ new X0 X4 X1)) (old_3 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X0 X3 ∨ ¬ old X1 X3 X2 ∨ old X0 X0 X1)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ a ≠ Z ∨ ¬ old X a X2 ∨ ¬ old X X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X1 X0 X3 ∨ ¬ new X1 X3 X2 ∨ new X0 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq101 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 77
  have eq102 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq101 rfl -- equality resolution 101
  have eq103 : (new a b c) := resolve eq102 rfl -- equality resolution 102
  have eq104 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old X0 X3 b) ∨ ¬(old X0 a X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 81
  have eq105 (X0 X3 : G) : ¬(old X0 a X3) ∨ ¬(old X0 X3 b) ∨ (new X0 c a) := resolve eq104 rfl -- equality resolution 104
  have eq111 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 84,70
  have eq120 (X0 : G) : ¬(new sk1 sk0 X0) ∨ sk3 = X0 := resolve prev_0 preserve_1 -- resolution 94,98
  have eq125 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) b) ∨ (new X0 c a) ∨ ¬(sP1 X0 X1 X2) := resolve eq105 rule_def_1_2 -- resolution 105,84
  have eq126 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c a) := resolve eq125 rule_def_1_3 -- subsumption resolution 125,85
  have eq136 (X0 X1 X2 X3 : G) : ¬(old X1 X0 (sF0 X1 X2 X3)) ∨ (old X0 X0 X1) ∨ ¬(old X0 X1 b) ∨ ¬(sP1 X1 X2 X3) := resolve old_3 rule_def_1_3 -- resolution 74,85
  have eq146 (X0 X1 : G) : ¬(new X0 sk0 X1) ∨ ¬(new X0 X1 sk1) ∨ (new X0 sk2 sk0) := resolve prev_1 preserve_0 -- resolution 95,97
  have eq154 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 93,97
  have eq155 : (sP2 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) := resolve new_imp preserve_1 -- resolution 93,98
  have eq156 : (sP2 sk1 sk3 sk2) ∨ (sP0 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ (sP1 sk1 sk3 sk2) := resolve new_imp preserve_2 -- resolution 93,99
  have eq164 : ¬(new sk1 sk3 sk1) ∨ (new sk1 sk2 sk0) := resolve eq146 preserve_1 -- resolution 146,98
  have eq197 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk2 := resolve eq154 rule_def_2_2 -- resolution 154,89
  have eq198 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq154 rule_def_2_1 -- resolution 154,88
  have eq199 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ b = sk0 := resolve eq154 rule_def_2_0 -- resolution 154,87
  have eq200 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq197 rule_def_1_1 -- subsumption resolution 197,83
  have eq201 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq198 rule_def_1_0 -- subsumption resolution 198,82
  have eq202 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq200 rule_def_0_2 -- resolution 200,80
  have eq203 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk1 := resolve eq200 rule_def_0_1 -- resolution 200,79
  have eq204 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ a = sk0 := resolve eq200 rule_def_0_0 -- resolution 200,78
  have eq207 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ a = sk3 := resolve eq155 rule_def_2_2 -- resolution 155,89
  have eq208 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ c = sk0 := resolve eq155 rule_def_2_1 -- resolution 155,88
  have eq210 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ a = sk3 := resolve eq207 rule_def_1_1 -- subsumption resolution 207,83
  have eq211 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ c = sk0 := resolve eq208 rule_def_1_0 -- subsumption resolution 208,82
  have eq219 : (sP0 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ (sP1 sk1 sk3 sk2) ∨ a = sk2 := resolve eq156 rule_def_2_2 -- resolution 156,89
  have eq220 : (sP0 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ (sP1 sk1 sk3 sk2) ∨ c = sk3 := resolve eq156 rule_def_2_1 -- resolution 156,88
  have eq221 : (sP1 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ (sP0 sk1 sk3 sk2) ∨ b = sk1 := resolve eq156 rule_def_2_0 -- resolution 156,87
  have eq222 : (sP0 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ a = sk2 := resolve eq219 rule_def_1_1 -- subsumption resolution 219,83
  have eq223 : (sP0 sk1 sk3 sk2) ∨ (old sk1 sk3 sk2) ∨ c = sk3 := resolve eq220 rule_def_1_0 -- subsumption resolution 220,82
  have eq238 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq201 rule_def_0_2 -- resolution 201,80
  have eq240 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq201 rule_def_0_0 -- resolution 201,78
  have eq264 (X0 X1 X2 : G) : (old a a X0) ∨ ¬(old a X0 b) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := resolve eq136 rule_def_1_2 -- resolution 136,84
  have eq265 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old a X0 b) ∨ (old a a X0) := resolve eq264 rfl -- duplicate literal removal 264
  have eq266 : (old sk1 sk0 sk3) ∨ a = sk3 ∨ c = sk3 := resolve eq210 rule_def_0_2 -- resolution 210,80
  have eq267 : (old sk1 sk0 sk3) ∨ a = sk3 ∨ b = sk0 := resolve eq210 rule_def_0_1 -- resolution 210,79
  have eq268 : (old sk1 sk0 sk3) ∨ a = sk3 ∨ a = sk1 := resolve eq210 rule_def_0_0 -- resolution 210,78
  have eq290 : (old sk1 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq211 rule_def_0_2 -- resolution 211,80
  have eq291 : (old sk1 sk0 sk3) ∨ c = sk0 ∨ b = sk0 := resolve eq211 rule_def_0_1 -- resolution 211,79
  have eq292 : (old sk1 sk0 sk3) ∨ c = sk0 ∨ a = sk1 := resolve eq211 rule_def_0_0 -- resolution 211,78
  have eq298 : (old sk1 sk3 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq222 rule_def_0_2 -- resolution 222,80
  have eq299 : (old sk1 sk3 sk2) ∨ a = sk2 ∨ b = sk3 := resolve eq222 rule_def_0_1 -- resolution 222,79
  have eq306 : (old sk1 sk3 sk2) ∨ c = sk3 ∨ c = sk2 := resolve eq223 rule_def_0_2 -- resolution 223,80
  have eq317 (X0 : G) : ¬(old sk1 X0 sk3) ∨ c = sk2 ∨ (old X0 X0 sk1) ∨ a = sk2 ∨ ¬(old X0 sk1 sk2) := resolve eq298 old_3 -- resolution 298,74
  have eq342 (X0 : G) : ¬(old sk1 X0 sk3) ∨ c = sk2 ∨ (old X0 X0 sk1) ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) := resolve eq306 old_3 -- resolution 306,74
  have eq377 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ (new sk0 c a) := resolve eq199 eq126 -- resolution 199,126
  have eq604 : (new sk0 c a) ∨ b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq377 rule_def_0_0 -- resolution 377,78
  have eq660 : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (sP1 sk0 c a) ∨ (sP0 sk0 c a) ∨ (old sk0 c a) ∨ (sP2 sk0 c a) := resolve eq604 new_imp -- resolution 604,93
  have eq663 : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (sP1 sk0 c a) ∨ (sP0 sk0 c a) ∨ (sP2 sk0 c a) := resolve eq660 p4XZ -- subsumption resolution 660,69
  have eq664 : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (sP1 sk0 c a) ∨ (sP2 sk0 c a) := resolve eq663 rule_def_0_0 -- subsumption resolution 663,78
  have eq665 : (sP1 sk0 c a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq664 rule_def_2_0 -- subsumption resolution 664,87
  have eq1139 : c = sk2 ∨ (old sk0 sk0 sk1) ∨ a = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk1 := resolve eq317 eq292 -- resolution 317,292
  have eq1140 : c = sk2 ∨ (old sk0 sk0 sk1) ∨ a = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ b = sk0 := resolve eq317 eq291 -- resolution 317,291
  have eq1141 : c = sk2 ∨ (old sk0 sk0 sk1) ∨ a = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk3 := resolve eq317 eq290 -- resolution 317,290
  have eq1145 : (old sk0 sk0 sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq1139 eq202 -- subsumption resolution 1139,202
  have eq1146 : (old sk0 sk0 sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1140 eq202 -- subsumption resolution 1140,202
  have eq1147 : (old sk0 sk0 sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ c = sk3 := resolve eq1141 eq202 -- subsumption resolution 1141,202
  have eq1185 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 ∨ (new sk0 sk0 sk1) := resolve eq1145 imp_new_0 -- resolution 1145,76
  have eq1198 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq1185 preserve_3 -- subsumption resolution 1185,100
  have eq1219 : (sP0 sk1 sk3 c) ∨ (old sk1 sk3 c) ∨ a = c ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 := Or.assoc3 (eq1198.imp_left (fun h : c = sk2 ↦ superpose h eq222)) -- superposition 222,1198, 1198 into 222, unify on (0).2 in 1198 and (0).3 in 222
  have eq1247 : (sP0 sk1 sk3 c) ∨ a = c ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq1219 p4XY -- subsumption resolution 1219,68
  have eq1248 : (sP0 sk1 sk3 c) ∨ a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq1247 ac -- subsumption resolution 1247,65
  have eq1249 : a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq1248 rule_def_0_0 -- subsumption resolution 1248,78
  have eq1380 : c = sk2 ∨ (old sk0 sk0 sk1) ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk3 := resolve eq342 eq290 -- resolution 342,290
  have eq1383 : c = sk2 ∨ (old sk0 sk0 sk1) ∨ c = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ a = sk3 ∨ c = sk3 := resolve eq342 eq266 -- resolution 342,266
  have eq1384 : ¬(old sk0 sk1 sk2) ∨ (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ a = sk3 := resolve eq1383 rfl -- duplicate literal removal 1383
  have eq1385 : ¬(old sk0 sk1 sk2) ∨ (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 := resolve eq1380 rfl -- duplicate literal removal 1380
  have eq1533 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 ∨ (new sk0 sk0 sk1) := resolve eq1146 imp_new_0 -- resolution 1146,76
  have eq1547 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1533 preserve_3 -- subsumption resolution 1533,100
  have eq1558 : (old sk0 sk1 c) ∨ a = c ∨ b = sk1 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := Or.assoc3 (eq1547.imp_left (fun h : c = sk2 ↦ superpose h eq203)) -- superposition 203,1547, 1547 into 203, unify on (0).2 in 1547 and (0).3 in 203
  have eq1559 : (old sk0 sk1 c) ∨ a = c ∨ a = sk0 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := Or.assoc3 (eq1547.imp_left (fun h : c = sk2 ↦ superpose h eq204)) -- superposition 204,1547, 1547 into 204, unify on (0).2 in 1547 and (0).3 in 204
  have eq1588 : a = c ∨ b = sk1 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1558 p4XY -- subsumption resolution 1558,68
  have eq1589 : a = sk2 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq1588 ac -- subsumption resolution 1588,65
  have eq1590 : a = c ∨ a = sk0 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1559 p4XY -- subsumption resolution 1559,68
  have eq1591 : a = sk2 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq1590 ac -- subsumption resolution 1590,65
  have eq2038 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ c = sk3 ∨ (new sk0 sk0 sk1) := resolve eq1147 imp_new_0 -- resolution 1147,76
  have eq2051 : c = sk3 ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := resolve eq2038 preserve_3 -- subsumption resolution 2038,100
  have eq2066 : (sP2 sk1 c sk2) ∨ (sP0 sk1 c sk2) ∨ (old sk1 c sk2) ∨ (sP1 sk1 c sk2) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := Or.assoc4 (eq2051.imp_left (fun h : c = sk3 ↦ superpose h eq156)) -- superposition 156,2051, 2051 into 156, unify on (0).2 in 2051 and (0).2 in 156
  have eq2144 : (sP2 sk1 c sk2) ∨ (sP0 sk1 c sk2) ∨ (sP1 sk1 c sk2) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := resolve eq2066 p4XZ -- subsumption resolution 2066,69
  have eq2145 : (sP2 sk1 c sk2) ∨ (sP1 sk1 c sk2) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := resolve eq2144 rule_def_0_2 -- subsumption resolution 2144,80
  have eq2146 : (sP2 sk1 c sk2) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := resolve eq2145 rule_def_1_1 -- subsumption resolution 2145,83
  have eq2147 : c = sk2 ∨ c = sk0 ∨ a = sk2 := resolve eq2146 rule_def_2_2 -- subsumption resolution 2146,89
  have eq2174 : (old sk0 sk1 c) ∨ a = c ∨ b = sk1 ∨ c = sk0 ∨ a = sk2 := Or.assoc3 (eq2147.imp_left (fun h : c = sk2 ↦ superpose h eq203)) -- superposition 203,2147, 2147 into 203, unify on (0).2 in 2147 and (0).3 in 203
  have eq2175 : (old sk0 sk1 c) ∨ a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk2 := Or.assoc3 (eq2147.imp_left (fun h : c = sk2 ↦ superpose h eq204)) -- superposition 204,2147, 2147 into 204, unify on (0).2 in 2147 and (0).3 in 204
  have eq2214 : a = c ∨ b = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq2174 p4XY -- subsumption resolution 2174,68
  have eq2215 : a = sk2 ∨ c = sk0 ∨ b = sk1 := resolve eq2214 ac -- subsumption resolution 2214,65
  have eq2216 : a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk2 := resolve eq2175 p4XY -- subsumption resolution 2175,68
  have eq2217 : a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq2216 ac -- subsumption resolution 2216,65
  have eq2320 : (new sk1 sk3 a) ∨ c = sk0 ∨ a = sk0 := eq2217.imp_left (fun h : a = sk2 ↦ superpose h preserve_2) -- superposition 99,2217, 2217 into 99, unify on (0).2 in 2217 and (0).3 in 99
  have eq4313 : (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1384 eq238 -- resolution 1384,238
  have eq4325 : (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := resolve eq4313 rfl -- duplicate literal removal 4313
  have eq4335 : (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq1385 eq238 -- resolution 1385,238
  have eq4354 : (old sk0 sk0 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq4335 rfl -- duplicate literal removal 4335
  have eq5923 : c = sk3 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 ∨ (new sk0 sk0 sk1) := resolve eq4325 imp_new_0 -- resolution 4325,76
  have eq5936 : c = sk3 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := resolve eq5923 preserve_3 -- subsumption resolution 5923,100
  have eq5965 : (old sk1 sk0 c) ∨ a = c ∨ b = sk0 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := Or.assoc3 (eq5936.imp_left (fun h : c = sk3 ↦ superpose h eq267)) -- superposition 267,5936, 5936 into 267, unify on (0).2 in 5936 and (0).3 in 267
  have eq5966 : (old sk1 sk0 c) ∨ a = c ∨ a = sk1 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := Or.assoc3 (eq5936.imp_left (fun h : c = sk3 ↦ superpose h eq268)) -- superposition 268,5936, 5936 into 268, unify on (0).2 in 5936 and (0).3 in 268
  have eq6096 : a = c ∨ b = sk0 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := resolve eq5965 p4XY -- subsumption resolution 5965,68
  have eq6097 : a = sk3 ∨ c = sk2 ∨ b = sk0 ∨ c = sk1 := resolve eq6096 ac -- subsumption resolution 6096,65
  have eq6098 : a = c ∨ a = sk1 ∨ c = sk2 ∨ a = sk3 ∨ c = sk1 := resolve eq5966 p4XY -- subsumption resolution 5966,68
  have eq6099 : a = sk3 ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq6098 ac -- subsumption resolution 6098,65
  have eq6957 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ (new sk0 sk0 sk1) := resolve eq4354 imp_new_0 -- resolution 4354,76
  have eq6970 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq6957 preserve_3 -- subsumption resolution 6957,100
  have eq6981 : a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ b = sk0 ∨ c = sk1 := Or.assoc4 (eq6097.imp_left (fun h : a = sk3 ↦ superpose h eq6970)) -- superposition 6970,6097, 6097 into 6970, unify on (0).2 in 6097 and (0).2 in 6970
  have eq6982 : a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq6099.imp_left (fun h : a = sk3 ↦ superpose h eq6970)) -- superposition 6970,6099, 6099 into 6970, unify on (0).2 in 6099 and (0).2 in 6970
  have eq6983 : (new sk1 sk0 c) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := eq6970.imp_left (fun h : c = sk3 ↦ superpose h preserve_1) -- superposition 98,6970, 6970 into 98, unify on (0).2 in 6970 and (0).3 in 98
  have eq7170 : a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 := resolve eq6982 rfl -- duplicate literal removal 6982
  have eq7171 : a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq6981 rfl -- duplicate literal removal 6981
  have eq7177 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq7171 ac -- subsumption resolution 7171,65
  have eq7178 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 := resolve eq7170 ac -- subsumption resolution 7170,65
  have eq7211 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc4 (eq1589.imp_left (fun h : a = sk2 ↦ superpose h eq7177)) -- superposition 7177,1589, 1589 into 7177, unify on (0).2 in 1589 and (0).2 in 7177
  have eq7212 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := Or.assoc4 (eq1591.imp_left (fun h : a = sk2 ↦ superpose h eq7177)) -- superposition 7177,1591, 1591 into 7177, unify on (0).2 in 1591 and (0).2 in 7177
  have eq7324 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ a = sk0 := resolve eq7212 rfl -- duplicate literal removal 7212
  have eq7325 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 := resolve eq7211 rfl -- duplicate literal removal 7211
  have eq7332 : b = sk1 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 := resolve eq7325 ac -- subsumption resolution 7325,65
  have eq7333 : c = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq7324 ac -- subsumption resolution 7324,65
  have eq7366 : a = c ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ a = sk1 := Or.assoc4 (eq1249.imp_left (fun h : a = sk2 ↦ superpose h eq7178)) -- superposition 7178,1249, 1249 into 7178, unify on (0).2 in 1249 and (0).2 in 7178
  have eq7495 : a = c ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 := resolve eq7366 rfl -- duplicate literal removal 7366
  have eq7500 : c = sk1 ∨ c = sk0 ∨ a = sk1 := resolve eq7495 ac -- subsumption resolution 7495,65
  have eq7523 : ¬(new sk0 sk0 c) ∨ c = sk0 ∨ a = sk1 := eq7500.imp_left (fun h : c = sk1 ↦ superpose h preserve_3) -- superposition 100,7500, 7500 into 100, unify on (0).2 in 7500 and (0).3 in 100
  have eq7569 : (old c sk0 sk3) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk1 := Or.assoc3 (eq7500.imp_left (fun h : c = sk1 ↦ superpose h eq291)) -- superposition 291,7500, 7500 into 291, unify on (0).2 in 7500 and (0).1 in 291
  have eq7570 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ c = sk0 ∨ a = sk1 := Or.assoc3 (eq7500.imp_left (fun h : c = sk1 ↦ superpose h eq292)) -- superposition 292,7500, 7500 into 292, unify on (0).2 in 7500 and (0).1 in 292
  have eq7895 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ a = sk1 := resolve eq7570 rfl -- duplicate literal removal 7570
  have eq7896 : (old c sk0 sk3) ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq7569 rfl -- duplicate literal removal 7569
  have eq7917 : a = sk1 ∨ b = sk0 ∨ c = sk0 := resolve eq7896 p4YZ -- subsumption resolution 7896,70
  have eq7918 : c = sk0 ∨ a = c ∨ a = sk1 := resolve eq7895 p4YZ -- subsumption resolution 7895,70
  have eq7919 : a = sk1 ∨ c = sk0 := resolve eq7918 ac -- subsumption resolution 7918,65
  have eq7935 (X0 : G) : ¬(new a sk0 X0) ∨ sk3 = X0 ∨ c = sk0 := Or.assoc2 (eq7919.imp_left (fun h : a = sk1 ↦ superpose h eq120)) -- superposition 120,7919, 7919 into 120, unify on (0).2 in 7919 and (0).1 in 120
  have eq7942 : ¬(new a sk3 a) ∨ (new a sk2 sk0) ∨ c = sk0 := Or.assoc2 (eq7919.imp_left (fun h : a = sk1 ↦ superpose h eq164)) -- superposition 164,7919, 7919 into 164, unify on (0).2 in 7919 and (0).1 in 164
  have eq8160 : (new a sk3 a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq7919.imp_left (fun h : a = sk1 ↦ superpose h eq2320)) -- superposition 2320,7919, 7919 into 2320, unify on (0).2 in 7919 and (0).1 in 2320
  have eq8226 : (new a sk3 a) ∨ c = sk0 ∨ a = sk0 := resolve eq8160 rfl -- duplicate literal removal 8160
  have eq10765 : (new a sk2 sk0) ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq7942 eq8226 -- resolution 7942,8226
  have eq10787 : (new a sk2 sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq10765 rfl -- duplicate literal removal 10765
  have eq10824 : (new a a sk0) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq2217.imp_left (fun h : a = sk2 ↦ superpose h eq10787)) -- superposition 10787,2217, 2217 into 10787, unify on (0).2 in 2217 and (0).2 in 10787
  have eq10831 : (new a a sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq10824 rfl -- duplicate literal removal 10824
  have eq10994 : c = sk0 ∨ a = sk0 ∨ (sP1 a a sk0) ∨ (sP0 a a sk0) ∨ (old a a sk0) ∨ (sP2 a a sk0) := resolve eq10831 new_imp -- resolution 10831,93
  have eq10997 : c = sk0 ∨ a = sk0 ∨ (sP0 a a sk0) ∨ (old a a sk0) ∨ (sP2 a a sk0) := resolve eq10994 rule_def_1_1 -- subsumption resolution 10994,83
  have eq10998 : c = sk0 ∨ a = sk0 ∨ (sP0 a a sk0) ∨ (old a a sk0) := resolve eq10997 rule_def_2_2 -- subsumption resolution 10997,89
  have eq10999 : (old a a sk0) ∨ a = sk0 ∨ c = sk0 := resolve eq10998 rule_def_0_2 -- subsumption resolution 10998,80
  have eq11886 : a = b ∨ a = c ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 := Or.assoc4 (eq7917.imp_left (fun h : a = sk1 ↦ superpose h eq7332)) -- superposition 7332,7917, 7917 into 7332, unify on (0).2 in 7917 and (0).2 in 7332
  have eq12314 : a = b ∨ a = c ∨ b = sk0 ∨ c = sk0 := resolve eq11886 rfl -- duplicate literal removal 11886
  have eq12315 : b = sk0 ∨ a = b ∨ c = sk0 := resolve eq12314 ac -- subsumption resolution 12314,65
  have eq12601 : (old a a b) ∨ a = b ∨ c = b ∨ a = b ∨ c = sk0 := Or.assoc3 (eq12315.imp_left (fun h : b = sk0 ↦ superpose h eq10999)) -- superposition 10999,12315, 12315 into 10999, unify on (0).2 in 12315 and (0).3 in 10999
  have eq12603 : (old a a b) ∨ a = b ∨ c = b ∨ c = sk0 := resolve eq12601 rfl -- duplicate literal removal 12601
  have eq12706 : (old a a b) ∨ a = b ∨ c = sk0 := resolve eq12603 bc -- subsumption resolution 12603,66
  have eq14234 : a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := Or.assoc4 (eq7917.imp_left (fun h : a = sk1 ↦ superpose h eq7333)) -- superposition 7333,7917, 7917 into 7333, unify on (0).2 in 7917 and (0).2 in 7333
  have eq14730 : a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq14234 rfl -- duplicate literal removal 14234
  have eq14732 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq14730 ac -- subsumption resolution 14730,65
  have eq19410 : (new a sk0 c) ∨ c = sk2 ∨ c = sk0 ∨ a = c ∨ c = sk0 := Or.assoc4 (eq7919.imp_left (fun h : a = sk1 ↦ superpose h eq6983)) -- superposition 6983,7919, 7919 into 6983, unify on (0).2 in 7919 and (0).1 in 6983
  have eq19413 : (new a sk0 c) ∨ c = sk2 ∨ c = sk0 ∨ a = c := resolve eq19410 rfl -- duplicate literal removal 19410
  have eq19422 : (new a sk0 c) ∨ c = sk2 ∨ c = sk0 := resolve eq19413 ac -- subsumption resolution 19413,65
  have eq19473 : c = sk2 ∨ c = sk0 ∨ c = sk3 ∨ c = sk0 := resolve eq19422 eq7935 -- resolution 19422,7935
  have eq19490 : c = sk3 ∨ c = sk0 ∨ c = sk2 := resolve eq19473 rfl -- duplicate literal removal 19473
  have eq19567 : (sP1 sk1 c sk2) ∨ (old sk1 c sk2) ∨ (sP0 sk1 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := Or.assoc4 (eq19490.imp_left (fun h : c = sk3 ↦ superpose h eq221)) -- superposition 221,19490, 19490 into 221, unify on (0).2 in 19490 and (0).2 in 221
  have eq19842 : (sP1 sk1 c sk2) ∨ (sP0 sk1 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := resolve eq19567 p4XZ -- subsumption resolution 19567,69
  have eq19843 : (sP1 sk1 c sk2) ∨ b = sk1 ∨ c = sk0 ∨ c = sk2 := resolve eq19842 rule_def_0_2 -- subsumption resolution 19842,80
  have eq32195 : (sP1 sk1 c a) ∨ b = sk1 ∨ c = sk0 ∨ a = c ∨ c = sk0 ∨ b = sk1 := Or.assoc4 (eq2215.imp_left (fun h : a = sk2 ↦ superpose h eq19843)) -- superposition 19843,2215, 2215 into 19843, unify on (0).2 in 2215 and (0).3 in 19843
  have eq32200 : (sP1 sk1 c a) ∨ b = sk1 ∨ c = sk0 ∨ a = c := resolve eq32195 rfl -- duplicate literal removal 32195
  have eq32217 : (sP1 sk1 c a) ∨ b = sk1 ∨ c = sk0 := resolve eq32200 ac -- subsumption resolution 32200,65
  have eq32290 : (sP1 a c a) ∨ a = b ∨ c = sk0 ∨ c = sk0 := Or.assoc3 (eq7919.imp_left (fun h : a = sk1 ↦ superpose h eq32217)) -- superposition 32217,7919, 7919 into 32217, unify on (0).2 in 7919 and (0).1 in 32217
  have eq32293 : (sP1 a c a) ∨ a = b ∨ c = sk0 := resolve eq32290 rfl -- duplicate literal removal 32290
  have eq32368 : a = b ∨ c = sk0 ∨ ¬(old a a b) ∨ (old a a a) := resolve eq32293 eq265 -- resolution 32293,265
  have eq32371 : a = b ∨ c = sk0 ∨ ¬(old a a b) := resolve eq32368 old_0 -- subsumption resolution 32368,71
  have eq32372 : c = sk0 ∨ a = b := resolve eq32371 eq12706 -- subsumption resolution 32371,12706
  have eq32511 : (sP1 c c a) ∨ (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = b := Or.assoc4 (eq32372.imp_left (fun h : c = sk0 ↦ superpose h eq665)) -- superposition 665,32372, 32372 into 665, unify on (0).2 in 32372 and (0).1 in 665
  have eq32804 : (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = b := resolve eq32511 eq111 -- subsumption resolution 32511,111
  have eq32805 : a = c ∨ c = b ∨ a = b := resolve eq32804 p4YZ -- subsumption resolution 32804,70
  have eq32806 : c = b ∨ a = b := resolve eq32805 ac -- subsumption resolution 32805,65
  have eq32807 : a = b := resolve eq32806 bc -- subsumption resolution 32806,66
  have eq32809 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 67,32807
  have eq32810 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 79,32807
  have eq32813 : ∀ (X0 X1 X2 : G) , (old a a (sF1 X0 X1 X2)) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 90,32807
  have eq32815 : (new a a c) := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq103 -- backward demodulation 103,32807
  have eq32878 : a = sk3 ∨ (old sk1 sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq299 -- backward demodulation 299,32807
  have eq34300 : a = sk0 ∨ c = sk0 ∨ a = sk0 := Eq.mp (by simp only [eq32807, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14732 -- backward demodulation 14732,32807
  have eq35375 : c = sk0 ∨ a = sk0 := resolve eq34300 rfl -- duplicate literal removal 34300
  have eq35578 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq32813 eq32809 -- subsumption resolution 32813,32809
  have eq36612 : (old c sk1 sk2) ∨ c = sk1 ∨ a = c ∨ a = sk0 := Or.assoc3 (eq35375.imp_left (fun h : c = sk0 ↦ superpose h eq240)) -- superposition 240,35375, 35375 into 240, unify on (0).2 in 35375 and (0).1 in 240
  have eq36688 : c = sk1 ∨ a = c ∨ a = sk0 := resolve eq36612 p4YZ -- subsumption resolution 36612,70
  have eq36689 : c = sk1 ∨ a = sk0 := resolve eq36688 ac -- subsumption resolution 36688,65
  have eq36799 : (sP2 c sk0 sk3) ∨ (sP0 c sk0 sk3) ∨ (old c sk0 sk3) ∨ (sP1 c sk0 sk3) ∨ a = sk0 := Or.assoc4 (eq36689.imp_left (fun h : c = sk1 ↦ superpose h eq155)) -- superposition 155,36689, 36689 into 155, unify on (0).2 in 36689 and (0).1 in 155
  have eq36960 : (sP0 c sk0 sk3) ∨ (old c sk0 sk3) ∨ (sP1 c sk0 sk3) ∨ a = sk0 := resolve eq36799 eq35578 -- subsumption resolution 36799,35578
  have eq36961 : (sP0 c sk0 sk3) ∨ (sP1 c sk0 sk3) ∨ a = sk0 := resolve eq36960 p4YZ -- subsumption resolution 36960,70
  have eq36962 : (sP0 c sk0 sk3) ∨ a = sk0 := resolve eq36961 eq111 -- subsumption resolution 36961,111
  have eq36963 : a = sk0 := resolve eq36962 eq32810 -- subsumption resolution 36962,32810
  have eq36965 : (new sk1 a sk3) := Eq.mp (by simp only [eq36963, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 98,36963
  have eq36966 : ¬(new a a sk1) := Eq.mp (by simp only [eq36963, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 100,36963
  have eq36986 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq36963, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq238 -- backward demodulation 238,36963
  have eq37245 : a = c ∨ ¬(new sk0 sk0 c) ∨ a = sk1 := Eq.mp (by simp only [eq36963, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7523 -- backward demodulation 7523,36963
  have eq38348 : ¬(new sk0 sk0 c) ∨ a = sk1 := resolve eq37245 ac -- subsumption resolution 37245,65
  have eq38349 : ¬(new a a c) ∨ a = sk1 := Eq.mp (by simp only [eq36963, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq38348 -- forward demodulation 38348,36963
  have eq38350 : a = sk1 := resolve eq38349 eq32815 -- subsumption resolution 38349,32815
  have eq38397 : (old a sk3 sk2) ∨ a = sk3 ∨ a = sk2 := Eq.mp (by simp only [eq38350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq32878 -- backward demodulation 32878,38350
  have eq38489 : (new a a sk3) := Eq.mp (by simp only [eq38350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq36965 -- backward demodulation 36965,38350
  have eq38490 : ¬(new a a a) := Eq.mp (by simp only [eq38350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq36966 -- backward demodulation 36966,38350
  have eq38497 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq38350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq36986 -- backward demodulation 36986,38350
  have eq38678 : (old a sk1 sk2) ∨ c = sk2 := resolve eq38497 ac -- subsumption resolution 38497,65
  have eq38679 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq38350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq38678 -- forward demodulation 38678,38350
  have eq38680 : c = sk2 := resolve eq38679 eq32809 -- subsumption resolution 38679,32809
  have eq38687 : a = c ∨ (old a sk3 sk2) ∨ a = sk3 := Eq.mp (by simp only [eq38680, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq38397 -- backward demodulation 38397,38680
  have eq38704 : (old a sk3 sk2) ∨ a = sk3 := resolve eq38687 ac -- subsumption resolution 38687,65
  have eq38705 : (old a sk3 c) ∨ a = sk3 := Eq.mp (by simp only [eq38680, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq38704 -- forward demodulation 38704,38680
  have eq38706 : a = sk3 := resolve eq38705 p4XY -- subsumption resolution 38705,68
  have eq38707 : (new a a a) := Eq.mp (by simp only [eq38706, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq38489 -- backward demodulation 38489,38706
  subsumption eq38490 eq38707 -- subsumption resolution 38707,38490

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X2 X0 X3 ∨ old X0 X3 X2)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ a ≠ Z ∨ ¬ old X a X2 ∨ ¬ old X X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z X1, b ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old b b X1 ∨ ¬ old b X1 a ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b (sF1 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old b (sF1 X Y Z) a ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X2 X0 X3 ∨ new X0 X3 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq104 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 79
  have eq105 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq104 rfl -- equality resolution 104
  have eq106 : (new a b c) := resolve eq105 rfl -- equality resolution 105
  have eq107 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old X0 X3 b) ∨ ¬(old X0 a X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 83
  have eq108 (X0 X3 : G) : ¬(old X0 a X3) ∨ ¬(old X0 X3 b) ∨ (new X0 c a) := resolve eq107 rfl -- equality resolution 107
  have eq109 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old b X3 a) ∨ ¬(old b b X3) ∨ c ≠ X1 ∨ b ≠ X0 := resolve imp_new_3 rfl -- equality resolution 88
  have eq110 (X0 X3 : G) : (new X0 c a) ∨ ¬(old b X3 a) ∨ ¬(old b b X3) ∨ b ≠ X0 := resolve eq109 rfl -- equality resolution 109
  have eq111 (X3 : G) : ¬(old b b X3) ∨ ¬(old b X3 a) ∨ (new b c a) := resolve eq110 rfl -- equality resolution 110
  have eq114 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 86,72
  have eq125 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq106 -- resolution 96,106
  have eq128 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) b) ∨ (new X0 c a) ∨ ¬(sP1 X0 X1 X2) := resolve eq108 rule_def_1_2 -- resolution 108,86
  have eq129 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c a) := resolve eq128 rule_def_1_3 -- subsumption resolution 128,87
  have eq131 (X0 X1 X2 : G) : ¬(old b (sF1 X0 X1 X2) a) ∨ (new b c a) ∨ ¬(sP2 X0 X1 X2) := resolve eq111 rule_def_2_3 -- resolution 111,92
  have eq132 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ (new b c a) := resolve eq131 rule_def_2_4 -- subsumption resolution 131,93
  have eq167 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 95,100
  have eq168 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 95,101
  have eq169 : (sP2 sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP1 sk2 sk0 sk3) := resolve new_imp preserve_2 -- resolution 95,102
  have eq211 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ a = sk1 := resolve eq167 rule_def_2_2 -- resolution 167,91
  have eq212 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ c = sk0 := resolve eq167 rule_def_2_1 -- resolution 167,90
  have eq213 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ b = sk0 := resolve eq167 rule_def_2_0 -- resolution 167,89
  have eq214 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk1 := resolve eq211 rule_def_1_1 -- subsumption resolution 211,85
  have eq215 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq212 rule_def_1_0 -- subsumption resolution 212,84
  have eq216 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq213 rule_def_0_1 -- subsumption resolution 213,81
  have eq221 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (new b c a) := resolve eq168 eq132 -- resolution 168,132
  have eq222 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk2 := resolve eq168 rule_def_2_2 -- resolution 168,91
  have eq223 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq168 rule_def_2_1 -- resolution 168,90
  have eq225 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq222 rule_def_1_1 -- subsumption resolution 222,85
  have eq226 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq223 rule_def_1_0 -- subsumption resolution 223,84
  have eq235 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP1 sk2 sk0 sk3) ∨ c = sk0 := resolve eq169 rule_def_2_1 -- resolution 169,90
  have eq236 : (sP1 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ b = sk2 := resolve eq169 rule_def_2_0 -- resolution 169,89
  have eq238 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ c = sk0 := resolve eq235 rule_def_1_0 -- subsumption resolution 235,84
  have eq253 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq215 rule_def_0_2 -- resolution 215,82
  have eq254 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ b = sk0 := resolve eq215 rule_def_0_1 -- resolution 215,81
  have eq255 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq215 rule_def_0_0 -- resolution 215,80
  have eq290 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk1 := resolve eq225 rule_def_0_1 -- resolution 225,81
  have eq291 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ a = sk0 := resolve eq225 rule_def_0_0 -- resolution 225,80
  have eq312 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq226 rule_def_0_2 -- resolution 226,82
  have eq313 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq226 rule_def_0_1 -- resolution 226,81
  have eq314 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq226 rule_def_0_0 -- resolution 226,80
  have eq323 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq238 rule_def_0_2 -- resolution 238,82
  have eq324 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ b = sk0 := resolve eq238 rule_def_0_1 -- resolution 238,81
  have eq325 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ a = sk2 := resolve eq238 rule_def_0_0 -- resolution 238,80
  have eq376 (X0 : G) : ¬(old sk0 sk0 X0) ∨ b = sk0 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 X0 sk2) ∨ c = sk0 := resolve eq324 old_4 -- resolution 324,77
  have eq383 (X0 : G) : ¬(old sk0 sk0 X0) ∨ a = sk2 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 X0 sk2) ∨ c = sk0 := resolve eq325 old_4 -- resolution 325,77
  have eq444 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (new b c a) ∨ (new sk0 c a) := resolve eq221 eq129 -- resolution 221,129
  have eq698 : (new sk0 c a) ∨ (new b c a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq444 rule_def_0_0 -- resolution 444,80
  have eq1524 : b = sk0 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq376 eq254 -- resolution 376,254
  have eq1531 : ¬(old sk0 sk1 sk2) ∨ (old sk0 sk3 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq1524 rfl -- duplicate literal removal 1524
  have eq1582 : a = sk2 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq383 eq255 -- resolution 383,255
  have eq1590 : a = sk2 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq1582 rfl -- duplicate literal removal 1582
  have eq1591 : (old sk0 sk3 sk2) ∨ a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq1590 eq291 -- subsumption resolution 1590,291
  have eq1596 : a = sk2 ∨ c = sk0 ∨ a = sk0 ∨ (new sk0 sk3 sk2) := resolve eq1591 imp_new_0 -- resolution 1591,78
  have eq1601 : a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq1596 preserve_3 -- subsumption resolution 1596,103
  have eq1604 : ¬(new sk0 sk3 a) ∨ c = sk0 ∨ a = sk0 := eq1601.imp_left (fun h : a = sk2 ↦ superpose h preserve_3) -- superposition 103,1601, 1601 into 103, unify on (0).2 in 1601 and (0).3 in 103
  have eq1840 : (old sk0 sk3 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := resolve eq1531 eq314 -- resolution 1531,314
  have eq1841 : (old sk0 sk3 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 := resolve eq1531 eq313 -- resolution 1531,313
  have eq1886 : b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 ∨ (new sk0 sk3 sk2) := resolve eq1840 imp_new_0 -- resolution 1840,78
  have eq1894 : c = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq1886 preserve_3 -- subsumption resolution 1886,103
  have eq1899 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := Or.assoc4 (eq1894.imp_left (fun h : c = sk1 ↦ superpose h eq167)) -- superposition 167,1894, 1894 into 167, unify on (0).2 in 1894 and (0).3 in 167
  have eq1973 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq1899 p4XY -- subsumption resolution 1899,70
  have eq1974 : (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq1973 rule_def_0_0 -- subsumption resolution 1973,80
  have eq1975 : (sP1 sk0 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq1974 rule_def_2_0 -- subsumption resolution 1974,89
  have eq1976 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq1975 rule_def_1_0 -- subsumption resolution 1975,84
  have eq1993 : (new sk2 b sk3) ∨ c = sk0 ∨ a = sk0 := eq1976.imp_left (fun h : b = sk0 ↦ superpose h preserve_2) -- superposition 102,1976, 1976 into 102, unify on (0).2 in 1976 and (0).2 in 102
  have eq1994 : ¬(new b sk3 sk2) ∨ c = sk0 ∨ a = sk0 := eq1976.imp_left (fun h : b = sk0 ↦ superpose h preserve_3) -- superposition 103,1976, 1976 into 103, unify on (0).2 in 1976 and (0).1 in 103
  have eq2029 : (old b b sk1) ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1976.imp_left (fun h : b = sk0 ↦ superpose h eq253)) -- superposition 253,1976, 1976 into 253, unify on (0).2 in 1976 and (0).1 in 253
  have eq2145 : a ≠ b ∨ c = sk0 ∨ a = sk0 := resolve eq1976 trans_resol -- equality factoring 1976
  have eq2157 : (old b b sk1) ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2029 bc -- subsumption resolution 2029,68
  have eq2268 : (new a b sk3) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1601.imp_left (fun h : a = sk2 ↦ superpose h eq1993)) -- superposition 1993,1601, 1601 into 1993, unify on (0).2 in 1601 and (0).1 in 1993
  have eq2273 : (new a b sk3) ∨ c = sk0 ∨ a = sk0 := resolve eq2268 rfl -- duplicate literal removal 2268
  have eq2286 : ¬(new b sk3 a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1601.imp_left (fun h : a = sk2 ↦ superpose h eq1994)) -- superposition 1994,1601, 1601 into 1994, unify on (0).2 in 1601 and (0).3 in 1994
  have eq2287 : ¬(new b sk3 a) ∨ c = sk0 ∨ a = sk0 := resolve eq2286 rfl -- duplicate literal removal 2286
  have eq2318 : c = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq2273 eq125 -- resolution 2273,125
  have eq2342 : ¬(new sk0 c sk2) ∨ a = sk0 ∨ c = sk0 := eq2318.imp_left (fun h : c = sk3 ↦ superpose h preserve_3) -- superposition 103,2318, 2318 into 103, unify on (0).2 in 2318 and (0).2 in 103
  have eq2376 : ¬(new sk0 c a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq2318.imp_left (fun h : c = sk3 ↦ superpose h eq1604)) -- superposition 1604,2318, 2318 into 1604, unify on (0).2 in 2318 and (0).2 in 1604
  have eq2396 : ¬(new sk0 c a) ∨ c = sk0 ∨ a = sk0 := resolve eq2376 rfl -- duplicate literal removal 2376
  have eq2432 : ¬(new b c a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq2318.imp_left (fun h : c = sk3 ↦ superpose h eq2287)) -- superposition 2287,2318, 2318 into 2287, unify on (0).2 in 2318 and (0).2 in 2287
  have eq2437 : ¬(new b c a) ∨ c = sk0 ∨ a = sk0 := resolve eq2432 rfl -- duplicate literal removal 2432
  have eq2557 : c = sk0 ∨ a = sk0 ∨ (new b c a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq2396 eq698 -- resolution 2396,698
  have eq2559 : c = sk0 ∨ a = sk0 ∨ (new b c a) ∨ (old sk0 sk1 sk2) := resolve eq2557 rfl -- duplicate literal removal 2557
  have eq2564 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := resolve eq2559 eq2437 -- subsumption resolution 2559,2437
  have eq2688 : (old sk0 sk1 a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1601.imp_left (fun h : a = sk2 ↦ superpose h eq2564)) -- superposition 2564,1601, 1601 into 2564, unify on (0).2 in 1601 and (0).3 in 2564
  have eq2689 : (old sk0 sk1 a) ∨ a = sk0 ∨ c = sk0 := resolve eq2688 rfl -- duplicate literal removal 2688
  have eq2752 : (old b sk1 a) ∨ a = b ∨ c = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1976.imp_left (fun h : b = sk0 ↦ superpose h eq2689)) -- superposition 2689,1976, 1976 into 2689, unify on (0).2 in 1976 and (0).1 in 2689
  have eq2759 : (old b sk1 a) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq2752 bc -- subsumption resolution 2752,68
  have eq2760 : (old b sk1 a) ∨ c = sk0 ∨ a = sk0 := resolve eq2759 eq2145 -- subsumption resolution 2759,2145
  have eq3050 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ ¬(old b sk1 a) ∨ (new b c a) := resolve eq2157 eq111 -- resolution 2157,111
  have eq3059 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ (new b c a) := resolve eq3050 eq2760 -- subsumption resolution 3050,2760
  have eq3060 : c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3059 eq2437 -- subsumption resolution 3059,2437
  have eq3063 : (new sk0 c sk2) ∨ c = sk0 ∨ a = sk0 := eq3060.imp_left (fun h : c = sk1 ↦ superpose h preserve_1) -- superposition 101,3060, 3060 into 101, unify on (0).2 in 3060 and (0).2 in 101
  have eq3177 : c = sk0 ∨ a = sk0 := resolve eq3063 eq2342 -- subsumption resolution 3063,2342
  have eq3199 : (sP1 c c sk1) ∨ (old c c sk1) ∨ c = b ∨ a = sk0 := Or.assoc3 (eq3177.imp_left (fun h : c = sk0 ↦ superpose h eq216)) -- superposition 216,3177, 3177 into 216, unify on (0).2 in 3177 and (0).1 in 216
  have eq3362 : (old c c sk1) ∨ c = b ∨ a = sk0 := resolve eq3199 eq114 -- subsumption resolution 3199,114
  have eq3363 : c = b ∨ a = sk0 := resolve eq3362 p4YZ -- subsumption resolution 3362,72
  have eq3364 : a = sk0 := resolve eq3363 bc -- subsumption resolution 3363,68
  have eq3366 : (new a sk1 sk2) := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 101,3364
  have eq3368 : ¬(new a sk3 sk2) := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 103,3364
  have eq3387 : (sP0 a a sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq214 -- backward demodulation 214,3364
  have eq3404 : (sP1 sk2 a sk3) ∨ (old sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ b = sk2 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq236 -- backward demodulation 236,3364
  have eq3411 : (old a a sk1) ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq253 -- backward demodulation 253,3364
  have eq3434 : (old a sk1 sk2) ∨ a = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq290 -- backward demodulation 290,3364
  have eq3445 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq312 -- backward demodulation 312,3364
  have eq3455 : (old sk2 a sk3) ∨ c = sk0 ∨ c = sk3 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq323 -- backward demodulation 323,3364
  have eq3933 : a = c ∨ (old sk0 sk3 sk2) ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1841 -- backward demodulation 1841,3364
  have eq4260 : (sP0 a a sk1) ∨ (old a a sk1) ∨ a = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3387 -- forward demodulation 3387,3364
  have eq4288 : (old sk2 a sk3) ∨ (sP1 sk2 a sk3) ∨ (sP0 sk2 sk0 sk3) ∨ b = sk2 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3404 -- forward demodulation 3404,3364
  have eq4289 : (sP1 sk2 a sk3) ∨ (old sk2 a sk3) ∨ (sP0 sk2 a sk3) ∨ b = sk2 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4288 -- forward demodulation 4288,3364
  have eq4304 : a = c ∨ (old a a sk1) ∨ c = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3411 -- forward demodulation 3411,3364
  have eq4305 : (old a a sk1) ∨ c = sk1 := resolve eq4304 ac -- subsumption resolution 4304,67
  have eq4374 : a = c ∨ (old sk2 a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3455 -- forward demodulation 3455,3364
  have eq4375 : (old sk2 a sk3) ∨ c = sk3 := resolve eq4374 ac -- subsumption resolution 4374,67
  have eq5015 : (old sk0 sk3 sk2) ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := resolve eq3933 ac -- subsumption resolution 3933,67
  have eq5016 : (old a sk3 sk2) ∨ b = sk0 ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5015 -- forward demodulation 5015,3364
  have eq5017 : (old a sk3 sk2) ∨ a = b ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3364, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5016 -- forward demodulation 5016,3364
  have eq5760 : a = b ∨ c = sk1 ∨ b = sk1 ∨ (new a sk3 sk2) := resolve eq5017 imp_new_0 -- resolution 5017,78
  have eq5761 : b = sk1 ∨ c = sk1 ∨ a = b := resolve eq5760 eq3368 -- subsumption resolution 5760,3368
  have eq5769 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 ∨ a = b := Or.assoc3 (eq5761.imp_left (fun h : b = sk1 ↦ superpose h eq3445)) -- superposition 3445,5761, 5761 into 3445, unify on (0).2 in 5761 and (0).2 in 3445
  have eq5808 : c = b ∨ c = sk2 ∨ c = sk1 ∨ a = b := resolve eq5769 p3 -- subsumption resolution 5769,69
  have eq5809 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq5808 bc -- subsumption resolution 5808,68
  have eq5843 : (sP1 c a sk3) ∨ (old c a sk3) ∨ (sP0 c a sk3) ∨ c = b ∨ c = sk1 ∨ a = b := Or.assoc4 (eq5809.imp_left (fun h : c = sk2 ↦ superpose h eq4289)) -- superposition 4289,5809, 5809 into 4289, unify on (0).2 in 5809 and (0).1 in 4289
  have eq5897 : (old c a sk3) ∨ (sP0 c a sk3) ∨ c = b ∨ c = sk1 ∨ a = b := resolve eq5843 eq114 -- subsumption resolution 5843,114
  have eq5898 : (sP0 c a sk3) ∨ c = b ∨ c = sk1 ∨ a = b := resolve eq5897 p4YZ -- subsumption resolution 5897,72
  have eq5899 : (sP0 c a sk3) ∨ c = sk1 ∨ a = b := resolve eq5898 bc -- subsumption resolution 5898,68
  have eq5900 : c = sk1 ∨ a = b := resolve eq5899 rule_def_0_1 -- subsumption resolution 5899,81
  have eq5920 : (sP0 a a c) ∨ (old a a c) ∨ a = c ∨ a = b := Or.assoc3 (eq5900.imp_left (fun h : c = sk1 ↦ superpose h eq4260)) -- superposition 4260,5900, 5900 into 4260, unify on (0).2 in 5900 and (0).3 in 4260
  have eq5953 : (sP0 a a c) ∨ a = c ∨ a = b := resolve eq5920 p4XY -- subsumption resolution 5920,70
  have eq5954 : (sP0 a a c) ∨ a = b := resolve eq5953 ac -- subsumption resolution 5953,67
  have eq5955 : a = b := resolve eq5954 rule_def_0_1 -- subsumption resolution 5954,81
  have eq5957 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 69,5955
  have eq6016 : a = sk1 ∨ (old a sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3434 -- backward demodulation 3434,5955
  have eq6169 : c = sk1 := resolve eq5957 eq4305 -- resolution 5957,4305
  have eq6172 : (new a c sk2) := Eq.mp (by simp only [eq6169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3366 -- backward demodulation 3366,6169
  have eq6209 : a = c ∨ (old a sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq6169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6016 -- backward demodulation 6016,6169
  have eq6256 : (old a sk1 sk2) ∨ a = sk2 := resolve eq6209 ac -- subsumption resolution 6209,67
  have eq6257 : (old a c sk2) ∨ a = sk2 := Eq.mp (by simp only [eq6169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6256 -- forward demodulation 6256,6169
  have eq6258 : a = sk2 := resolve eq6257 p4XZ -- subsumption resolution 6257,71
  have eq6260 : ¬(new a sk3 a) := Eq.mp (by simp only [eq6258, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3368 -- backward demodulation 3368,6258
  have eq6272 : (old a a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq6258, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4375 -- backward demodulation 4375,6258
  have eq6281 : (new a c a) := Eq.mp (by simp only [eq6258, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6172 -- backward demodulation 6172,6258
  have eq6301 : c = sk3 := resolve eq6272 eq5957 -- subsumption resolution 6272,5957
  have eq6303 : ¬(new a c a) := Eq.mp (by simp only [eq6301, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6260 -- backward demodulation 6260,6301
  subsumption eq6303 eq6281 -- subsumption resolution 6281,6303

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq115 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X0 := resolve rule_def_1_2 old_mem1 -- resolution 85,95
  have eq149 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 94,98
  have eq187 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk0 := resolve eq149 rule_def_2_0 -- resolution 149,88
  have eq194 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq187 preserve_2 -- subsumption resolution 187,100
  have eq199 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk0 := resolve eq194 eq115 -- resolution 194,115
  have eq202 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq199 preserve_3 -- subsumption resolution 199,101
  have eq207 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq202 rule_def_0_0 -- resolution 202,79
  have eq208 : (old sk0 sk1 sk2) := resolve eq207 preserve_1 -- subsumption resolution 207,99
  have eq216 : memold sk0 := resolve eq208 old_mem1 -- resolution 208,95
  subsumption preserve_3 eq216 -- subsumption resolution 216,101

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq149 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 94,98
  have eq188 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq149 rule_def_2_1 -- resolution 149,89
  have eq194 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq188 preserve_4 -- subsumption resolution 188,102
  have eq195 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq194 rule_def_1_0 -- resolution 194,83
  have eq202 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq195 preserve_4 -- subsumption resolution 195,102
  have eq206 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq202 rule_def_0_1 -- resolution 202,80
  have eq208 : (old sk0 sk1 sk2) := resolve eq206 preserve_2 -- subsumption resolution 206,100
  have eq217 : memold sk1 := resolve eq208 old_mem2 -- resolution 208,96
  subsumption preserve_3 eq217 -- subsumption resolution 217,101

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq149 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 94,98
  have eq188 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq149 rule_def_2_1 -- resolution 149,89
  have eq189 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk2 := resolve eq149 rule_def_2_2 -- resolution 149,90
  have eq194 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq188 rule_def_1_0 -- subsumption resolution 188,83
  have eq195 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve eq189 preserve_1 -- subsumption resolution 189,99
  have eq196 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq194 rule_def_0_2 -- resolution 194,81
  have eq199 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq196 preserve_4 -- subsumption resolution 196,102
  have eq208 : c = sk1 ∨ memold sk2 := resolve eq199 old_mem3 -- resolution 199,97
  have eq209 : c = sk1 := resolve eq208 preserve_3 -- subsumption resolution 208,101
  have eq214 : (sP1 sk0 c sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq209, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq195 -- backward demodulation 195,209
  have eq223 : (sP0 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq209, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq214 -- forward demodulation 214,209
  have eq224 : (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP1 sk0 c sk2) := Eq.mp (by simp only [eq209, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq223 -- forward demodulation 223,209
  have eq225 : (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) := resolve eq224 p4XZ -- subsumption resolution 224,70
  have eq235 : (sP0 sk0 c sk2) ∨ a = sk2 := resolve eq225 rule_def_1_1 -- resolution 225,84
  have eq242 : (sP0 sk0 c sk2) := resolve eq235 preserve_1 -- subsumption resolution 235,99
  have eq245 : c = sk2 := resolve eq242 rule_def_0_2 -- resolution 242,81
  subsumption preserve_4 eq245 -- subsumption resolution 245,102

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X2 X3 ∨ ¬ R X1 X3 X4 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1, ¬ R X0 X1 X0 ∨ ¬ R X1 X0 X0 ∨ R X0 X0 X1)
  rule_3 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X1 X0 X3 ∨ ¬ R X1 X3 X2 ∨ R X0 X0 X1)
  rule_4 : (∀ X0 X1 X2 X3, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X2 X0 X3 ∨ R X0 X3 X2)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp  

variable {G : Type*} (ps : PartialSolution G)

set_option linter.all false in
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ ps.R a b X0)
    (p4XY : ∀ X1 X2, ¬ ps.R X1 X2 c) (p4XZ : ∀ X1 X2, ¬ ps.R X1 c X2) (p4YZ : ∀ X1 X2, ¬ ps.R c X1 X2)
    : ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by classical
  let sP0 (X Y Z) := a = X ∧ b = Y ∧ c = Z
  have hsP0 (X Y Z) (h : sP0 X Y Z) : a = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP0
  obtain ⟨rule_def_0_0, rule_def_0_1, rule_def_0_2⟩ := hsP0
  simp_rw [or_comm] at rule_def_0_0 rule_def_0_1 rule_def_0_2
  let sP1 (X Y Z) := ∃ sF0, c = Y ∧ a = Z ∧ ps.R X a sF0 ∧ ps.R X sF0 b
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := ∃ sF1, b = X ∧ c = Y ∧ a = Z ∧ ps.R b b sF1 ∧ ps.R b sF1 a
  choose! sF1 hsP2 using fun (X Y Z) (h : sP2 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3, rule_def_2_4⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 ps.rule_1 ps.rule_3 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4YZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 prev_1 ps.rule_3 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_4 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_2 rule_def_2_0 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_0 rule_def_2_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) p4XZ rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 new_imp ps.mem_3
  }, by simp only [new_new, imp_iff_not_or, imp_new_0, implies_true, and_self]⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_not_mem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_not_mem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by simp_all [eq_comm]) (by simp_all)
        (by simpa using h) (fun _ _ h ↦ by have := (ps.mem_3 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_2 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_1 _ _ _).neg_resolve_left h; simp_all)).choose

lemma PartialSolution.addArbitrary_covers [Infinite G] (a b : G) :
    ∃ c, (ps.addArbitrary a b).R a b c := by
  unfold addArbitrary
  split
  · assumption
  · generalize_proofs h1 h2 h3
    exact ⟨h1.choose, (h3 h2).choose_spec.1⟩

lemma PartialSolution.addArbitrary_contains [Infinite G] (a b : G) :
    ∀ x y z, ps.R x y z → (ps.addArbitrary a b).R x y z := by
  unfold addArbitrary
  split
  · simp
  · generalize_proofs v1 v2 v3
    exact (v3 v2).choose_spec.2

variable (ps : PartialSolution ℕ)

include ps in
noncomputable def PartialSolution.complSeq : ℕ → PartialSolution ℕ
| 0 => ps
| n+1 => (complSeq n).addArbitrary n.unpair.1 n.unpair.2

lemma PartialSolution.complSeq_exists (a b : ℕ) : ∃ c, (complSeq ps (Nat.pair a b + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_covers

lemma PartialSolution.complSeq_mono_add_one (i : ℕ) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps (i + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_contains
  exact h

lemma PartialSolution.complSeq_mono (i j : ℕ) (hij : i ≤ j) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps j).R a b c := by
  induction hij
  · exact h
  · apply ps.complSeq_mono_add_one
    assumption

lemma PartialSolution.complSeq_exists_of_lt (a b i : ℕ) (h : Nat.pair a b < i) :
    ∃ c, (complSeq ps i).R a b c := by
  obtain ⟨c, hc⟩ := ps.complSeq_exists a b
  use c
  apply complSeq_mono _ _ _ _ _ _ _ hc
  omega

noncomputable def PartialSolution.compl (a b c : ℕ) : Prop :=
  (ps.complSeq (Nat.pair a b + 1)).R a b c

theorem PartialSolution.compl_rule0 (a b c d : ℕ)
    (h : ps.compl a b c) (h2 : ps.compl a b d) : c = d := by
  unfold compl at *
  have := (ps.complSeq (Nat.pair a b + 1)).rule_0 a b c d
  simp_all

theorem PartialSolution.compl_exists (a b : ℕ) : ∃ c, ps.compl a b c :=
  complSeq_exists ..

lemma PartialSolution.complSeq_of_compl_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) (h : ps.compl a b c) : (ps.complSeq i).R a b c :=
  PartialSolution.complSeq_mono _ _ _ (by omega) _ _ _ h

lemma PartialSolution.complSeq_iff_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) : ps.compl a b c ↔ (ps.complSeq i).R a b c := by
  constructor
  · intro
    apply PartialSolution.complSeq_of_compl_of_lt <;> assumption
  · intro h
    have ⟨c', hc⟩ := ps.compl_exists a b
    convert hc
    have := ps.complSeq_of_compl_of_lt a b i habi c' hc
    have := (ps.complSeq i).rule_0 a b c c'
    simp_all

theorem PartialSolution.compl_rule1 (X0 X1 X2 X3 X4 : ℕ) :
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X0 X2 X3 ∨ ¬ ps.compl X1 X3 X4 ∨ ps.compl X0 X4 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X0 X2) (max (Nat.pair X1 X3) (max (Nat.pair X0 X4) 0)))
  repeat rw [PartialSolution.complSeq_iff_of_lt _ _ _ i]
  apply PartialSolution.rule_1
  all_goals omega

noncomputable def PartialSolution.complFun (a b : ℕ) : ℕ := (ps.compl_exists a b).choose

theorem PartialSolution.complFun_eq_iff (a b c : ℕ) : ps.complFun a b = c ↔ ps.compl a b c := by
  constructor
  · rintro rfl
    exact (ps.compl_exists a b).choose_spec
  · intro h
    have : ps.compl a b (ps.complFun a b) := (ps.compl_exists a b).choose_spec
    exact ps.compl_rule0 a b _ _ this h

lemma PartialSolution.of_R (a b c : ℕ) (h : ps.R a b c) : ps.complFun a b = c := by
  rw [PartialSolution.complFun_eq_iff]
  apply PartialSolution.complSeq_mono _ 0 _ (by simp) _ _ _ h

noncomputable def PartialSolution.toMagma : Magma ℕ where
  op := ps.complFun

theorem PartialSolution.toMagma_equation476 :
    letI := ps.toMagma
    Equation476 ℕ := by
  simp only [Equation476, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun X1 (ps.complFun X1 X0)) (ps.complFun X0 (ps.complFun X1 (ps.complFun X1 X0)))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter359 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation476_not_implies_Equation359 : ∃ (G : Type) (_ : Magma G), Equation476 G ∧ ¬Equation359 G := by
  use ℕ, PartialSolution.counter359.toMagma, PartialSolution.counter359.toMagma_equation476
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter359.of_R 1 1 2] | rw [PartialSolution.counter359.of_R 2 1 3])
  all_goals simp [PartialSolution.counter359]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3862 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (1, 4, 3), (3, 1, 4)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3, 4}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation476_not_implies_Equation3862 : ∃ (G : Type) (_ : Magma G), Equation476 G ∧ ¬Equation3862 G := by
  use ℕ, PartialSolution.counter3862.toMagma, PartialSolution.counter3862.toMagma_equation476
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3862.of_R 1 1 2] | rw [PartialSolution.counter3862.of_R 1 2 3] | rw [PartialSolution.counter3862.of_R 1 4 3] | rw [PartialSolution.counter3862.of_R 3 1 4])
  all_goals simp [PartialSolution.counter3862]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter4065 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 3), (3, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation476_not_implies_Equation4065 : ∃ (G : Type) (_ : Magma G), Equation476 G ∧ ¬Equation4065 G := by
  use ℕ, PartialSolution.counter4065.toMagma, PartialSolution.counter4065.toMagma_equation476
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter4065.of_R 1 1 2] | rw [PartialSolution.counter4065.of_R 2 1 3] | rw [PartialSolution.counter4065.of_R 3 1 3])
  all_goals simp [PartialSolution.counter4065]

end Eq476