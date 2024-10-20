import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq1112

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq124 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 83,84
  have eq125 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 83,85
  have eq157 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk2 := resolve eq124 rule_def_2_2 -- resolution 124,79
  have eq158 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq124 rule_def_2_1 -- resolution 124,78
  have eq160 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq157 rule_def_1_1 -- subsumption resolution 157,73
  have eq161 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq158 rule_def_1_0 -- subsumption resolution 158,72
  have eq164 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq160 rule_def_0_1 -- resolution 160,69
  have eq165 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ a = sk0 := resolve eq160 rule_def_0_0 -- resolution 160,68
  have eq169 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ b = sk3 := resolve eq125 rule_def_2_2 -- resolution 125,79
  have eq170 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ c = sk1 := resolve eq125 rule_def_2_1 -- resolution 125,78
  have eq172 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 := resolve eq169 rule_def_1_1 -- subsumption resolution 169,73
  have eq173 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq170 rule_def_1_0 -- subsumption resolution 170,72
  have eq181 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk2 := resolve eq164 old_0 -- resolution 164,62
  have eq186 (X0 : G) : ¬(old sk0 sk1 X0) ∨ a = sk0 ∨ sk2 = X0 ∨ b = sk2 := resolve eq165 old_0 -- resolution 165,62
  have eq191 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq161 rule_def_0_2 -- resolution 161,70
  have eq197 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq191 old_0 -- resolution 191,62
  have eq217 : (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq172 rule_def_0_2 -- resolution 172,70
  have eq218 : (old sk0 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq172 rule_def_0_1 -- resolution 172,69
  have eq221 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq173 rule_def_0_1 -- resolution 173,69
  have eq222 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq173 rule_def_0_0 -- resolution 173,68
  have eq461 : b = sk1 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq181 eq221 -- resolution 181,221
  have eq467 : b = sk1 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 := resolve eq461 rfl -- duplicate literal removal 461
  have eq473 : b = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq467 preserve_2 -- subsumption resolution 467,86
  have eq601 : a = sk0 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq186 eq222 -- resolution 186,222
  have eq610 : a = sk0 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 := resolve eq601 rfl -- duplicate literal removal 601
  have eq615 : b = sk2 ∨ a = sk0 ∨ c = sk1 := resolve eq610 preserve_2 -- subsumption resolution 610,86
  have eq737 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq197 eq222 -- resolution 197,222
  have eq738 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq197 eq221 -- resolution 197,221
  have eq748 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq738 rfl -- duplicate literal removal 738
  have eq749 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq737 rfl -- duplicate literal removal 737
  have eq754 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq749 preserve_2 -- subsumption resolution 749,86
  have eq755 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq748 preserve_2 -- subsumption resolution 748,86
  have eq757 : c = b ∨ c = sk1 ∨ a = sk0 ∨ a = sk0 ∨ c = sk1 := Or.assoc3 (eq615.imp_left (fun h : b = sk2 ↦ superpose h eq754)) -- superposition 754,615, 615 into 754, unify on (0).2 in 615 and (0).2 in 754
  have eq788 : c = b ∨ c = sk1 ∨ a = sk0 := resolve eq757 rfl -- duplicate literal removal 757
  have eq789 : c = sk1 ∨ a = sk0 := resolve eq788 bc -- subsumption resolution 788,57
  have eq795 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ b = sk2 ∨ a = sk0 := Or.assoc3 (eq789.imp_left (fun h : c = sk1 ↦ superpose h eq160)) -- superposition 160,789, 789 into 160, unify on (0).2 in 789 and (0).2 in 160
  have eq801 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ b = sk3 ∨ a = sk0 := Or.assoc3 (eq789.imp_left (fun h : c = sk1 ↦ superpose h eq172)) -- superposition 172,789, 789 into 172, unify on (0).2 in 789 and (0).2 in 172
  have eq827 : (sP0 sk0 c sk2) ∨ b = sk2 ∨ a = sk0 := resolve eq795 p4XZ -- subsumption resolution 795,60
  have eq828 : b = sk2 ∨ a = sk0 := resolve eq827 rule_def_0_0 -- subsumption resolution 827,68
  have eq829 : (sP0 sk0 c sk3) ∨ b = sk3 ∨ a = sk0 := resolve eq801 p4XZ -- subsumption resolution 801,60
  have eq830 : b = sk3 ∨ a = sk0 := resolve eq829 rule_def_0_0 -- subsumption resolution 829,68
  have eq880 : b ≠ sk2 ∨ a = sk0 := eq830.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 86,830, 830 into 86, unify on (0).2 in 830 and (0).2 in 86
  have eq892 : a = sk0 := resolve eq880 eq828 -- subsumption resolution 880,828
  have eq901 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq161 -- backward demodulation 161,892
  have eq904 : (old a sk1 sk2) ∨ b = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq164 -- backward demodulation 164,892
  have eq910 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq173 -- backward demodulation 173,892
  have eq933 : (old a sk1 sk3) ∨ b = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq217 -- backward demodulation 217,892
  have eq934 : (old a sk1 sk3) ∨ b = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq218 -- backward demodulation 218,892
  have eq1049 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq901 -- forward demodulation 901,892
  have eq1059 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq892, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq910 -- forward demodulation 910,892
  have eq1209 : c = b ∨ c = sk1 ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq473.imp_left (fun h : b = sk2 ↦ superpose h eq755)) -- superposition 755,473, 473 into 755, unify on (0).2 in 473 and (0).2 in 755
  have eq1213 : c = b ∨ c = sk1 ∨ b = sk1 := resolve eq1209 rfl -- duplicate literal removal 1209
  have eq1215 : b = sk1 ∨ c = sk1 := resolve eq1213 bc -- subsumption resolution 1213,57
  have eq1266 : (sP0 a b sk2) ∨ (old a b sk2) ∨ c = b ∨ c = sk1 := Or.assoc3 (eq1215.imp_left (fun h : b = sk1 ↦ superpose h eq1049)) -- superposition 1049,1215, 1215 into 1049, unify on (0).2 in 1215 and (0).2 in 1049
  have eq1273 : (sP0 a b sk2) ∨ c = b ∨ c = sk1 := resolve eq1266 p3 -- subsumption resolution 1266,58
  have eq1274 : (sP0 a b sk2) ∨ c = sk1 := resolve eq1273 bc -- subsumption resolution 1273,57
  have eq1275 : c = sk2 ∨ c = sk1 := resolve eq1274 rule_def_0_2 -- resolution 1274,70
  have eq1311 : (sP0 a b sk3) ∨ (old a b sk3) ∨ c = b ∨ c = sk1 := Or.assoc3 (eq1215.imp_left (fun h : b = sk1 ↦ superpose h eq1059)) -- superposition 1059,1215, 1215 into 1059, unify on (0).2 in 1215 and (0).2 in 1059
  have eq1317 : (sP0 a b sk3) ∨ c = b ∨ c = sk1 := resolve eq1311 p3 -- subsumption resolution 1311,58
  have eq1318 : (sP0 a b sk3) ∨ c = sk1 := resolve eq1317 bc -- subsumption resolution 1317,57
  have eq1319 : c = sk3 ∨ c = sk1 := resolve eq1318 rule_def_0_2 -- resolution 1318,70
  have eq1338 : c ≠ sk2 ∨ c = sk1 := eq1319.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 86,1319, 1319 into 86, unify on (0).2 in 1319 and (0).2 in 86
  have eq1350 : c = sk1 := resolve eq1338 eq1275 -- subsumption resolution 1338,1275
  have eq1356 : c = b ∨ (old a sk1 sk2) ∨ b = sk2 := Eq.mp (by simp only [eq1350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq904 -- backward demodulation 904,1350
  have eq1361 : (old a c sk3) ∨ b = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq1350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq933 -- backward demodulation 933,1350
  have eq1362 : c = b ∨ (old a sk1 sk3) ∨ b = sk3 := Eq.mp (by simp only [eq1350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq934 -- backward demodulation 934,1350
  have eq1418 : (old a sk1 sk2) ∨ b = sk2 := resolve eq1356 bc -- subsumption resolution 1356,57
  have eq1419 : (old a c sk2) ∨ b = sk2 := Eq.mp (by simp only [eq1350, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1418 -- forward demodulation 1418,1350
  have eq1420 : b = sk2 := resolve eq1419 p4XZ -- subsumption resolution 1419,60
  have eq1421 : b ≠ sk3 := Eq.mp (by simp only [eq1420, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 86,1420
  have eq1423 : b = sk3 ∨ c = sk3 := resolve eq1361 p4XZ -- subsumption resolution 1361,60
  have eq1424 : c = sk3 := resolve eq1423 eq1421 -- subsumption resolution 1423,1421
  have eq1427 : (old a sk1 sk3) ∨ b = sk3 := resolve eq1362 bc -- subsumption resolution 1362,57
  have eq1428 : (old a sk1 c) ∨ b = sk3 := Eq.mp (by simp only [eq1424, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1427 -- forward demodulation 1427,1424
  have eq1429 : b = sk3 := resolve eq1428 p4XY -- subsumption resolution 1428,59
  have eq1430 : c = b := Eq.mp (by simp only [eq1424, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1429 -- forward demodulation 1429,1424
  subsumption bc eq1430 -- subsumption resolution 1430,57

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X0 X4 ∨ old X1 X4 X0)) (old_3 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ old X0 X3 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ b ≠ Z ∨ ¬ old b X X2 ∨ ¬ old X X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b X (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old X (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old a a (sF1 X Y Z) ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X0 X4 ∨ new X1 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq95 (X0 X1 X3 : G) : (new X0 X1 b) ∨ ¬(old X0 X3 a) ∨ ¬(old b X0 X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 74
  have eq96 (X0 X3 : G) : ¬(old b X0 X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c b) := resolve eq95 rfl -- equality resolution 95
  have eq100 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ (sF0 X0 X1 X2) = X3 ∨ ¬(old b X0 X3) := resolve rule_def_1_2 old_0 -- resolution 77,65
  have eq102 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4XZ -- resolution 77,63
  have eq113 (X0 : G) : ¬(new sk3 sk0 X0) ∨ sk4 = X0 := resolve prev_0 preserve_2 -- resolution 87,90
  have eq114 (X0 X1 X2 : G) : ¬(old X0 (sF0 X0 X1 X2) a) ∨ (new X0 c b) ∨ ¬(sP1 X0 X1 X2) := resolve eq96 rule_def_1_2 -- resolution 96,77
  have eq116 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c b) := resolve eq114 rule_def_1_3 -- subsumption resolution 114,78
  have eq134 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 86,88
  have eq135 : (sP2 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) := resolve new_imp preserve_1 -- resolution 86,89
  have eq136 : (sP2 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) := resolve new_imp preserve_2 -- resolution 86,90
  have eq175 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk2 := resolve eq134 rule_def_2_2 -- resolution 134,82
  have eq176 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq134 rule_def_2_1 -- resolution 134,81
  have eq177 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk0 := resolve eq134 rule_def_2_0 -- resolution 134,80
  have eq178 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq175 rule_def_1_1 -- subsumption resolution 175,76
  have eq179 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq176 rule_def_1_0 -- subsumption resolution 176,75
  have eq180 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq177 rule_def_0_0 -- subsumption resolution 177,71
  have eq181 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq178 rule_def_0_2 -- resolution 178,73
  have eq182 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq178 rule_def_0_1 -- resolution 178,72
  have eq187 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ b = sk3 := resolve eq135 rule_def_2_2 -- resolution 135,82
  have eq188 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ c = sk2 := resolve eq135 rule_def_2_1 -- resolution 135,81
  have eq189 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ a = sk1 := resolve eq135 rule_def_2_0 -- resolution 135,80
  have eq190 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk3 := resolve eq187 rule_def_1_1 -- subsumption resolution 187,76
  have eq191 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq188 rule_def_1_0 -- subsumption resolution 188,75
  have eq192 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq189 rule_def_0_0 -- subsumption resolution 189,71
  have eq200 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ b = sk4 := resolve eq136 rule_def_2_2 -- resolution 136,82
  have eq201 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ c = sk0 := resolve eq136 rule_def_2_1 -- resolution 136,81
  have eq202 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ a = sk3 := resolve eq136 rule_def_2_0 -- resolution 136,80
  have eq203 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ b = sk4 := resolve eq200 rule_def_1_1 -- subsumption resolution 200,76
  have eq204 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ c = sk0 := resolve eq201 rule_def_1_0 -- subsumption resolution 201,75
  have eq205 : (sP1 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ a = sk3 := resolve eq202 rule_def_0_0 -- subsumption resolution 202,71
  have eq215 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq179 rule_def_0_2 -- resolution 179,73
  have eq217 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq179 rule_def_0_0 -- resolution 179,71
  have eq243 : (old sk1 sk2 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq190 rule_def_0_2 -- resolution 190,73
  have eq244 : (old sk1 sk2 sk3) ∨ b = sk3 ∨ b = sk2 := resolve eq190 rule_def_0_1 -- resolution 190,72
  have eq252 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq191 rule_def_0_2 -- resolution 191,73
  have eq253 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ b = sk2 := resolve eq191 rule_def_0_1 -- resolution 191,72
  have eq254 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk1 := resolve eq191 rule_def_0_0 -- resolution 191,71
  have eq261 (X0 : G) : ¬(old b sk1 X0) ∨ a = sk1 ∨ (sF0 sk1 sk2 sk3) = X0 ∨ (old sk1 sk2 sk3) := resolve eq192 eq100 -- resolution 192,100
  have eq262 : (new sk1 c b) ∨ a = sk1 ∨ (old sk1 sk2 sk3) := resolve eq192 eq116 -- resolution 192,116
  have eq270 : (old sk3 sk0 sk4) ∨ b = sk4 ∨ b = sk0 := resolve eq203 rule_def_0_1 -- resolution 203,72
  have eq271 : (old sk3 sk0 sk4) ∨ b = sk4 ∨ a = sk3 := resolve eq203 rule_def_0_0 -- resolution 203,71
  have eq276 : (old sk3 sk0 sk4) ∨ c = sk0 ∨ c = sk4 := resolve eq204 rule_def_0_2 -- resolution 204,73
  have eq277 : (old sk3 sk0 sk4) ∨ c = sk0 ∨ b = sk0 := resolve eq204 rule_def_0_1 -- resolution 204,72
  have eq305 (X0 X1 : G) : ¬(old sk0 X0 X1) ∨ b = sk0 ∨ (old X0 sk4 sk0) ∨ ¬(old X0 X1 sk3) ∨ b = sk4 := resolve eq270 old_1 -- resolution 270,66
  have eq313 (X0 X1 : G) : ¬(old sk0 X0 X1) ∨ a = sk3 ∨ (old X0 sk4 sk0) ∨ ¬(old X0 X1 sk3) ∨ b = sk4 := resolve eq271 old_1 -- resolution 271,66
  have eq319 (X0 X1 : G) : ¬(old sk0 X0 X1) ∨ c = sk4 ∨ (old X0 sk4 sk0) ∨ ¬(old X0 X1 sk3) ∨ c = sk0 := resolve eq276 old_1 -- resolution 276,66
  have eq329 (X0 : G) : ¬(old sk3 sk3 X0) ∨ b = sk0 ∨ (old sk3 sk4 sk0) ∨ ¬(old sk3 X0 sk0) ∨ c = sk0 := resolve eq277 old_3 -- resolution 277,68
  have eq363 : a = sk1 ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 c b) ∨ (sP0 sk1 c b) ∨ (old sk1 c b) ∨ (sP2 sk1 c b) := resolve eq262 new_imp -- resolution 262,86
  have eq365 : a = sk1 ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 c b) ∨ (sP0 sk1 c b) ∨ (sP2 sk1 c b) := resolve eq363 p4XZ -- subsumption resolution 363,63
  have eq366 : a = sk1 ∨ (old sk1 sk2 sk3) ∨ (sP1 sk1 c b) ∨ (sP2 sk1 c b) := resolve eq365 rule_def_0_0 -- subsumption resolution 365,71
  have eq367 : (sP1 sk1 c b) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq366 rule_def_2_0 -- subsumption resolution 366,80
  have eq572 (X0 X1 : G) : ¬(sP1 sk1 X0 X1) ∨ (sF0 sk1 sk2 sk3) = (sF0 sk1 X0 X1) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq261 rule_def_1_2 -- resolution 261,77
  have eq873 : ¬(old sk1 sk2 sk3) ∨ (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq305 eq215 -- resolution 305,215
  have eq876 : b = sk0 ∨ (old sk1 sk4 sk0) ∨ ¬(old sk1 sk2 sk3) ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := resolve eq305 eq181 -- resolution 305,181
  have eq878 : (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 := resolve eq876 eq253 -- subsumption resolution 876,253
  have eq898 : ¬(old sk1 sk2 sk3) ∨ (old sk1 sk4 sk0) ∨ a = sk3 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq313 eq215 -- resolution 313,215
  have eq915 : b = sk0 ∨ b = sk4 ∨ b = sk2 ∨ c = sk2 ∨ (new sk1 sk4 sk0) := resolve eq878 imp_new_0 -- resolution 878,69
  have eq920 : b = sk4 ∨ b = sk0 ∨ b = sk2 ∨ c = sk2 := resolve eq915 preserve_3 -- subsumption resolution 915,91
  have eq923 : ¬(old sk1 sk2 sk3) ∨ (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq319 eq215 -- resolution 319,215
  have eq926 : c = sk4 ∨ (old sk1 sk4 sk0) ∨ ¬(old sk1 sk2 sk3) ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 := resolve eq319 eq181 -- resolution 319,181
  have eq928 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 := resolve eq926 eq253 -- subsumption resolution 926,253
  have eq1013 : (sF0 sk1 sk2 sk3) = (sF0 sk1 c b) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq572 eq367 -- resolution 572,367
  have eq1014 : (old sk1 sk2 sk3) ∨ (sF0 sk1 sk2 sk3) = (sF0 sk1 c b) ∨ a = sk1 := resolve eq1013 rfl -- duplicate literal removal 1013
  have eq1028 : c = sk4 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ (new sk1 sk4 sk0) := resolve eq928 imp_new_0 -- resolution 928,69
  have eq1039 : c = sk4 ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 := resolve eq1028 preserve_3 -- subsumption resolution 1028,91
  have eq1049 : c = b ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 ∨ b = sk2 ∨ c = sk2 := Or.assoc4 (eq920.imp_left (fun h : b = sk4 ↦ superpose h eq1039)) -- superposition 1039,920, 920 into 1039, unify on (0).2 in 920 and (0).2 in 1039
  have eq1077 : c = b ∨ c = sk0 ∨ b = sk2 ∨ c = sk2 ∨ b = sk0 := resolve eq1049 rfl -- duplicate literal removal 1049
  have eq1080 : b = sk2 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 := resolve eq1077 bc -- subsumption resolution 1077,60
  have eq1192 : (old sk1 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 := Or.assoc3 (eq1080.imp_left (fun h : b = sk2 ↦ superpose h eq252)) -- superposition 252,1080, 1080 into 252, unify on (0).2 in 1080 and (0).2 in 252
  have eq1211 : (old sk1 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 := resolve eq1192 bc -- subsumption resolution 1192,60
  have eq2422 : (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk3 := resolve eq873 eq252 -- resolution 873,252
  have eq2424 : (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ a = sk1 := resolve eq873 eq254 -- resolution 873,254
  have eq2430 : (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq2424 rfl -- duplicate literal removal 2424
  have eq2432 : (old sk1 sk4 sk0) ∨ b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq2422 rfl -- duplicate literal removal 2422
  have eq2594 : (old sk1 sk4 sk0) ∨ a = sk3 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk3 := resolve eq898 eq252 -- resolution 898,252
  have eq2601 : (old sk1 sk4 sk0) ∨ a = sk3 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq2594 rfl -- duplicate literal removal 2594
  have eq2737 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ c = sk3 := resolve eq923 eq252 -- resolution 923,252
  have eq2739 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ a = sk1 := resolve eq923 eq254 -- resolution 923,254
  have eq2745 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq2739 rfl -- duplicate literal removal 2739
  have eq2747 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq2737 rfl -- duplicate literal removal 2737
  have eq2774 : b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ (new sk1 sk4 sk0) := resolve eq2430 imp_new_0 -- resolution 2430,69
  have eq2786 : b = sk4 ∨ b = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq2774 preserve_3 -- subsumption resolution 2774,91
  have eq2919 : b = sk0 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk4 sk0) := resolve eq2432 imp_new_0 -- resolution 2432,69
  have eq2930 : b = sk4 ∨ b = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq2919 preserve_3 -- subsumption resolution 2919,91
  have eq3435 : a = sk3 ∨ b = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk4 sk0) := resolve eq2601 imp_new_0 -- resolution 2601,69
  have eq3446 : b = sk4 ∨ a = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq3435 preserve_3 -- subsumption resolution 3435,91
  have eq3707 : c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ (new sk1 sk4 sk0) := resolve eq2745 imp_new_0 -- resolution 2745,69
  have eq3742 : c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq3707 preserve_3 -- subsumption resolution 3707,91
  have eq3754 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ b = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := Or.assoc5 (eq2786.imp_left (fun h : b = sk4 ↦ superpose h eq3742)) -- superposition 3742,2786, 2786 into 3742, unify on (0).2 in 2786 and (0).2 in 3742
  have eq3839 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ b = sk0 := resolve eq3754 rfl -- duplicate literal removal 3754
  have eq3845 : c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3839 bc -- subsumption resolution 3839,60
  have eq3857 : (sP2 sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ (old sk1 c sk3) ∨ (sP1 sk1 c sk3) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := Or.assoc4 (eq3845.imp_left (fun h : c = sk2 ↦ superpose h eq135)) -- superposition 135,3845, 3845 into 135, unify on (0).2 in 3845 and (0).2 in 135
  have eq3861 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := Or.assoc3 (eq3845.imp_left (fun h : c = sk2 ↦ superpose h eq180)) -- superposition 180,3845, 3845 into 180, unify on (0).2 in 3845 and (0).3 in 180
  have eq3941 : (old sk1 c sk3) ∨ (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := Or.assoc3 (eq3845.imp_left (fun h : c = sk2 ↦ superpose h eq1014)) -- superposition 1014,3845, 3845 into 1014, unify on (0).2 in 3845 and (0).2 in 1014
  have eq3944 : (old sk1 c sk3) ∨ (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq3941 rfl -- duplicate literal removal 3941
  have eq3984 : (sP2 sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ (sP1 sk1 c sk3) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3857 p4XZ -- subsumption resolution 3857,63
  have eq3985 : (sP2 sk1 c sk3) ∨ (sP1 sk1 c sk3) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3984 rule_def_0_0 -- subsumption resolution 3984,71
  have eq3986 : (sP1 sk1 c sk3) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3985 rule_def_2_0 -- subsumption resolution 3985,80
  have eq3987 : (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3861 p4XY -- subsumption resolution 3861,62
  have eq3988 : c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq3987 rule_def_1_0 -- subsumption resolution 3987,75
  have eq3996 : (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq3944 p4XZ -- subsumption resolution 3944,63
  have eq4215 : (sP1 c sk2 sk3) ∨ (old c sk2 sk3) ∨ a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := Or.assoc3 (eq3988.imp_left (fun h : c = sk1 ↦ superpose h eq192)) -- superposition 192,3988, 3988 into 192, unify on (0).2 in 3988 and (0).1 in 192
  have eq4415 : (old c sk2 sk3) ∨ a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq4215 eq102 -- subsumption resolution 4215,102
  have eq4416 : a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk1 ∨ b = sk0 := resolve eq4415 p4YZ -- subsumption resolution 4415,64
  have eq4417 : a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq4416 ac -- subsumption resolution 4416,59
  have eq4575 : (old a b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := Or.assoc5 (eq4417.imp_left (fun h : a = sk1 ↦ superpose h eq1211)) -- superposition 1211,4417, 4417 into 1211, unify on (0).2 in 4417 and (0).1 in 1211
  have eq4614 : (old a b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := resolve eq4575 rfl -- duplicate literal removal 4575
  have eq4694 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := resolve eq4614 p3 -- subsumption resolution 4614,61
  have eq5520 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ (old c sk0 sk4) ∨ (sP1 c sk0 sk4) ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := Or.assoc4 (eq4694.imp_left (fun h : c = sk3 ↦ superpose h eq136)) -- superposition 136,4694, 4694 into 136, unify on (0).2 in 4694 and (0).1 in 136
  have eq5776 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ (sP1 c sk0 sk4) ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := resolve eq5520 p4YZ -- subsumption resolution 5520,64
  have eq5777 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := resolve eq5776 eq102 -- subsumption resolution 5776,102
  have eq5778 : (sP2 c sk0 sk4) ∨ c = sk0 ∨ c = sk2 ∨ b = sk0 ∨ a = sk0 := resolve eq5777 rule_def_0_1 -- subsumption resolution 5777,72
  have eq5779 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq5778 rule_def_2_1 -- subsumption resolution 5778,81
  have eq5809 : (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = b ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := Or.assoc3 (eq5779.imp_left (fun h : c = sk2 ↦ superpose h eq178)) -- superposition 178,5779, 5779 into 178, unify on (0).2 in 5779 and (0).3 in 178
  have eq5947 : (sP0 sk0 sk1 c) ∨ c = b ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq5809 p4XY -- subsumption resolution 5809,62
  have eq5948 : (sP0 sk0 sk1 c) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq5947 bc -- subsumption resolution 5947,60
  have eq5949 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5948 rule_def_0_0 -- subsumption resolution 5948,71
  have eq5961 : ¬(new sk1 sk4 b) ∨ c = sk0 ∨ a = sk0 := eq5949.imp_left (fun h : b = sk0 ↦ superpose h preserve_3) -- superposition 91,5949, 5949 into 91, unify on (0).2 in 5949 and (0).3 in 91
  have eq5985 : (old b sk1 sk2) ∨ c = sk1 ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq5949.imp_left (fun h : b = sk0 ↦ superpose h eq217)) -- superposition 217,5949, 5949 into 217, unify on (0).2 in 5949 and (0).1 in 217
  have eq5997 : (old sk3 b sk4) ∨ c = b ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq5949.imp_left (fun h : b = sk0 ↦ superpose h eq276)) -- superposition 276,5949, 5949 into 276, unify on (0).2 in 5949 and (0).2 in 276
  have eq6139 : a ≠ b ∨ c = sk0 ∨ a = sk0 := resolve eq5949 trans_resol -- equality factoring 5949
  have eq6141 : (old sk3 b sk4) ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 := resolve eq5997 bc -- subsumption resolution 5997,60
  have eq8441 : c = sk1 ∨ a = b ∨ c = sk0 ∨ a = sk0 ∨ ¬(old sk1 sk2 a) ∨ (new sk1 c b) := resolve eq5985 eq96 -- resolution 5985,96
  have eq8460 : ¬(old sk1 sk2 a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ (new sk1 c b) := resolve eq8441 eq6139 -- subsumption resolution 8441,6139
  have eq9194 : c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk4 sk0) := resolve eq2747 imp_new_0 -- resolution 2747,69
  have eq9232 : c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq9194 preserve_3 -- subsumption resolution 9194,91
  have eq9243 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := Or.assoc5 (eq2930.imp_left (fun h : b = sk4 ↦ superpose h eq9232)) -- superposition 9232,2930, 2930 into 9232, unify on (0).2 in 2930 and (0).2 in 9232
  have eq9247 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ a = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := Or.assoc5 (eq3446.imp_left (fun h : b = sk4 ↦ superpose h eq9232)) -- superposition 9232,3446, 3446 into 9232, unify on (0).2 in 3446 and (0).2 in 9232
  have eq9250 : (new sk3 sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := eq9232.imp_left (fun h : c = sk4 ↦ superpose h preserve_2) -- superposition 90,9232, 9232 into 90, unify on (0).2 in 9232 and (0).3 in 90
  have eq9377 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ a = sk3 := resolve eq9247 rfl -- duplicate literal removal 9247
  have eq9379 : c = b ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 := resolve eq9243 rfl -- duplicate literal removal 9243
  have eq9386 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq9379 bc -- subsumption resolution 9379,60
  have eq9387 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk3 := resolve eq9377 bc -- subsumption resolution 9377,60
  have eq9894 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ (old c sk0 sk4) ∨ (sP1 c sk0 sk4) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := Or.assoc4 (eq9386.imp_left (fun h : c = sk3 ↦ superpose h eq136)) -- superposition 136,9386, 9386 into 136, unify on (0).2 in 9386 and (0).1 in 136
  have eq10250 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ (sP1 c sk0 sk4) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq9894 p4YZ -- subsumption resolution 9894,64
  have eq10251 : (sP2 c sk0 sk4) ∨ (sP0 c sk0 sk4) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq10250 eq102 -- subsumption resolution 10250,102
  have eq10252 : (sP2 c sk0 sk4) ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq10251 rule_def_0_1 -- subsumption resolution 10251,72
  have eq10253 : c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq10252 rule_def_2_1 -- subsumption resolution 10252,81
  have eq10332 : (old sk0 sk1 c) ∨ c = b ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc3 (eq10253.imp_left (fun h : c = sk2 ↦ superpose h eq182)) -- superposition 182,10253, 10253 into 182, unify on (0).2 in 10253 and (0).3 in 182
  have eq10340 : (old sk1 c sk3) ∨ b = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc3 (eq10253.imp_left (fun h : c = sk2 ↦ superpose h eq244)) -- superposition 244,10253, 10253 into 244, unify on (0).2 in 10253 and (0).2 in 244
  have eq10544 : c = b ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq10332 p4XY -- subsumption resolution 10332,62
  have eq10545 : b = sk1 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq10544 bc -- subsumption resolution 10544,60
  have eq10549 : b = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq10340 p4XZ -- subsumption resolution 10340,63
  have eq10550 : b = sk3 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq10549 bc -- subsumption resolution 10549,60
  have eq10651 : ¬(new b sk4 sk0) ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := eq10545.imp_left (fun h : b = sk1 ↦ superpose h preserve_3) -- superposition 91,10545, 10545 into 91, unify on (0).2 in 10545 and (0).1 in 91
  have eq10889 : (sP1 b c sk3) ∨ c = b ∨ c = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc5 (eq10545.imp_left (fun h : b = sk1 ↦ superpose h eq3986)) -- superposition 3986,10545, 10545 into 3986, unify on (0).2 in 10545 and (0).1 in 3986
  have eq10959 : (sP1 b c sk3) ∨ c = b ∨ c = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk1 := resolve eq10889 rfl -- duplicate literal removal 10889
  have eq11016 : (sP1 b c sk3) ∨ c = sk0 ∨ a = b ∨ b = sk0 ∨ c = sk1 := resolve eq10959 bc -- subsumption resolution 10959,60
  have eq11123 (X0 : G) : ¬(old b b X0) ∨ b = sk0 ∨ (old b sk4 sk0) ∨ ¬(old b X0 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc5 (eq10550.imp_left (fun h : b = sk3 ↦ superpose h eq329)) -- superposition 329,10550, 10550 into 329, unify on (0).2 in 10550 and (0).1 in 329
  have eq11418 (X0 : G) : ¬(old b b X0) ∨ b = sk0 ∨ (old b sk4 sk0) ∨ ¬(old b X0 sk0) ∨ c = sk0 ∨ c = sk1 := resolve eq11123 rfl -- duplicate literal removal 11123
  have eq12286 : (sP1 c sk0 sk4) ∨ (old c sk0 sk4) ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk3 := Or.assoc3 (eq9387.imp_left (fun h : c = sk3 ↦ superpose h eq205)) -- superposition 205,9387, 9387 into 205, unify on (0).2 in 9387 and (0).1 in 205
  have eq12635 : (old c sk0 sk4) ∨ a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk3 := resolve eq12286 eq102 -- subsumption resolution 12286,102
  have eq12636 : a = c ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk3 := resolve eq12635 p4YZ -- subsumption resolution 12635,64
  have eq12637 : a = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq12636 ac -- subsumption resolution 12636,59
  have eq12674 (X0 : G) : ¬(new a sk0 X0) ∨ sk4 = X0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc2 (eq12637.imp_left (fun h : a = sk3 ↦ superpose h eq113)) -- superposition 113,12637, 12637 into 113, unify on (0).2 in 12637 and (0).1 in 113
  have eq12684 : (old sk1 sk2 a) ∨ a = b ∨ a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq12637.imp_left (fun h : a = sk3 ↦ superpose h eq243)) -- superposition 243,12637, 12637 into 243, unify on (0).2 in 12637 and (0).3 in 243
  have eq12687 : (old sk1 sk2 a) ∨ c = sk2 ∨ a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq12637.imp_left (fun h : a = sk3 ↦ superpose h eq252)) -- superposition 252,12637, 12637 into 252, unify on (0).2 in 12637 and (0).3 in 252
  have eq12871 : (old a b sk4) ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc4 (eq12637.imp_left (fun h : a = sk3 ↦ superpose h eq6141)) -- superposition 6141,12637, 12637 into 6141, unify on (0).2 in 12637 and (0).1 in 6141
  have eq12898 : (old a b sk4) ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq12871 rfl -- duplicate literal removal 12871
  have eq12971 : (old sk1 sk2 a) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ c = sk1 := resolve eq12687 rfl -- duplicate literal removal 12687
  have eq12983 : (old sk1 sk2 a) ∨ a = b ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq12684 ac -- subsumption resolution 12684,59
  have eq12984 : (old sk1 sk2 a) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq12971 ac -- subsumption resolution 12971,59
  have eq12995 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq12898 p3 -- subsumption resolution 12898,61
  have eq15027 : ¬(new sk1 c b) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq12995.imp_left (fun h : c = sk4 ↦ superpose h eq5961)) -- superposition 5961,12995, 12995 into 5961, unify on (0).2 in 12995 and (0).2 in 5961
  have eq15046 : ¬(new sk1 c b) ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq15027 rfl -- duplicate literal removal 15027
  have eq15168 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = c ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc5 (eq12637.imp_left (fun h : a = sk3 ↦ superpose h eq9250)) -- superposition 9250,12637, 12637 into 9250, unify on (0).2 in 12637 and (0).1 in 9250
  have eq15170 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = c := resolve eq15168 rfl -- duplicate literal removal 15168
  have eq15183 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq15170 ac -- subsumption resolution 15170,59
  have eq17041 : c = sk4 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq12674 eq15183 -- resolution 12674,15183
  have eq17047 : c = sk4 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq17041 rfl -- duplicate literal removal 17041
  have eq17126 : ¬(new sk1 c sk0) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := eq17047.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 91,17047, 17047 into 91, unify on (0).2 in 17047 and (0).2 in 91
  have eq21807 : c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ (new sk1 c b) ∨ a = b ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq8460 eq12983 -- resolution 8460,12983
  have eq21832 : c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ (new sk1 c b) ∨ a = b ∨ c = sk2 := resolve eq21807 rfl -- duplicate literal removal 21807
  have eq21833 : c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ a = b ∨ c = sk2 := resolve eq21832 eq15046 -- subsumption resolution 21832,15046
  have eq21834 : c = sk2 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq21833 eq6139 -- subsumption resolution 21833,6139
  have eq21863 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq21834.imp_left (fun h : c = sk2 ↦ superpose h eq134)) -- superposition 134,21834, 21834 into 134, unify on (0).2 in 21834 and (0).3 in 134
  have eq22119 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq21863 p4XY -- subsumption resolution 21863,62
  have eq22120 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq22119 rule_def_1_0 -- subsumption resolution 22119,75
  have eq22121 : (sP0 sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq22120 rule_def_2_1 -- subsumption resolution 22120,81
  have eq22122 : c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq22121 rule_def_0_0 -- subsumption resolution 22121,71
  have eq22148 : (sP1 c sk2 sk3) ∨ (old c sk2 sk3) ∨ a = c ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq22122.imp_left (fun h : c = sk1 ↦ superpose h eq192)) -- superposition 192,22122, 22122 into 192, unify on (0).2 in 22122 and (0).1 in 192
  have eq22512 : (old c sk2 sk3) ∨ a = c ∨ a = sk0 ∨ c = sk0 := resolve eq22148 eq102 -- subsumption resolution 22148,102
  have eq22513 : a = c ∨ a = sk0 ∨ c = sk0 := resolve eq22512 p4YZ -- subsumption resolution 22512,64
  have eq22514 : c = sk0 ∨ a = sk0 := resolve eq22513 ac -- subsumption resolution 22513,59
  have eq22533 : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ a = c ∨ a = sk0 := Or.assoc3 (eq22514.imp_left (fun h : c = sk0 ↦ superpose h eq180)) -- superposition 180,22514, 22514 into 180, unify on (0).2 in 22514 and (0).1 in 180
  have eq22801 : (old c sk1 sk2) ∨ a = c ∨ a = sk0 := resolve eq22533 eq102 -- subsumption resolution 22533,102
  have eq22802 : a = c ∨ a = sk0 := resolve eq22801 p4YZ -- subsumption resolution 22801,64
  have eq22803 : a = sk0 := resolve eq22802 ac -- subsumption resolution 22802,59
  have eq22806 : ¬(new sk1 sk4 a) := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 91,22803
  have eq22809 : (sP1 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq134 -- backward demodulation 134,22803
  have eq22832 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq215 -- backward demodulation 215,22803
  have eq22850 : (old sk3 a sk4) ∨ c = sk0 ∨ c = sk4 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq276 -- backward demodulation 276,22803
  have eq23549 : a = c ∨ (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 ∨ b = sk0 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3996 -- backward demodulation 3996,22803
  have eq24010 : a = c ∨ b = sk1 ∨ c = sk1 ∨ b = sk0 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10545 -- backward demodulation 10545,22803
  have eq24046 : a = c ∨ ¬(new b sk4 sk0) ∨ c = sk1 ∨ b = sk0 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10651 -- backward demodulation 10651,22803
  have eq24118 : a = c ∨ (sP1 b c sk3) ∨ a = b ∨ b = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq11016 -- backward demodulation 11016,22803
  have eq24163 : ∀ (X0 : G) , a = c ∨ ¬(old b b X0) ∨ b = sk0 ∨ (old b sk4 sk0) ∨ ¬(old b X0 sk0) ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq11418 -- backward demodulation 11418,22803
  have eq24213 : a = c ∨ (old sk1 sk2 a) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12984 -- backward demodulation 12984,22803
  have eq24383 : a = c ∨ ¬(new sk1 c sk0) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq17126 -- backward demodulation 17126,22803
  have eq24434 : (sP2 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq22809 -- forward demodulation 22809,22803
  have eq24435 : (sP0 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq24434 -- forward demodulation 24434,22803
  have eq24436 : (sP2 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP1 a sk1 sk2) := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq24435 -- forward demodulation 24435,22803
  have eq24477 : a = c ∨ (old sk3 a sk4) ∨ c = sk4 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq22850 -- forward demodulation 22850,22803
  have eq24478 : (old sk3 a sk4) ∨ c = sk4 := resolve eq24477 ac -- subsumption resolution 24477,59
  have eq25631 : (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 ∨ b = sk0 := resolve eq23549 ac -- subsumption resolution 23549,59
  have eq25632 : (sF0 sk1 c b) = (sF0 sk1 c sk3) ∨ a = b ∨ a = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq25631 -- forward demodulation 25631,22803
  have eq26456 : b = sk1 ∨ c = sk1 ∨ b = sk0 := resolve eq24010 ac -- subsumption resolution 24010,59
  have eq26457 : b = sk1 ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26456 -- forward demodulation 26456,22803
  have eq26529 : ¬(new b sk4 sk0) ∨ c = sk1 ∨ b = sk0 := resolve eq24046 ac -- subsumption resolution 24046,59
  have eq26530 : ¬(new b sk4 a) ∨ c = sk1 ∨ b = sk0 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26529 -- forward demodulation 26529,22803
  have eq26531 : ¬(new b sk4 a) ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26530 -- forward demodulation 26530,22803
  have eq26710 : (sP1 b c sk3) ∨ a = b ∨ b = sk0 ∨ c = sk1 := resolve eq24118 ac -- subsumption resolution 24118,59
  have eq26711 : a = b ∨ (sP1 b c sk3) ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26710 -- forward demodulation 26710,22803
  have eq26712 : (sP1 b c sk3) ∨ a = b ∨ c = sk1 := resolve eq26711 rfl -- duplicate literal removal 26711
  have eq26822 (X0 : G) : ¬(old b b X0) ∨ b = sk0 ∨ (old b sk4 sk0) ∨ ¬(old b X0 sk0) ∨ c = sk1 := resolve eq24163 ac -- subsumption resolution 24163,59
  have eq26823 : ∀ (X0 : G) , a = b ∨ ¬(old b b X0) ∨ (old b sk4 sk0) ∨ ¬(old b X0 sk0) ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26822 -- forward demodulation 26822,22803
  have eq26824 : ∀ (X0 : G) , (old b sk4 a) ∨ a = b ∨ ¬(old b b X0) ∨ ¬(old b X0 sk0) ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26823 -- forward demodulation 26823,22803
  have eq26825 : ∀ (X0 : G) , ¬(old b b X0) ∨ (old b sk4 a) ∨ a = b ∨ ¬(old b X0 a) ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26824 -- forward demodulation 26824,22803
  have eq26931 : (old sk1 sk2 a) ∨ c = sk2 ∨ c = sk1 := resolve eq24213 ac -- subsumption resolution 24213,59
  have eq27228 : ¬(new sk1 c sk0) ∨ c = sk2 ∨ c = sk1 := resolve eq24383 ac -- subsumption resolution 24383,59
  have eq27229 : ¬(new sk1 c a) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq22803, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq27228 -- forward demodulation 27228,22803
  have eq46198 : (sF0 b c b) = (sF0 b c sk3) ∨ a = b ∨ a = b ∨ c = b ∨ a = b ∨ c = sk1 := Or.assoc4 (eq26457.imp_left (fun h : b = sk1 ↦ superpose h eq25632)) -- superposition 25632,26457, 26457 into 25632, unify on (0).2 in 26457 and (0).1.1 in 25632
  have eq46275 : (sF0 b c b) = (sF0 b c sk3) ∨ a = b ∨ c = b ∨ c = sk1 := resolve eq46198 rfl -- duplicate literal removal 46198
  have eq46278 : (sF0 b c b) = (sF0 b c sk3) ∨ a = b ∨ c = sk1 := resolve eq46275 bc -- subsumption resolution 46275,60
  have eq46346 : (old b b (sF0 b c b)) ∨ ¬(sP1 b c sk3) ∨ a = b ∨ c = sk1 := Or.assoc2 (eq46278.imp_left (fun h : (sF0 b c b) = (sF0 b c sk3) ↦ superpose h rule_def_1_2)) -- superposition 77,46278, 46278 into 77, unify on (0).2 in 46278 and (0).3 in 77
  have eq46347 : (old b (sF0 b c b) a) ∨ ¬(sP1 b c sk3) ∨ a = b ∨ c = sk1 := Or.assoc2 (eq46278.imp_left (fun h : (sF0 b c b) = (sF0 b c sk3) ↦ superpose h rule_def_1_3)) -- superposition 78,46278, 46278 into 78, unify on (0).2 in 46278 and (0).2 in 78
  have eq46375 : (old b b (sF0 b c b)) ∨ a = b ∨ c = sk1 := resolve eq46346 eq26712 -- subsumption resolution 46346,26712
  have eq46376 : (old b (sF0 b c b) a) ∨ a = b ∨ c = sk1 := resolve eq46347 eq26712 -- subsumption resolution 46347,26712
  have eq47963 : (old b sk4 a) ∨ a = b ∨ ¬(old b (sF0 b c b) a) ∨ c = sk1 ∨ a = b ∨ c = sk1 := resolve eq26825 eq46375 -- resolution 26825,46375
  have eq47965 : (old b sk4 a) ∨ a = b ∨ ¬(old b (sF0 b c b) a) ∨ c = sk1 := resolve eq47963 rfl -- duplicate literal removal 47963
  have eq47966 : (old b sk4 a) ∨ a = b ∨ c = sk1 := resolve eq47965 eq46376 -- subsumption resolution 47965,46376
  have eq47975 : a = b ∨ c = sk1 ∨ (new b sk4 a) := resolve eq47966 imp_new_0 -- resolution 47966,69
  have eq48020 : c = sk1 ∨ a = b := resolve eq47975 eq26531 -- subsumption resolution 47975,26531
  have eq48033 : (sP1 c sk2 sk3) ∨ (old c sk2 sk3) ∨ a = c ∨ a = b := Or.assoc3 (eq48020.imp_left (fun h : c = sk1 ↦ superpose h eq192)) -- superposition 192,48020, 48020 into 192, unify on (0).2 in 48020 and (0).1 in 192
  have eq48349 : (old c sk2 sk3) ∨ a = c ∨ a = b := resolve eq48033 eq102 -- subsumption resolution 48033,102
  have eq48350 : a = c ∨ a = b := resolve eq48349 p4YZ -- subsumption resolution 48349,64
  have eq48351 : a = b := resolve eq48350 ac -- subsumption resolution 48350,59
  have eq48353 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 61,48351
  have eq48354 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 72,48351
  have eq48356 : ∀ (X0 X1 X2 : G) , (old a X0 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_2 -- backward demodulation 77,48351
  have eq48360 : ∀ (X0 X3 : G) , ¬(old a X0 X3) ∨ ¬(old X0 X3 a) ∨ (new X0 c b) := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq96 -- backward demodulation 96,48351
  have eq48385 : a = sk2 ∨ (old sk1 sk2 sk3) ∨ b = sk3 := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq244 -- backward demodulation 244,48351
  have eq49965 : ∀ (X0 X3 : G) , ¬(old a X0 X3) ∨ (new X0 c a) ∨ ¬(old X0 X3 a) := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq48360 -- forward demodulation 48360,48351
  have eq49977 : a = sk3 ∨ a = sk2 ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq48351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq48385 -- forward demodulation 48385,48351
  have eq51325 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq48353 rule_def_2_3 -- resolution 48353,83
  have eq51367 (X0 X1 : G) : ¬(sP1 a X0 X1) := resolve eq48356 eq48353 -- resolution 48356,48353
  have eq51405 : (new sk1 c a) ∨ ¬(old sk1 sk2 a) ∨ c = sk1 ∨ c = sk2 := resolve eq49965 eq22832 -- resolution 49965,22832
  have eq51407 : ¬(old sk1 sk2 a) ∨ c = sk1 ∨ c = sk2 := resolve eq51405 eq27229 -- subsumption resolution 51405,27229
  have eq51408 : c = sk2 ∨ c = sk1 := resolve eq51407 eq26931 -- subsumption resolution 51407,26931
  have eq51422 : (sP2 a sk1 c) ∨ (sP0 a sk1 c) ∨ (old a sk1 c) ∨ (sP1 a sk1 c) ∨ c = sk1 := Or.assoc4 (eq51408.imp_left (fun h : c = sk2 ↦ superpose h eq24436)) -- superposition 24436,51408, 51408 into 24436, unify on (0).2 in 51408 and (0).3 in 24436
  have eq51437 : (sP0 a sk1 c) ∨ (old a sk1 c) ∨ (sP1 a sk1 c) ∨ c = sk1 := resolve eq51422 eq51325 -- subsumption resolution 51422,51325
  have eq51438 : (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ c = sk1 := resolve eq51437 p4XY -- subsumption resolution 51437,62
  have eq51439 : (sP0 a sk1 c) ∨ c = sk1 := resolve eq51438 eq51367 -- subsumption resolution 51438,51367
  have eq51468 : c = sk1 ∨ a = sk1 := resolve eq51439 eq48354 -- resolution 51439,48354
  have eq51477 : (sP1 c sk2 sk3) ∨ (old c sk2 sk3) ∨ a = c ∨ a = sk1 := Or.assoc3 (eq51468.imp_left (fun h : c = sk1 ↦ superpose h eq192)) -- superposition 192,51468, 51468 into 192, unify on (0).2 in 51468 and (0).1 in 192
  have eq51513 : (old c sk2 sk3) ∨ a = c ∨ a = sk1 := resolve eq51477 eq102 -- subsumption resolution 51477,102
  have eq51514 : a = c ∨ a = sk1 := resolve eq51513 p4YZ -- subsumption resolution 51513,64
  have eq51515 : a = sk1 := resolve eq51514 ac -- subsumption resolution 51514,59
  have eq51516 : (new a sk2 sk3) := Eq.mp (by simp only [eq51515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 89,51515
  have eq51544 : ¬(new a sk4 a) := Eq.mp (by simp only [eq51515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq22806 -- backward demodulation 22806,51515
  have eq51546 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq51515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq22832 -- backward demodulation 22832,51515
  have eq51744 : (old a sk2 sk3) ∨ a = sk3 ∨ a = sk2 := Eq.mp (by simp only [eq51515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq49977 -- backward demodulation 49977,51515
  have eq51967 : (old a sk1 sk2) ∨ c = sk2 := resolve eq51546 ac -- subsumption resolution 51546,59
  have eq51968 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq51515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq51967 -- forward demodulation 51967,51515
  have eq51969 : c = sk2 := resolve eq51968 eq48353 -- subsumption resolution 51968,48353
  have eq51970 : (new a c sk3) := Eq.mp (by simp only [eq51969, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq51516 -- backward demodulation 51516,51969
  have eq52027 : (old a c sk3) ∨ a = sk3 ∨ a = sk2 := Eq.mp (by simp only [eq51969, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq51744 -- forward demodulation 51744,51969
  have eq52028 : a = sk3 ∨ a = sk2 := resolve eq52027 p4XZ -- subsumption resolution 52027,63
  have eq52029 : a = c ∨ a = sk3 := Eq.mp (by simp only [eq51969, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq52028 -- forward demodulation 52028,51969
  have eq52030 : a = sk3 := resolve eq52029 ac -- subsumption resolution 52029,59
  have eq52037 : (old a a sk4) ∨ c = sk4 := Eq.mp (by simp only [eq52030, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq24478 -- backward demodulation 24478,52030
  have eq52045 : (new a c a) := Eq.mp (by simp only [eq52030, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq51970 -- backward demodulation 51970,52030
  have eq52053 : c = sk4 := resolve eq52037 eq48353 -- subsumption resolution 52037,48353
  have eq52054 : ¬(new a c a) := Eq.mp (by simp only [eq52053, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq51544 -- backward demodulation 51544,52053
  subsumption eq52054 eq52045 -- subsumption resolution 52045,52054

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X0 ∨ X1 = X2)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b X (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X0 ∨ X1 = X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq95 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 72
  have eq96 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq95 rfl -- equality resolution 95
  have eq97 : (new a b c) := resolve eq96 rfl -- equality resolution 96
  have eq105 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4XZ -- resolution 79,65
  have eq113 (X0 : G) : ¬(new sk0 sk0 X0) ∨ sk1 = X0 := resolve prev_0 preserve_0 -- resolution 89,91
  have eq140 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 88,91
  have eq141 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 88,92
  have eq142 : (sP2 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) := resolve new_imp preserve_2 -- resolution 88,93
  have eq196 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ c = sk0 := resolve eq140 rule_def_2_1 -- resolution 140,83
  have eq197 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ a = sk0 := resolve eq140 rule_def_2_0 -- resolution 140,82
  have eq199 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq196 rule_def_1_0 -- subsumption resolution 196,77
  have eq200 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 := resolve eq197 rule_def_0_0 -- subsumption resolution 197,73
  have eq207 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk2 := resolve eq141 rule_def_2_2 -- resolution 141,84
  have eq208 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq141 rule_def_2_1 -- resolution 141,83
  have eq209 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk0 := resolve eq141 rule_def_2_0 -- resolution 141,82
  have eq210 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq207 rule_def_1_1 -- subsumption resolution 207,78
  have eq211 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq208 rule_def_1_0 -- subsumption resolution 208,77
  have eq212 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq209 rule_def_0_0 -- subsumption resolution 209,73
  have eq220 : (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) ∨ b = sk0 := resolve eq142 rule_def_2_2 -- resolution 142,84
  have eq221 : (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) ∨ c = sk2 := resolve eq142 rule_def_2_1 -- resolution 142,83
  have eq223 : (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ b = sk0 := resolve eq220 rule_def_1_1 -- subsumption resolution 220,78
  have eq224 : (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ c = sk2 := resolve eq221 rule_def_1_0 -- subsumption resolution 221,77
  have eq235 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq199 rule_def_0_2 -- resolution 199,75
  have eq236 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ b = sk0 := resolve eq199 rule_def_0_1 -- resolution 199,74
  have eq264 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq210 rule_def_0_2 -- resolution 210,75
  have eq273 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq211 rule_def_0_2 -- resolution 211,75
  have eq291 : (old sk0 sk2 sk0) ∨ b = sk0 ∨ c = sk0 := resolve eq223 rule_def_0_2 -- resolution 223,75
  have eq298 : (old sk0 sk2 sk0) ∨ c = sk2 ∨ c = sk0 := resolve eq224 rule_def_0_2 -- resolution 224,75
  have eq319 (X0 : G) : ¬(old sk0 sk0 X0) ∨ c = sk0 ∨ sk2 = X0 ∨ ¬(old sk0 X0 sk2) ∨ b = sk0 := resolve eq291 old_2 -- resolution 291,69
  have eq347 (X0 : G) : ¬(old sk0 sk0 X0) ∨ c = sk0 ∨ sk2 = X0 ∨ ¬(old sk0 X0 sk2) ∨ c = sk2 := resolve eq298 old_2 -- resolution 298,69
  have eq796 : c = sk0 ∨ sk1 = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq319 eq236 -- resolution 319,236
  have eq803 : c = sk0 ∨ sk1 = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ b = sk0 := resolve eq796 rfl -- duplicate literal removal 796
  have eq806 : ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ b = sk0 := resolve eq803 preserve_3 -- subsumption resolution 803,94
  have eq810 : c = sk2 ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq806 eq273 -- resolution 806,273
  have eq1049 : (sP2 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq810.imp_left (fun h : c = sk2 ↦ superpose h eq142)) -- superposition 142,810, 810 into 142, unify on (0).2 in 810 and (0).2 in 142
  have eq1091 : (sP2 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq1049 p4XZ -- subsumption resolution 1049,65
  have eq1092 : (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq1091 rule_def_0_2 -- subsumption resolution 1091,75
  have eq1093 : (sP2 sk0 c sk0) ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq1092 rule_def_1_1 -- subsumption resolution 1092,78
  have eq1094 : c = sk1 ∨ b = sk0 ∨ c = sk0 := resolve eq1093 rule_def_2_2 -- subsumption resolution 1093,84
  have eq1102 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := Or.assoc4 (eq1094.imp_left (fun h : c = sk1 ↦ superpose h eq140)) -- superposition 140,1094, 1094 into 140, unify on (0).2 in 1094 and (0).3 in 140
  have eq1136 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq1102 p4XY -- subsumption resolution 1102,64
  have eq1137 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq1136 rule_def_1_0 -- subsumption resolution 1136,77
  have eq1138 : (sP0 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq1137 rule_def_2_1 -- subsumption resolution 1137,83
  have eq1139 : b = sk0 ∨ c = sk0 := resolve eq1138 rule_def_0_1 -- subsumption resolution 1138,74
  have eq2347 : c = sk0 ∨ sk1 = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq347 eq235 -- resolution 347,235
  have eq2355 : c = sk0 ∨ sk1 = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq2347 rfl -- duplicate literal removal 2347
  have eq2359 : c = sk0 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq2355 preserve_3 -- subsumption resolution 2355,94
  have eq2360 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq2359 eq273 -- subsumption resolution 2359,273
  have eq2378 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq2360.imp_left (fun h : c = sk2 ↦ superpose h eq212)) -- superposition 212,2360, 2360 into 212, unify on (0).2 in 2360 and (0).3 in 212
  have eq2450 : (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq2378 p4XY -- subsumption resolution 2378,64
  have eq2451 : c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2450 rule_def_1_0 -- subsumption resolution 2450,77
  have eq2481 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq2451.imp_left (fun h : c = sk1 ↦ superpose h eq140)) -- superposition 140,2451, 2451 into 140, unify on (0).2 in 2451 and (0).3 in 140
  have eq2552 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2481 p4XY -- subsumption resolution 2481,64
  have eq2553 : (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2552 rule_def_0_0 -- subsumption resolution 2552,73
  have eq2554 : (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2553 rule_def_2_0 -- subsumption resolution 2553,82
  have eq2555 : c = sk0 ∨ a = sk0 := resolve eq2554 rule_def_1_0 -- subsumption resolution 2554,77
  have eq2587 : (sP1 c c sk1) ∨ (old c c sk1) ∨ a = c ∨ a = sk0 := Or.assoc3 (eq2555.imp_left (fun h : c = sk0 ↦ superpose h eq200)) -- superposition 200,2555, 2555 into 200, unify on (0).2 in 2555 and (0).1 in 200
  have eq2688 : (old c c sk1) ∨ a = c ∨ a = sk0 := resolve eq2587 eq105 -- subsumption resolution 2587,105
  have eq2689 : a = c ∨ a = sk0 := resolve eq2688 p4YZ -- subsumption resolution 2688,66
  have eq2690 : a = sk0 := resolve eq2689 ac -- subsumption resolution 2689,61
  have eq2694 : ∀ (X0 : G) , ¬(new a a X0) ∨ sk1 = X0 := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq113 -- backward demodulation 113,2690
  have eq2755 : (old a sk1 sk2) ∨ b = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq264 -- backward demodulation 264,2690
  have eq2778 : (old a sk2 a) ∨ c = sk2 ∨ c = sk0 := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq298 -- backward demodulation 298,2690
  have eq3033 : a = c ∨ b = sk0 := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1139 -- backward demodulation 1139,2690
  have eq3408 : a = c ∨ (old a sk2 a) ∨ c = sk2 := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2778 -- forward demodulation 2778,2690
  have eq3409 : (old a sk2 a) ∨ c = sk2 := resolve eq3408 ac -- subsumption resolution 3408,61
  have eq3675 : b = sk0 := resolve eq3033 ac -- subsumption resolution 3033,61
  have eq3676 : a = b := Eq.mp (by simp only [eq2690, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3675 -- forward demodulation 3675,2690
  have eq3678 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq3676, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 63,3676
  have eq3684 : (new a a c) := Eq.mp (by simp only [eq3676, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq97 -- backward demodulation 97,3676
  have eq3735 : a = sk2 ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq3676, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2755 -- backward demodulation 2755,3676
  have eq4503 : c = sk1 := resolve eq2694 eq3684 -- resolution 2694,3684
  have eq4504 : c ≠ sk2 := Eq.mp (by simp only [eq4503, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 94,4503
  have eq4529 : (old a c sk2) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq4503, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3735 -- backward demodulation 3735,4503
  have eq4589 : a = sk2 ∨ c = sk2 := resolve eq4529 p4XZ -- subsumption resolution 4529,65
  have eq4590 : a = sk2 := resolve eq4589 eq4504 -- subsumption resolution 4589,4504
  have eq4600 : a = c ∨ (old a sk2 a) := Eq.mp (by simp only [eq4590, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3409 -- backward demodulation 3409,4590
  have eq4650 : (old a sk2 a) := resolve eq4600 ac -- subsumption resolution 4600,61
  have eq4651 : (old a a a) := Eq.mp (by simp only [eq4590, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4650 -- forward demodulation 4650,4590
  subsumption eq3678 eq4651 -- subsumption resolution 4651,3678

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X0 X2 X3 ∨ old X0 X3 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b X (sF0 X Y Z) ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z X1, a ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ ¬ old a a X1 ∨ ¬ old a X1 b ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X0 X2 X3 ∨ new X0 X3 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq103 (X0 X1 X3 : G) : (new X0 X1 b) ∨ ¬(old a X3 b) ∨ ¬(old a a X3) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_3 rfl -- equality resolution 83
  have eq104 (X0 X3 : G) : (new X0 c b) ∨ ¬(old a X3 b) ∨ ¬(old a a X3) ∨ a ≠ X0 := resolve eq103 rfl -- equality resolution 103
  have eq105 (X3 : G) : ¬(old a a X3) ∨ ¬(old a X3 b) ∨ (new a c b) := resolve eq104 rfl -- equality resolution 104
  have eq108 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4XZ -- resolution 81,67
  have eq145 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 90,94
  have eq146 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 90,95
  have eq147 : (sP2 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) := resolve new_imp preserve_2 -- resolution 90,96
  have eq199 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ c = sk0 := resolve eq145 rule_def_2_1 -- resolution 145,85
  have eq200 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ a = sk0 := resolve eq145 rule_def_2_0 -- resolution 145,84
  have eq202 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq199 rule_def_1_0 -- subsumption resolution 199,79
  have eq203 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 := resolve eq200 rule_def_0_0 -- subsumption resolution 200,75
  have eq210 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk2 := resolve eq146 rule_def_2_2 -- resolution 146,86
  have eq211 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq146 rule_def_2_1 -- resolution 146,85
  have eq213 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq210 rule_def_1_1 -- subsumption resolution 210,80
  have eq214 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq211 rule_def_1_0 -- subsumption resolution 211,79
  have eq223 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ b = sk3 := resolve eq147 rule_def_2_2 -- resolution 147,86
  have eq224 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ c = sk2 := resolve eq147 rule_def_2_1 -- resolution 147,85
  have eq225 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ a = sk0 := resolve eq147 rule_def_2_0 -- resolution 147,84
  have eq226 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ b = sk3 := resolve eq223 rule_def_1_1 -- subsumption resolution 223,80
  have eq227 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk2 := resolve eq224 rule_def_1_0 -- subsumption resolution 224,79
  have eq228 : (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ a = sk0 := resolve eq225 rule_def_0_0 -- subsumption resolution 225,75
  have eq238 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq202 rule_def_0_2 -- resolution 202,77
  have eq267 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq213 rule_def_0_1 -- resolution 213,76
  have eq275 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq214 rule_def_0_2 -- resolution 214,77
  have eq293 : (old sk0 sk2 sk3) ∨ b = sk3 ∨ b = sk2 := resolve eq226 rule_def_0_1 -- resolution 226,76
  have eq299 : (old sk0 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq227 rule_def_0_2 -- resolution 227,77
  have eq341 (X0 : G) : ¬(old sk0 sk0 X0) ∨ c = sk3 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 X0 sk2) ∨ c = sk2 := resolve eq299 old_3 -- resolution 299,72
  have eq1524 : c = sk3 ∨ (old sk0 sk3 sk2) ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq341 eq238 -- resolution 341,238
  have eq1528 : (old sk0 sk3 sk2) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1524 eq275 -- subsumption resolution 1524,275
  have eq1858 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ (new sk0 sk3 sk2) := resolve eq1528 imp_new_0 -- resolution 1528,73
  have eq1871 : c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1858 preserve_3 -- subsumption resolution 1858,97
  have eq1892 : ¬(new sk0 c sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := eq1871.imp_left (fun h : c = sk3 ↦ superpose h preserve_3) -- superposition 97,1871, 1871 into 97, unify on (0).2 in 1871 and (0).2 in 97
  have eq1898 : (sP1 sk0 sk2 c) ∨ (old sk0 sk2 c) ∨ a = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq1871.imp_left (fun h : c = sk3 ↦ superpose h eq228)) -- superposition 228,1871, 1871 into 228, unify on (0).2 in 1871 and (0).3 in 228
  have eq1899 : (old sk0 sk2 c) ∨ c = b ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq1871.imp_left (fun h : c = sk3 ↦ superpose h eq293)) -- superposition 293,1871, 1871 into 293, unify on (0).2 in 1871 and (0).3 in 293
  have eq1940 : (sP1 sk0 sk2 c) ∨ a = sk0 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1898 p4XY -- subsumption resolution 1898,66
  have eq1941 : c = sk2 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq1940 rule_def_1_0 -- subsumption resolution 1940,79
  have eq1942 : c = b ∨ b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1899 p4XY -- subsumption resolution 1899,66
  have eq1943 : b = sk2 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1942 bc -- subsumption resolution 1942,64
  have eq1949 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := Or.assoc4 (eq1941.imp_left (fun h : c = sk2 ↦ superpose h eq146)) -- superposition 146,1941, 1941 into 146, unify on (0).2 in 1941 and (0).3 in 146
  have eq2049 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq1949 p4XY -- subsumption resolution 1949,66
  have eq2050 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq2049 rule_def_1_0 -- subsumption resolution 2049,79
  have eq2051 : (sP0 sk0 sk1 c) ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq2050 rule_def_2_1 -- subsumption resolution 2050,85
  have eq2052 : c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2051 rule_def_0_0 -- subsumption resolution 2051,75
  have eq2064 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq2052.imp_left (fun h : c = sk1 ↦ superpose h eq145)) -- superposition 145,2052, 2052 into 145, unify on (0).2 in 2052 and (0).3 in 145
  have eq2137 : (sP2 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2064 p4XY -- subsumption resolution 2064,66
  have eq2138 : (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2137 rule_def_0_0 -- subsumption resolution 2137,75
  have eq2139 : (sP1 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq2138 rule_def_2_0 -- subsumption resolution 2138,84
  have eq2140 : c = sk0 ∨ a = sk0 := resolve eq2139 rule_def_1_0 -- subsumption resolution 2139,79
  have eq2166 : (sP1 c c sk1) ∨ (old c c sk1) ∨ a = c ∨ a = sk0 := Or.assoc3 (eq2140.imp_left (fun h : c = sk0 ↦ superpose h eq203)) -- superposition 203,2140, 2140 into 203, unify on (0).2 in 2140 and (0).1 in 203
  have eq2330 : (old c c sk1) ∨ a = c ∨ a = sk0 := resolve eq2166 eq108 -- subsumption resolution 2166,108
  have eq2331 : a = c ∨ a = sk0 := resolve eq2330 p4YZ -- subsumption resolution 2330,68
  have eq2332 : a = sk0 := resolve eq2331 ac -- subsumption resolution 2331,63
  have eq2334 : (new a sk1 sk2) := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 95,2332
  have eq2336 : ¬(new a sk3 sk2) := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 97,2332
  have eq2378 : (old a a sk1) ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq238 -- backward demodulation 238,2332
  have eq2398 : (old a sk1 sk2) ∨ b = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq267 -- backward demodulation 267,2332
  have eq2403 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq275 -- backward demodulation 275,2332
  have eq2414 : (old a sk2 sk3) ∨ b = sk3 ∨ b = sk2 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq293 -- backward demodulation 293,2332
  have eq2419 : (old a sk2 sk3) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq299 -- backward demodulation 299,2332
  have eq2899 : a = c ∨ ¬(new sk0 c sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1892 -- backward demodulation 1892,2332
  have eq2905 : a = c ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1943 -- backward demodulation 1943,2332
  have eq2983 : a = c ∨ (old a a sk1) ∨ c = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2378 -- forward demodulation 2378,2332
  have eq2984 : (old a a sk1) ∨ c = sk1 := resolve eq2983 ac -- subsumption resolution 2983,63
  have eq3582 : ¬(new sk0 c sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq2899 ac -- subsumption resolution 2899,63
  have eq3583 : ¬(new a c sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3582 -- forward demodulation 3582,2332
  have eq3589 : b = sk2 ∨ c = sk2 ∨ c = sk1 := resolve eq2905 ac -- subsumption resolution 2905,63
  have eq3608 : ¬(old a sk1 b) ∨ c = sk1 ∨ (new a c b) := resolve eq2984 eq105 -- resolution 2984,105
  have eq3731 : (old a sk1 b) ∨ c = sk1 ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq3589.imp_left (fun h : b = sk2 ↦ superpose h eq2403)) -- superposition 2403,3589, 3589 into 2403, unify on (0).2 in 3589 and (0).3 in 2403
  have eq3732 : (old a sk1 b) ∨ c = sk1 ∨ c = b ∨ c = sk2 := resolve eq3731 rfl -- duplicate literal removal 3731
  have eq3733 : (old a sk1 b) ∨ c = sk1 ∨ c = sk2 := resolve eq3732 bc -- subsumption resolution 3732,64
  have eq3817 : ¬(new a c b) ∨ c = b ∨ c = sk1 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq3589.imp_left (fun h : b = sk2 ↦ superpose h eq3583)) -- superposition 3583,3589, 3589 into 3583, unify on (0).2 in 3589 and (0).3 in 3583
  have eq3818 : ¬(new a c b) ∨ c = b ∨ c = sk1 ∨ c = sk2 := resolve eq3817 rfl -- duplicate literal removal 3817
  have eq3819 : ¬(new a c b) ∨ c = sk1 ∨ c = sk2 := resolve eq3818 bc -- subsumption resolution 3818,64
  have eq3962 : c = sk1 ∨ (new a c b) ∨ c = sk1 ∨ c = sk2 := resolve eq3608 eq3733 -- resolution 3608,3733
  have eq3963 : c = sk1 ∨ (new a c b) ∨ c = sk2 := resolve eq3962 rfl -- duplicate literal removal 3962
  have eq3964 : c = sk2 ∨ c = sk1 := resolve eq3963 eq3819 -- subsumption resolution 3963,3819
  have eq3990 : (old a sk1 c) ∨ c = b ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq3964.imp_left (fun h : c = sk2 ↦ superpose h eq2398)) -- superposition 2398,3964, 3964 into 2398, unify on (0).2 in 3964 and (0).3 in 2398
  have eq3993 : (old a c sk3) ∨ b = sk3 ∨ c = b ∨ c = sk1 := Or.assoc3 (eq3964.imp_left (fun h : c = sk2 ↦ superpose h eq2414)) -- superposition 2414,3964, 3964 into 2414, unify on (0).2 in 3964 and (0).2 in 2414
  have eq4008 : c = b ∨ b = sk1 ∨ c = sk1 := resolve eq3990 p4XY -- subsumption resolution 3990,66
  have eq4009 : b = sk1 ∨ c = sk1 := resolve eq4008 bc -- subsumption resolution 4008,64
  have eq4011 : b = sk3 ∨ c = b ∨ c = sk1 := resolve eq3993 p4XZ -- subsumption resolution 3993,67
  have eq4012 : b = sk3 ∨ c = sk1 := resolve eq4011 bc -- subsumption resolution 4011,64
  have eq4038 : (new a b sk2) ∨ c = sk1 := eq4009.imp_left (fun h : b = sk1 ↦ superpose h eq2334) -- superposition 2334,4009, 4009 into 2334, unify on (0).2 in 4009 and (0).2 in 2334
  have eq4067 : ¬(new a b sk2) ∨ c = sk1 := eq4012.imp_left (fun h : b = sk3 ↦ superpose h eq2336) -- superposition 2336,4012, 4012 into 2336, unify on (0).2 in 4012 and (0).2 in 2336
  have eq4084 : c = sk1 := resolve eq4067 eq4038 -- subsumption resolution 4067,4038
  have eq4088 : (new a c sk2) := Eq.mp (by simp only [eq4084, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2334 -- backward demodulation 2334,4084
  have eq4096 : c = b ∨ (old a sk1 sk2) ∨ b = sk2 := Eq.mp (by simp only [eq4084, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2398 -- backward demodulation 2398,4084
  have eq4276 : (old a sk1 sk2) ∨ b = sk2 := resolve eq4096 bc -- subsumption resolution 4096,64
  have eq4277 : (old a c sk2) ∨ b = sk2 := Eq.mp (by simp only [eq4084, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4276 -- forward demodulation 4276,4084
  have eq4278 : b = sk2 := resolve eq4277 p4XZ -- subsumption resolution 4277,67
  have eq4280 : ¬(new a sk3 b) := Eq.mp (by simp only [eq4278, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2336 -- backward demodulation 2336,4278
  have eq4285 : c = b ∨ (old a sk2 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq4278, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2419 -- backward demodulation 2419,4278
  have eq4329 : (new a c b) := Eq.mp (by simp only [eq4278, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4088 -- backward demodulation 4088,4278
  have eq4336 : (old a sk2 sk3) ∨ c = sk3 := resolve eq4285 bc -- subsumption resolution 4285,64
  have eq4337 : (old a b sk3) ∨ c = sk3 := Eq.mp (by simp only [eq4278, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4336 -- forward demodulation 4336,4278
  have eq4338 : c = sk3 := resolve eq4337 p3 -- subsumption resolution 4337,65
  have eq4340 : ¬(new a c b) := Eq.mp (by simp only [eq4338, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4280 -- backward demodulation 4280,4338
  subsumption eq4340 eq4329 -- subsumption resolution 4329,4340

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old b X (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq111 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X0 := resolve rule_def_1_2 old_mem2 -- resolution 82,93
  have eq145 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 91,95
  have eq191 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk0 := resolve eq145 rule_def_2_0 -- resolution 145,85
  have eq199 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq191 preserve_1 -- subsumption resolution 191,96
  have eq203 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk0 := resolve eq199 eq111 -- resolution 199,111
  have eq207 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq203 preserve_3 -- subsumption resolution 203,98
  have eq210 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq207 rule_def_0_0 -- resolution 207,76
  have eq211 : (old sk0 sk1 sk2) := resolve eq210 preserve_1 -- subsumption resolution 210,96
  have eq218 : memold sk0 := resolve eq211 old_mem1 -- resolution 211,92
  subsumption preserve_3 eq218 -- subsumption resolution 218,98

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq145 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 91,95
  have eq191 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk0 := resolve eq145 rule_def_2_0 -- resolution 145,85
  have eq192 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq145 rule_def_2_1 -- resolution 145,86
  have eq199 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq191 rule_def_0_0 -- subsumption resolution 191,76
  have eq200 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve eq192 preserve_4 -- subsumption resolution 192,99
  have eq201 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := resolve eq199 rule_def_1_0 -- resolution 199,80
  have eq208 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq201 preserve_4 -- subsumption resolution 201,99
  have eq214 : a = sk0 ∨ memold sk1 := resolve eq208 old_mem2 -- resolution 208,93
  have eq216 : a = sk0 := resolve eq214 preserve_3 -- subsumption resolution 214,98
  have eq220 : (sP1 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq216, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq200 -- backward demodulation 200,216
  have eq225 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq216, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq220 -- forward demodulation 220,216
  have eq226 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq216, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq225 -- forward demodulation 225,216
  have eq236 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := resolve eq226 rule_def_1_0 -- resolution 226,80
  have eq243 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := resolve eq236 preserve_4 -- subsumption resolution 236,99
  have eq247 : (old a sk1 sk2) ∨ b = sk1 := resolve eq243 rule_def_0_1 -- resolution 243,77
  have eq249 : (old a sk1 sk2) := resolve eq247 preserve_2 -- subsumption resolution 247,97
  have eq257 : memold sk1 := resolve eq249 old_mem2 -- resolution 249,93
  subsumption preserve_3 eq257 -- subsumption resolution 257,98

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sP2 : G → G → G → Prop) (memold : G → Prop) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq145 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 91,95
  have eq191 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk0 := resolve eq145 rule_def_2_0 -- resolution 145,85
  have eq192 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk1 := resolve eq145 rule_def_2_1 -- resolution 145,86
  have eq193 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk2 := resolve eq145 rule_def_2_2 -- resolution 145,87
  have eq199 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq191 rule_def_0_0 -- subsumption resolution 191,76
  have eq200 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq192 rule_def_1_0 -- subsumption resolution 192,80
  have eq201 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve eq193 preserve_2 -- subsumption resolution 193,97
  have eq203 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk2 := resolve eq199 rule_def_1_1 -- resolution 199,81
  have eq209 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq203 preserve_2 -- subsumption resolution 203,97
  have eq216 : a = sk0 ∨ memold sk2 := resolve eq209 old_mem3 -- resolution 209,94
  have eq217 : a = sk0 := resolve eq216 preserve_3 -- subsumption resolution 216,98
  have eq221 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq217, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq200 -- backward demodulation 200,217
  have eq222 : (sP1 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq217, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq201 -- backward demodulation 201,217
  have eq228 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq217, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq221 -- forward demodulation 221,217
  have eq229 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq217, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq222 -- forward demodulation 222,217
  have eq230 : (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) := Eq.mp (by simp only [eq217, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq229 -- forward demodulation 229,217
  have eq240 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq228 rule_def_0_2 -- resolution 228,78
  have eq243 : (old a sk1 sk2) ∨ c = sk1 := resolve eq240 preserve_4 -- subsumption resolution 240,99
  have eq251 : c = sk1 ∨ memold sk2 := resolve eq243 old_mem3 -- resolution 243,94
  have eq252 : c = sk1 := resolve eq251 preserve_3 -- subsumption resolution 251,98
  have eq255 : (sP1 a c sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) := Eq.mp (by simp only [eq252, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq230 -- backward demodulation 230,252
  have eq260 : (old a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a sk1 sk2) := Eq.mp (by simp only [eq252, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq255 -- forward demodulation 255,252
  have eq261 : (sP1 a c sk2) ∨ (sP0 a sk1 sk2) := resolve eq260 p4XZ -- subsumption resolution 260,68
  have eq262 : (sP1 a c sk2) ∨ (sP0 a c sk2) := Eq.mp (by simp only [eq252, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq261 -- forward demodulation 261,252
  have eq273 : (sP0 a c sk2) ∨ b = sk2 := resolve eq262 rule_def_1_1 -- resolution 262,81
  have eq280 : (sP0 a c sk2) := resolve eq273 preserve_2 -- subsumption resolution 273,97
  have eq283 : c = sk2 := resolve eq280 rule_def_0_2 -- resolution 280,78
  subsumption preserve_4 eq283 -- subsumption resolution 283,99

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X3 ∨ ¬ R X3 X0 X4 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X0 X2 X0 ∨ X1 = X2)
  rule_3 : (∀ X0 X1 X2 X3, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X0 X2 X3 ∨ R X0 X3 X2)
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
  let sP1 (X Y Z) := ∃ sF0, c = Y ∧ b = Z ∧ ps.R b X sF0 ∧ ps.R X sF0 a
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := ∃ sF1, a = X ∧ c = Y ∧ b = Z ∧ ps.R a a sF1 ∧ ps.R a sF1 b
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 bc p3 p4XY p4XZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_1 rule_def_2_2 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 ps.rule_1 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac p3 p4XY p4XZ p4YZ prev_0 ps.rule_2 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 ac bc p3 p4XY p4XZ p4YZ ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_2 rule_def_2_0 new_imp ps.mem_1 ps.mem_2
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) rule_def_0_0 rule_def_0_1 rule_def_1_0 rule_def_2_0 rule_def_2_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sP2 (· ∈ ps.finsupp) p4XZ rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_2 new_imp ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X2 X3 ∨ ¬ ps.compl X3 X0 X4 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X2) (max (Nat.pair X3 X0) (max (Nat.pair X1 X4) 0)))
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

theorem PartialSolution.toMagma_equation1112 :
    letI := ps.toMagma
    Equation1112 ℕ := by
  simp only [Equation1112, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun X1 (ps.complFun X0 X1)) (ps.complFun (ps.complFun X1 (ps.complFun X0 X1)) X0)


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter8 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation8 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation8 G := by
  use ℕ, PartialSolution.counter8.toMagma, PartialSolution.counter8.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter8.of_R 1 1 2] | rw [PartialSolution.counter8.of_R 1 2 2])
  all_goals simp [PartialSolution.counter8]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter411 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation411 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation411 G := by
  use ℕ, PartialSolution.counter411.toMagma, PartialSolution.counter411.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter411.of_R 1 1 2] | rw [PartialSolution.counter411.of_R 1 2 2])
  all_goals simp [PartialSolution.counter411]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1629 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 2), (2, 2, 2)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation1629 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation1629 G := by
  use ℕ, PartialSolution.counter1629.toMagma, PartialSolution.counter1629.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter1629.of_R 1 1 2] | rw [PartialSolution.counter1629.of_R 2 1 2] | rw [PartialSolution.counter1629.of_R 2 2 2])
  all_goals simp [PartialSolution.counter1629]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1832 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (2, 2, 2)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation1832 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation1832 G := by
  use ℕ, PartialSolution.counter1832.toMagma, PartialSolution.counter1832.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter1832.of_R 1 1 2] | rw [PartialSolution.counter1832.of_R 1 2 2] | rw [PartialSolution.counter1832.of_R 2 2 2])
  all_goals simp [PartialSolution.counter1832]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3253 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (1, 3, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation3253 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation3253 G := by
  use ℕ, PartialSolution.counter3253.toMagma, PartialSolution.counter3253.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3253.of_R 1 1 2] | rw [PartialSolution.counter3253.of_R 1 2 3] | rw [PartialSolution.counter3253.of_R 1 3 3])
  all_goals simp [PartialSolution.counter3253]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3319 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (1, 3, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation3319 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation3319 G := by
  use ℕ, PartialSolution.counter3319.toMagma, PartialSolution.counter3319.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1, 1
  repeat (first | rw [PartialSolution.counter3319.of_R 1 1 2] | rw [PartialSolution.counter3319.of_R 1 2 3] | rw [PartialSolution.counter3319.of_R 1 3 3])
  all_goals simp [PartialSolution.counter3319]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3862 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (1, 3, 1), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation3862 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation3862 G := by
  use ℕ, PartialSolution.counter3862.toMagma, PartialSolution.counter3862.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3862.of_R 1 1 2] | rw [PartialSolution.counter3862.of_R 1 2 2] | rw [PartialSolution.counter3862.of_R 1 3 1] | rw [PartialSolution.counter3862.of_R 2 1 3])
  all_goals simp [PartialSolution.counter3862]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3915 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (2, 2, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1112_not_implies_Equation3915 : ∃ (G : Type) (_ : Magma G), Equation1112 G ∧ ¬Equation3915 G := by
  use ℕ, PartialSolution.counter3915.toMagma, PartialSolution.counter3915.toMagma_equation1112
  simp only [not_forall, PartialSolution.toMagma]
  use 1, 2
  repeat (first | rw [PartialSolution.counter3915.of_R 1 1 2] | rw [PartialSolution.counter3915.of_R 1 2 2] | rw [PartialSolution.counter3915.of_R 2 2 1])
  all_goals simp [PartialSolution.counter3915]

end Eq1112