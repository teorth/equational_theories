import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq906

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_4 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X2 ∨ ¬ old X1 X1 X4 ∨ ¬ old X3 X3 X4 ∨ X1 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq76 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 68,69
  have eq77 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 68,70
  have eq87 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 sk2 b) := resolve eq76 rule_def_1_2 -- resolution 76,66
  have eq88 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk2 a) := resolve eq76 rule_def_1_1 -- resolution 76,65
  have eq89 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq76 rule_def_1_0 -- resolution 76,64
  have eq90 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq89 rule_def_0_2 -- resolution 89,62
  have eq91 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq89 rule_def_0_1 -- resolution 89,61
  have eq93 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (old sk3 sk3 b) := resolve eq77 rule_def_1_2 -- resolution 77,66
  have eq94 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (old sk0 sk3 a) := resolve eq77 rule_def_1_1 -- resolution 77,65
  have eq95 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq77 rule_def_1_0 -- resolution 77,64
  have eq98 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq90 old_0 -- resolution 90,52
  have eq100 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq95 rule_def_0_2 -- resolution 95,62
  have eq101 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq95 rule_def_0_1 -- resolution 95,61
  have eq102 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq95 rule_def_0_0 -- resolution 95,60
  have eq105 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ c = sk1 := resolve eq91 old_0 -- resolution 91,52
  have eq108 : (old sk2 sk2 b) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq87 rule_def_0_1 -- resolution 87,61
  have eq115 : (old sk0 sk2 a) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq88 rule_def_0_1 -- resolution 88,61
  have eq122 : (old sk3 sk3 b) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := resolve eq93 rule_def_0_1 -- resolution 93,61
  have eq128 : (old sk0 sk3 a) ∨ (old sk0 sk1 sk3) ∨ c = sk3 := resolve eq94 rule_def_0_2 -- resolution 94,62
  have eq148 (X0 X1 X2 : G) : (old sk0 sk1 sk2) ∨ b = sk1 ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ ¬(old X1 sk2 X2) ∨ ¬(old X1 X0 X2) := resolve eq108 old_4 -- resolution 108,56
  have eq222 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq98 eq102 -- resolution 98,102
  have eq227 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq222 rfl -- duplicate literal removal 222
  have eq231 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq227 preserve_2 -- subsumption resolution 227,71
  have eq235 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := Or.assoc3 (eq231.imp_left (fun h : c = sk2 ↦ superpose h eq76)) -- superposition 76,231, 231 into 76, unify on (0).2 in 231 and (0).3 in 76
  have eq256 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq235 p4XY -- subsumption resolution 235,49
  have eq257 : (sP1 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq256 rule_def_0_0 -- subsumption resolution 256,60
  have eq258 : c = sk1 ∨ a = sk0 := resolve eq257 rule_def_1_0 -- subsumption resolution 257,64
  have eq263 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq105 eq101 -- resolution 105,101
  have eq266 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq263 rfl -- duplicate literal removal 263
  have eq271 : b = sk1 ∨ c = sk1 := resolve eq266 preserve_2 -- subsumption resolution 266,71
  have eq279 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq271.imp_left (fun h : b = sk1 ↦ superpose h eq90)) -- superposition 90,271, 271 into 90, unify on (0).2 in 271 and (0).2 in 90
  have eq285 : (old sk0 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq271.imp_left (fun h : b = sk1 ↦ superpose h eq100)) -- superposition 100,271, 271 into 100, unify on (0).2 in 271 and (0).2 in 100
  have eq289 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq279 bc -- subsumption resolution 279,47
  have eq292 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq285 bc -- subsumption resolution 285,47
  have eq311 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (old sk2 sk2 b) ∨ a = sk0 := Or.assoc3 (eq258.imp_left (fun h : c = sk1 ↦ superpose h eq87)) -- superposition 87,258, 258 into 87, unify on (0).2 in 258 and (0).2 in 87
  have eq312 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (old sk0 sk2 a) ∨ a = sk0 := Or.assoc3 (eq258.imp_left (fun h : c = sk1 ↦ superpose h eq88)) -- superposition 88,258, 258 into 88, unify on (0).2 in 258 and (0).2 in 88
  have eq313 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (old sk3 sk3 b) ∨ a = sk0 := Or.assoc3 (eq258.imp_left (fun h : c = sk1 ↦ superpose h eq93)) -- superposition 93,258, 258 into 93, unify on (0).2 in 258 and (0).2 in 93
  have eq314 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (old sk0 sk3 a) ∨ a = sk0 := Or.assoc3 (eq258.imp_left (fun h : c = sk1 ↦ superpose h eq94)) -- superposition 94,258, 258 into 94, unify on (0).2 in 258 and (0).2 in 94
  have eq319 : (sP0 sk0 c sk2) ∨ (old sk2 sk2 b) ∨ a = sk0 := resolve eq311 p4XZ -- subsumption resolution 311,50
  have eq320 : (old sk2 sk2 b) ∨ a = sk0 := resolve eq319 rule_def_0_0 -- subsumption resolution 319,60
  have eq321 : (sP0 sk0 c sk2) ∨ (old sk0 sk2 a) ∨ a = sk0 := resolve eq312 p4XZ -- subsumption resolution 312,50
  have eq322 : (old sk0 sk2 a) ∨ a = sk0 := resolve eq321 rule_def_0_0 -- subsumption resolution 321,60
  have eq323 : (sP0 sk0 c sk3) ∨ (old sk3 sk3 b) ∨ a = sk0 := resolve eq313 p4XZ -- subsumption resolution 313,50
  have eq324 : (old sk3 sk3 b) ∨ a = sk0 := resolve eq323 rule_def_0_0 -- subsumption resolution 323,60
  have eq325 : (sP0 sk0 c sk3) ∨ (old sk0 sk3 a) ∨ a = sk0 := resolve eq314 p4XZ -- subsumption resolution 314,50
  have eq326 : (old sk0 sk3 a) ∨ a = sk0 := resolve eq325 rule_def_0_0 -- subsumption resolution 325,60
  have eq417 (X0 X1 X2 : G) : ¬(old X1 sk2 X2) ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ a = sk0 ∨ ¬(old X1 X0 X2) := resolve eq320 old_4 -- resolution 320,56
  have eq963 (X0 : G) : sk2 = X0 ∨ ¬(old X0 X0 b) ∨ a = sk0 ∨ ¬(old sk0 X0 a) ∨ a = sk0 := resolve eq417 eq322 -- resolution 417,322
  have eq977 (X0 : G) : ¬(old sk0 X0 a) ∨ ¬(old X0 X0 b) ∨ a = sk0 ∨ sk2 = X0 := resolve eq963 rfl -- duplicate literal removal 963
  have eq983 : ¬(old sk3 sk3 b) ∨ a = sk0 ∨ sk2 = sk3 ∨ a = sk0 := resolve eq977 eq326 -- resolution 977,326
  have eq988 : ¬(old sk3 sk3 b) ∨ a = sk0 ∨ sk2 = sk3 := resolve eq983 rfl -- duplicate literal removal 983
  have eq991 : ¬(old sk3 sk3 b) ∨ a = sk0 := resolve eq988 preserve_2 -- subsumption resolution 988,71
  have eq992 : a = sk0 := resolve eq991 eq324 -- subsumption resolution 991,324
  have eq1019 : (old a sk1 sk2) ∨ (old sk0 sk2 a) ∨ b = sk1 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq115 -- backward demodulation 115,992
  have eq1025 : (old a sk1 sk3) ∨ (old sk3 sk3 b) ∨ b = sk1 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq122 -- backward demodulation 122,992
  have eq1030 : (old a sk1 sk3) ∨ (old sk0 sk3 a) ∨ c = sk3 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq128 -- backward demodulation 128,992
  have eq1046 : ∀ (X0 X1 X2 : G) , (old a sk1 sk2) ∨ b = sk1 ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ ¬(old X1 sk2 X2) ∨ ¬(old X1 X0 X2) := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq148 -- backward demodulation 148,992
  have eq1114 : (old a b sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq289 -- backward demodulation 289,992
  have eq1117 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq292 -- backward demodulation 292,992
  have eq1151 : (old a sk2 a) ∨ (old a sk1 sk2) ∨ b = sk1 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1019 -- forward demodulation 1019,992
  have eq1152 : (old a sk3 a) ∨ (old a sk1 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq992, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1030 -- forward demodulation 1030,992
  have eq1188 : c = sk2 ∨ c = sk1 := resolve eq1114 p3 -- subsumption resolution 1114,48
  have eq1191 : c = sk3 ∨ c = sk1 := resolve eq1117 p3 -- subsumption resolution 1117,48
  have eq1219 : c ≠ sk2 ∨ c = sk1 := eq1191.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 71,1191, 1191 into 71, unify on (0).2 in 1191 and (0).2 in 71
  have eq1221 : c = sk1 := resolve eq1219 eq1188 -- subsumption resolution 1219,1188
  have eq1227 : c = b ∨ (old a sk1 sk3) ∨ (old sk3 sk3 b) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1025 -- backward demodulation 1025,1221
  have eq1241 : ∀ (X0 X1 X2 : G) , c = b ∨ (old a sk1 sk2) ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ ¬(old X1 sk2 X2) ∨ ¬(old X1 X0 X2) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1046 -- backward demodulation 1046,1221
  have eq1267 : c = b ∨ (old a sk2 a) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1151 -- backward demodulation 1151,1221
  have eq1268 : (old a c sk3) ∨ (old a sk3 a) ∨ c = sk3 := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1152 -- backward demodulation 1152,1221
  have eq1295 : (old a sk1 sk3) ∨ (old sk3 sk3 b) := resolve eq1227 bc -- subsumption resolution 1227,47
  have eq1296 : (old a c sk3) ∨ (old sk3 sk3 b) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1295 -- forward demodulation 1295,1221
  have eq1297 : (old sk3 sk3 b) := resolve eq1296 p4XZ -- subsumption resolution 1296,50
  have eq1321 (X0 X1 X2 : G) : (old a sk1 sk2) ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ ¬(old X1 sk2 X2) ∨ ¬(old X1 X0 X2) := resolve eq1241 bc -- subsumption resolution 1241,47
  have eq1322 : ∀ (X0 X1 X2 : G) , (old a c sk2) ∨ sk2 = X0 ∨ ¬(old X0 X0 b) ∨ ¬(old X1 sk2 X2) ∨ ¬(old X1 X0 X2) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1321 -- forward demodulation 1321,1221
  have eq1323 (X0 X1 X2 : G) : ¬(old X1 sk2 X2) ∨ ¬(old X0 X0 b) ∨ sk2 = X0 ∨ ¬(old X1 X0 X2) := resolve eq1322 p4XZ -- subsumption resolution 1322,50
  have eq1373 : (old a sk2 a) ∨ (old a sk1 sk2) := resolve eq1267 bc -- subsumption resolution 1267,47
  have eq1374 : (old a c sk2) ∨ (old a sk2 a) := Eq.mp (by simp only [eq1221, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1373 -- forward demodulation 1373,1221
  have eq1375 : (old a sk2 a) := resolve eq1374 p4XZ -- subsumption resolution 1374,50
  have eq1376 : (old a sk3 a) ∨ c = sk3 := resolve eq1268 p4XZ -- subsumption resolution 1268,50
  have eq1525 (X0 : G) : ¬(old a X0 a) ∨ sk2 = X0 ∨ ¬(old X0 X0 b) := resolve eq1323 eq1375 -- resolution 1323,1375
  have eq1528 : sk2 = sk3 ∨ ¬(old sk3 sk3 b) ∨ c = sk3 := resolve eq1525 eq1376 -- resolution 1525,1376
  have eq1530 : ¬(old sk3 sk3 b) ∨ c = sk3 := resolve eq1528 preserve_2 -- subsumption resolution 1528,71
  have eq1531 : c = sk3 := resolve eq1530 eq1297 -- subsumption resolution 1530,1297
  have eq1535 : (old c c b) := Eq.mp (by simp only [eq1531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1297 -- backward demodulation 1297,1531
  subsumption p4YZ eq1535 -- subsumption resolution 1535,51

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X1 X3 ∨ ¬ old X2 X3 X4 ∨ old X0 X4 X1)) (old_5 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X1 X2 ∨ ¬ old X3 X2 X0 ∨ old X3 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, c ≠ Y ∨ ¬ old X Z a ∨ ¬ old Z Z b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X3 ∨ ¬ new X2 X3 X4 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq80 (X0 X2 : G) : ¬(old X2 X2 b) ∨ (new X0 c X2) ∨ ¬(old X0 X2 a) := resolve imp_new_2 rfl -- equality resolution 66
  have eq83 (X0 : G) : ¬(new sk2 sk3 X0) ∨ sk4 = X0 := resolve prev_0 preserve_2 -- resolution 72,75
  have eq89 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 71,73
  have eq90 : (sP1 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ (sP0 sk1 sk1 sk3) := resolve new_imp preserve_1 -- resolution 71,74
  have eq91 : (sP1 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ (sP0 sk2 sk3 sk4) := resolve new_imp preserve_2 -- resolution 71,75
  have eq103 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq89 rule_def_1_0 -- resolution 89,67
  have eq104 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq103 rule_def_0_2 -- resolution 103,65
  have eq107 : (sP0 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ (old sk3 sk3 b) := resolve eq90 rule_def_1_2 -- resolution 90,69
  have eq108 : (sP0 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ (old sk1 sk3 a) := resolve eq90 rule_def_1_1 -- resolution 90,68
  have eq109 : (sP0 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ c = sk1 := resolve eq90 rule_def_1_0 -- resolution 90,67
  have eq110 (X0 : G) : ¬(old sk2 X0 sk1) ∨ c = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old X0 X0 sk1) ∨ c = sk1 := resolve eq104 old_5 -- resolution 104,60
  have eq114 : (sP0 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ (old sk4 sk4 b) := resolve eq91 rule_def_1_2 -- resolution 91,69
  have eq115 : (sP0 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ (old sk2 sk4 a) := resolve eq91 rule_def_1_1 -- resolution 91,68
  have eq116 : (sP0 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ c = sk3 := resolve eq91 rule_def_1_0 -- resolution 91,67
  have eq121 : (old sk1 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq109 rule_def_0_2 -- resolution 109,65
  have eq122 : (old sk1 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq109 rule_def_0_1 -- resolution 109,64
  have eq123 : (old sk1 sk1 sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq109 rule_def_0_0 -- resolution 109,63
  have eq128 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq116 rule_def_0_2 -- resolution 116,65
  have eq129 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq116 rule_def_0_1 -- resolution 116,64
  have eq130 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ a = sk2 := resolve eq116 rule_def_0_0 -- resolution 116,63
  have eq162 (X0 X1 : G) : ¬(old X1 X1 sk3) ∨ c = sk4 ∨ (old X0 sk4 X1) ∨ c = sk3 ∨ ¬(old X0 X1 sk2) := resolve eq128 old_1 -- resolution 128,56
  have eq166 : (old sk1 sk3 a) ∨ (old sk1 sk1 sk3) ∨ b = sk1 := resolve eq108 rule_def_0_1 -- resolution 108,64
  have eq173 : (old sk4 sk4 b) ∨ (old sk2 sk3 sk4) ∨ b = sk3 := resolve eq114 rule_def_0_1 -- resolution 114,64
  have eq179 : (old sk2 sk4 a) ∨ (old sk2 sk3 sk4) ∨ c = sk4 := resolve eq115 rule_def_0_2 -- resolution 115,65
  have eq180 : (old sk2 sk4 a) ∨ (old sk2 sk3 sk4) ∨ b = sk3 := resolve eq115 rule_def_0_1 -- resolution 115,64
  have eq181 : (old sk2 sk4 a) ∨ (old sk2 sk3 sk4) ∨ a = sk2 := resolve eq115 rule_def_0_0 -- resolution 115,63
  have eq707 (X0 : G) : c = sk4 ∨ (old X0 sk4 sk1) ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) ∨ c = sk1 ∨ c = sk3 := resolve eq162 eq121 -- resolution 162,121
  have eq708 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old X0 sk4 sk1) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 := resolve eq707 rfl -- duplicate literal removal 707
  have eq938 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq708 eq104 -- resolution 708,104
  have eq939 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq938 rfl -- duplicate literal removal 938
  have eq945 : c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ (new sk0 sk4 sk1) := resolve eq939 imp_new_0 -- resolution 939,61
  have eq946 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq945 preserve_3 -- subsumption resolution 945,76
  have eq947 : (new sk2 sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := eq946.imp_left (fun h : c = sk4 ↦ superpose h preserve_2) -- superposition 75,946, 946 into 75, unify on (0).2 in 946 and (0).3 in 75
  have eq953 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq946.imp_left (fun h : c = sk4 ↦ superpose h eq129)) -- superposition 129,946, 946 into 129, unify on (0).2 in 946 and (0).3 in 129
  have eq954 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq946.imp_left (fun h : c = sk4 ↦ superpose h eq130)) -- superposition 130,946, 946 into 130, unify on (0).2 in 946 and (0).3 in 130
  have eq986 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq954 rfl -- duplicate literal removal 954
  have eq987 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq953 rfl -- duplicate literal removal 953
  have eq991 : b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq987 p4XY -- subsumption resolution 987,52
  have eq992 : c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq986 p4XY -- subsumption resolution 986,52
  have eq1004 : (old sk1 sk1 b) ∨ c = sk1 ∨ c = b ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq991.imp_left (fun h : b = sk3 ↦ superpose h eq121)) -- superposition 121,991, 991 into 121, unify on (0).2 in 991 and (0).3 in 121
  have eq1078 : (old sk1 sk1 b) ∨ c = sk1 ∨ c = b ∨ c = sk3 ∨ c = sk2 := resolve eq1004 rfl -- duplicate literal removal 1004
  have eq1082 : (old sk1 sk1 b) ∨ c = sk1 ∨ c = sk3 ∨ c = sk2 := resolve eq1078 bc -- subsumption resolution 1078,50
  have eq1097 : (old sk1 sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq992.imp_left (fun h : c = sk3 ↦ superpose h eq122)) -- superposition 122,992, 992 into 122, unify on (0).2 in 992 and (0).3 in 122
  have eq1098 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq992.imp_left (fun h : c = sk3 ↦ superpose h eq123)) -- superposition 123,992, 992 into 123, unify on (0).2 in 992 and (0).3 in 123
  have eq1138 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk2 ∨ c = sk2 := resolve eq1098 rfl -- duplicate literal removal 1098
  have eq1139 : (old sk1 sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ a = sk2 ∨ c = sk2 := resolve eq1097 rfl -- duplicate literal removal 1097
  have eq1150 : c = sk2 ∨ b = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1139 p4XY -- subsumption resolution 1139,52
  have eq1151 : c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1138 p4XY -- subsumption resolution 1138,52
  have eq1155 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk2 ∨ c = sk1 := Or.assoc3 (eq1150.imp_left (fun h : c = sk2 ↦ superpose h eq89)) -- superposition 89,1150, 1150 into 89, unify on (0).2 in 1150 and (0).3 in 89
  have eq1254 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1155 p4XY -- subsumption resolution 1155,52
  have eq1255 : (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1254 rule_def_1_0 -- subsumption resolution 1254,67
  have eq1256 : a = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq1255 rule_def_0_1 -- subsumption resolution 1255,64
  have eq1262 (X0 : G) : ¬(new a sk3 X0) ∨ sk4 = X0 ∨ b = sk1 ∨ c = sk1 := Or.assoc2 (eq1256.imp_left (fun h : a = sk2 ↦ superpose h eq83)) -- superposition 83,1256, 1256 into 83, unify on (0).2 in 1256 and (0).1 in 83
  have eq1263 : (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP0 sk0 sk1 a) ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq1256.imp_left (fun h : a = sk2 ↦ superpose h eq89)) -- superposition 89,1256, 1256 into 89, unify on (0).2 in 1256 and (0).3 in 89
  have eq1377 : (old sk0 sk1 a) ∨ (sP0 sk0 sk1 a) ∨ b = sk1 ∨ c = sk1 := resolve eq1263 rule_def_1_0 -- subsumption resolution 1263,67
  have eq1378 : (old sk0 sk1 a) ∨ b = sk1 ∨ c = sk1 := resolve eq1377 rule_def_0_1 -- subsumption resolution 1377,64
  have eq1438 : (old c sk4 a) ∨ (old c sk3 sk4) ∨ a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := Or.assoc3 (eq1151.imp_left (fun h : c = sk2 ↦ superpose h eq181)) -- superposition 181,1151, 1151 into 181, unify on (0).2 in 1151 and (0).1 in 181
  have eq1516 : (old c sk3 sk4) ∨ a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1438 p4YZ -- subsumption resolution 1438,54
  have eq1517 : a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq1516 p4YZ -- subsumption resolution 1516,54
  have eq1518 : a = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq1517 ac -- subsumption resolution 1517,49
  have eq1525 (X0 : G) : ¬(new a sk3 X0) ∨ sk4 = X0 ∨ a = sk1 ∨ c = sk1 := Or.assoc2 (eq1518.imp_left (fun h : a = sk2 ↦ superpose h eq83)) -- superposition 83,1518, 1518 into 83, unify on (0).2 in 1518 and (0).1 in 83
  have eq1531 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq1518.imp_left (fun h : a = sk2 ↦ superpose h eq104)) -- superposition 104,1518, 1518 into 104, unify on (0).2 in 1518 and (0).3 in 104
  have eq1620 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c ∨ a = sk1 := resolve eq1531 rfl -- duplicate literal removal 1531
  have eq1625 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = sk1 := resolve eq1620 ac -- subsumption resolution 1620,49
  have eq2076 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq1518.imp_left (fun h : a = sk2 ↦ superpose h eq947)) -- superposition 947,1518, 1518 into 947, unify on (0).2 in 1518 and (0).1 in 947
  have eq2077 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ b = sk1 ∨ c = sk1 := Or.assoc4 (eq1256.imp_left (fun h : a = sk2 ↦ superpose h eq947)) -- superposition 947,1256, 1256 into 947, unify on (0).2 in 1256 and (0).1 in 947
  have eq2082 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ b = sk1 := resolve eq2077 rfl -- duplicate literal removal 2077
  have eq2083 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ a = sk1 := resolve eq2076 rfl -- duplicate literal removal 2076
  have eq2086 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq2083 ac -- subsumption resolution 2083,49
  have eq2087 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq2082 ac -- subsumption resolution 2082,49
  have eq2141 (X0 : G) : ¬(old X0 sk1 a) ∨ c = sk3 ∨ c = sk2 ∨ (new X0 c sk1) ∨ c = sk1 := resolve eq1082 eq80 -- resolution 1082,80
  have eq2539 : c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk4 ∨ a = sk1 ∨ c = sk1 := resolve eq2086 eq1525 -- resolution 2086,1525
  have eq2548 : c = sk4 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := resolve eq2539 rfl -- duplicate literal removal 2539
  have eq2570 : ¬(new sk0 c sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := eq2548.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 76,2548, 2548 into 76, unify on (0).2 in 2548 and (0).2 in 76
  have eq2827 : c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ c = sk4 ∨ b = sk1 ∨ c = sk1 := resolve eq2087 eq1262 -- resolution 2087,1262
  have eq2836 : c = sk4 ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 := resolve eq2827 rfl -- duplicate literal removal 2827
  have eq2855 : ¬(new sk0 c sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 := eq2836.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 76,2836, 2836 into 76, unify on (0).2 in 2836 and (0).2 in 76
  have eq5545 : c = sk3 ∨ c = sk2 ∨ (new sk0 c sk1) ∨ c = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq2141 eq1625 -- resolution 2141,1625
  have eq5546 : c = sk3 ∨ c = sk2 ∨ (new sk0 c sk1) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq2141 eq1378 -- resolution 2141,1378
  have eq5547 : c = sk3 ∨ c = sk2 ∨ (new sk0 c sk1) ∨ c = sk1 ∨ b = sk1 := resolve eq5546 rfl -- duplicate literal removal 5546
  have eq5548 : c = sk3 ∨ c = sk2 ∨ (new sk0 c sk1) ∨ c = sk1 ∨ a = sk1 := resolve eq5545 rfl -- duplicate literal removal 5545
  have eq5549 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5548 eq2570 -- subsumption resolution 5548,2570
  have eq5550 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq5547 eq2855 -- subsumption resolution 5547,2855
  have eq5560 : (sP1 sk1 sk1 c) ∨ (old sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5549.imp_left (fun h : c = sk3 ↦ superpose h eq90)) -- superposition 90,5549, 5549 into 90, unify on (0).2 in 5549 and (0).3 in 90
  have eq5670 : (sP1 sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5560 p4XY -- subsumption resolution 5560,52
  have eq5671 : (sP1 sk1 sk1 c) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5670 rule_def_0_0 -- subsumption resolution 5670,63
  have eq5672 : c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5671 rule_def_1_0 -- subsumption resolution 5671,67
  have eq5694 : a = c ∨ c = sk1 ∨ a = sk1 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq1518.imp_left (fun h : a = sk2 ↦ superpose h eq5672)) -- superposition 5672,1518, 1518 into 5672, unify on (0).2 in 1518 and (0).2 in 5672
  have eq5883 : a = c ∨ c = sk1 ∨ a = sk1 := resolve eq5694 rfl -- duplicate literal removal 5694
  have eq5886 : c = sk1 ∨ a = sk1 := resolve eq5883 ac -- subsumption resolution 5883,49
  have eq5904 : (old c sk3 a) ∨ (old c c sk3) ∨ c = b ∨ a = sk1 := Or.assoc3 (eq5886.imp_left (fun h : c = sk1 ↦ superpose h eq166)) -- superposition 166,5886, 5886 into 166, unify on (0).2 in 5886 and (0).1 in 166
  have eq5943 : (old c c sk3) ∨ c = b ∨ a = sk1 := resolve eq5904 p4YZ -- subsumption resolution 5904,54
  have eq5944 : c = b ∨ a = sk1 := resolve eq5943 p4YZ -- subsumption resolution 5943,54
  have eq5945 : a = sk1 := resolve eq5944 bc -- subsumption resolution 5944,50
  have eq5948 : ¬(new sk0 sk4 a) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 76,5945
  have eq5959 : (sP0 a a sk3) ∨ (old sk1 sk1 sk3) ∨ (old sk3 sk3 b) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq107 -- backward demodulation 107,5945
  have eq5962 : ∀ (X0 : G) , a = c ∨ ¬(old sk2 X0 sk1) ∨ c = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old X0 X0 sk1) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq110 -- backward demodulation 110,5945
  have eq5968 : (old a a sk3) ∨ c = sk1 ∨ c = sk3 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq121 -- backward demodulation 121,5945
  have eq6157 : a = c ∨ a = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1256 -- backward demodulation 1256,5945
  have eq6433 : a = c ∨ c = sk3 ∨ c = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5550 -- backward demodulation 5550,5945
  have eq6457 : (sP0 a a sk3) ∨ (old a a sk3) ∨ (old sk3 sk3 b) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5959 -- forward demodulation 5959,5945
  have eq6463 (X0 : G) : ¬(old sk2 X0 sk1) ∨ c = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old X0 X0 sk1) := resolve eq5962 ac -- subsumption resolution 5962,49
  have eq6464 : ∀ (X0 : G) , ¬(old sk2 X0 a) ∨ c = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old X0 X0 sk1) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6463 -- forward demodulation 6463,5945
  have eq6465 : ∀ (X0 : G) , (old sk0 X0 a) ∨ ¬(old sk2 X0 a) ∨ c = sk2 ∨ ¬(old X0 X0 sk1) := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6464 -- forward demodulation 6464,5945
  have eq6466 : ∀ (X0 : G) , ¬(old sk2 X0 a) ∨ (old sk0 X0 a) ∨ ¬(old X0 X0 a) ∨ c = sk2 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6465 -- forward demodulation 6465,5945
  have eq6482 : a = c ∨ (old a a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5968 -- forward demodulation 5968,5945
  have eq6483 : (old a a sk3) ∨ c = sk3 := resolve eq6482 ac -- subsumption resolution 6482,49
  have eq6664 : a = sk2 ∨ b = sk1 := resolve eq6157 ac -- subsumption resolution 6157,49
  have eq6665 : a = sk2 ∨ a = b := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6664 -- forward demodulation 6664,5945
  have eq6981 : c = sk3 ∨ c = sk2 ∨ b = sk1 := resolve eq6433 ac -- subsumption resolution 6433,49
  have eq6982 : c = sk3 ∨ a = b ∨ c = sk2 := Eq.mp (by simp only [eq5945, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6981 -- forward demodulation 6981,5945
  have eq7431 : (sP0 a a c) ∨ (old a a c) ∨ (old c c b) ∨ a = b ∨ c = sk2 := Or.assoc3 (eq6982.imp_left (fun h : c = sk3 ↦ superpose h eq6457)) -- superposition 6457,6982, 6982 into 6457, unify on (0).2 in 6982 and (0).3 in 6457
  have eq7446 : (sP0 a a c) ∨ (old c c b) ∨ a = b ∨ c = sk2 := resolve eq7431 p4XY -- subsumption resolution 7431,52
  have eq7447 : (sP0 a a c) ∨ a = b ∨ c = sk2 := resolve eq7446 p4YZ -- subsumption resolution 7446,54
  have eq7448 : c = sk2 ∨ a = b := resolve eq7447 rule_def_0_1 -- subsumption resolution 7447,64
  have eq7455 : a = c ∨ a = b ∨ a = b := Or.assoc2 (eq6665.imp_left (fun h : a = sk2 ↦ superpose h eq7448)) -- superposition 7448,6665, 6665 into 7448, unify on (0).2 in 6665 and (0).2 in 7448
  have eq7508 : a = c ∨ a = b := resolve eq7455 rfl -- duplicate literal removal 7455
  have eq7509 : a = b := resolve eq7508 ac -- subsumption resolution 7508,49
  have eq7511 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq7509, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 51,7509
  have eq7525 : (old sk4 sk4 a) ∨ (old sk2 sk3 sk4) ∨ b = sk3 := Eq.mp (by simp only [eq7509, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq173 -- backward demodulation 173,7509
  have eq7527 : a = sk3 ∨ (old sk2 sk4 a) ∨ (old sk2 sk3 sk4) := Eq.mp (by simp only [eq7509, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq180 -- backward demodulation 180,7509
  have eq7673 : a = sk3 ∨ (old sk4 sk4 a) ∨ (old sk2 sk3 sk4) := Eq.mp (by simp only [eq7509, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7525 -- forward demodulation 7525,7509
  have eq7712 : c = sk3 := resolve eq7511 eq6483 -- resolution 7511,6483
  have eq7720 : (old sk2 c sk4) ∨ (old sk2 sk4 a) ∨ c = sk4 := Eq.mp (by simp only [eq7712, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq179 -- backward demodulation 179,7712
  have eq7753 : (old sk2 c sk4) ∨ a = sk3 ∨ (old sk2 sk4 a) := Eq.mp (by simp only [eq7712, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7527 -- backward demodulation 7527,7712
  have eq7777 : (old sk2 c sk4) ∨ a = sk3 ∨ (old sk4 sk4 a) := Eq.mp (by simp only [eq7712, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7673 -- backward demodulation 7673,7712
  have eq7796 : (old sk2 sk4 a) ∨ c = sk4 := resolve eq7720 p4XZ -- subsumption resolution 7720,53
  have eq7816 : a = sk3 ∨ (old sk2 sk4 a) := resolve eq7753 p4XZ -- subsumption resolution 7753,53
  have eq7817 : a = c ∨ (old sk2 sk4 a) := Eq.mp (by simp only [eq7712, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7816 -- forward demodulation 7816,7712
  have eq7818 : (old sk2 sk4 a) := resolve eq7817 ac -- subsumption resolution 7817,49
  have eq7851 : a = sk3 ∨ (old sk4 sk4 a) := resolve eq7777 p4XZ -- subsumption resolution 7777,53
  have eq7852 : a = c ∨ (old sk4 sk4 a) := Eq.mp (by simp only [eq7712, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7851 -- forward demodulation 7851,7712
  have eq7853 : (old sk4 sk4 a) := resolve eq7852 ac -- subsumption resolution 7852,49
  have eq8054 : (old sk0 sk4 a) ∨ ¬(old sk4 sk4 a) ∨ c = sk2 := resolve eq6466 eq7818 -- resolution 6466,7818
  have eq8057 : (old sk0 sk4 a) ∨ c = sk2 := resolve eq8054 eq7853 -- subsumption resolution 8054,7853
  have eq8064 : c = sk2 ∨ (new sk0 sk4 a) := resolve eq8057 imp_new_0 -- resolution 8057,61
  have eq8065 : c = sk2 := resolve eq8064 eq5948 -- subsumption resolution 8064,5948
  have eq8103 : (old c sk4 a) ∨ c = sk4 := Eq.mp (by simp only [eq8065, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7796 -- backward demodulation 7796,8065
  have eq8153 : c = sk4 := resolve eq8103 p4YZ -- subsumption resolution 8103,54
  have eq8156 : (old c c a) := Eq.mp (by simp only [eq8153, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7853 -- backward demodulation 7853,8153
  subsumption p4YZ eq8156 -- subsumption resolution 8156,54

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X1 X0 ∨ ¬ old X2 X2 X1 ∨ X0 = X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X1 X0 ∨ ¬ new X2 X2 X1 ∨ X0 = X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq92 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 73,76
  have eq93 : (sP1 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ (sP0 sk2 sk1 sk0) := resolve new_imp preserve_1 -- resolution 73,77
  have eq94 : (sP1 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (sP0 sk2 sk2 sk1) := resolve new_imp preserve_2 -- resolution 73,78
  have eq109 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (old sk0 sk1 a) := resolve eq92 rule_def_1_1 -- resolution 92,70
  have eq110 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq92 rule_def_1_0 -- resolution 92,69
  have eq113 : (sP0 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ c = sk1 := resolve eq93 rule_def_1_0 -- resolution 93,69
  have eq114 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq110 rule_def_0_2 -- resolution 110,67
  have eq116 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq110 rule_def_0_0 -- resolution 110,65
  have eq117 : (sP0 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (old sk1 sk1 b) := resolve eq94 rule_def_1_2 -- resolution 94,71
  have eq119 : (sP0 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ c = sk2 := resolve eq94 rule_def_1_0 -- resolution 94,69
  have eq143 : (old sk2 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq113 rule_def_0_2 -- resolution 113,67
  have eq150 : (old sk2 sk2 sk1) ∨ c = sk2 ∨ c = sk1 := resolve eq119 rule_def_0_2 -- resolution 119,67
  have eq152 : (old sk2 sk2 sk1) ∨ c = sk2 ∨ a = sk2 := resolve eq119 rule_def_0_0 -- resolution 119,65
  have eq165 : (old sk0 sk1 a) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq109 rule_def_0_1 -- resolution 109,66
  have eq173 (X0 : G) : ¬(old sk2 sk1 X0) ∨ c = sk1 ∨ sk2 = X0 ∨ c = sk2 ∨ ¬(old X0 X0 sk1) := resolve eq150 old_2 -- resolution 150,59
  have eq195 : (old sk2 sk2 sk1) ∨ (old sk1 sk1 b) ∨ b = sk2 := resolve eq117 rule_def_0_1 -- resolution 117,66
  have eq751 : c = sk1 ∨ sk0 = sk2 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq173 eq143 -- resolution 173,143
  have eq762 : c = sk1 ∨ sk0 = sk2 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk0 := resolve eq751 rfl -- duplicate literal removal 751
  have eq763 : c = sk1 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk0 := resolve eq762 preserve_3 -- subsumption resolution 762,79
  have eq764 : c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq763 eq114 -- subsumption resolution 763,114
  have eq772 : (sP1 c sk1 sk0) ∨ (old c sk1 sk0) ∨ (sP0 c sk1 sk0) ∨ c = sk1 ∨ c = sk0 := Or.assoc3 (eq764.imp_left (fun h : c = sk2 ↦ superpose h eq93)) -- superposition 93,764, 764 into 93, unify on (0).2 in 764 and (0).1 in 93
  have eq827 : (sP1 c sk1 sk0) ∨ (sP0 c sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq772 p4YZ -- subsumption resolution 772,56
  have eq828 : (sP1 c sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq827 rule_def_0_2 -- subsumption resolution 827,67
  have eq829 : c = sk1 ∨ c = sk0 := resolve eq828 rule_def_1_0 -- subsumption resolution 828,69
  have eq858 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq829.imp_left (fun h : c = sk1 ↦ superpose h eq116)) -- superposition 116,829, 829 into 116, unify on (0).2 in 829 and (0).3 in 116
  have eq914 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq858 rfl -- duplicate literal removal 858
  have eq927 : c = sk0 ∨ a = sk0 := resolve eq914 p4XY -- subsumption resolution 914,54
  have eq1031 : (old c sk1 a) ∨ (old c c sk1) ∨ c = b ∨ a = sk0 := Or.assoc3 (eq927.imp_left (fun h : c = sk0 ↦ superpose h eq165)) -- superposition 165,927, 927 into 165, unify on (0).2 in 927 and (0).1 in 165
  have eq1064 : (old c c sk1) ∨ c = b ∨ a = sk0 := resolve eq1031 p4YZ -- subsumption resolution 1031,56
  have eq1065 : c = b ∨ a = sk0 := resolve eq1064 p4YZ -- subsumption resolution 1064,56
  have eq1066 : a = sk0 := resolve eq1065 bc -- subsumption resolution 1065,52
  have eq1069 : a ≠ sk2 := Eq.mp (by simp only [eq1066, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 79,1066
  have eq1220 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq1066, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq829 -- backward demodulation 829,1066
  have eq1415 : c = sk1 := resolve eq1220 ac -- subsumption resolution 1220,51
  have eq1425 : (old sk2 sk2 c) ∨ c = sk2 ∨ a = sk2 := Eq.mp (by simp only [eq1415, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq152 -- backward demodulation 152,1415
  have eq1440 : (old sk2 sk2 c) ∨ (old sk1 sk1 b) ∨ b = sk2 := Eq.mp (by simp only [eq1415, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq195 -- backward demodulation 195,1415
  have eq1514 : c = sk2 ∨ a = sk2 := resolve eq1425 p4XY -- subsumption resolution 1425,54
  have eq1515 : c = sk2 := resolve eq1514 eq1069 -- subsumption resolution 1514,1069
  have eq1526 : (old sk1 sk1 b) ∨ b = sk2 := resolve eq1440 p4XY -- subsumption resolution 1440,54
  have eq1527 : (old c c b) ∨ b = sk2 := Eq.mp (by simp only [eq1415, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1526 -- forward demodulation 1526,1415
  have eq1528 : b = sk2 := resolve eq1527 p4YZ -- subsumption resolution 1527,56
  have eq1529 : c = b := Eq.mp (by simp only [eq1515, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1528 -- forward demodulation 1528,1515
  subsumption bc eq1529 -- subsumption resolution 1529,52

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X1 ∨ ¬ old X2 X2 X1 ∨ X2 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X0 X1 ∨ ¬ new X2 X2 X1 ∨ X2 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq97 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 75,79
  have eq98 : (sP1 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) := resolve new_imp preserve_1 -- resolution 75,80
  have eq99 : (sP1 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (sP0 sk2 sk2 sk1) := resolve new_imp preserve_2 -- resolution 75,81
  have eq114 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (old sk0 sk1 a) := resolve eq97 rule_def_1_1 -- resolution 97,72
  have eq115 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq97 rule_def_1_0 -- resolution 97,71
  have eq116 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq115 rule_def_0_2 -- resolution 115,69
  have eq118 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq115 rule_def_0_0 -- resolution 115,67
  have eq121 : (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ c = sk0 := resolve eq98 rule_def_1_0 -- resolution 98,71
  have eq129 : (sP0 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ (old sk1 sk1 b) := resolve eq99 rule_def_1_2 -- resolution 99,73
  have eq131 : (sP0 sk2 sk2 sk1) ∨ (old sk2 sk2 sk1) ∨ c = sk2 := resolve eq99 rule_def_1_0 -- resolution 99,71
  have eq146 : (old sk2 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq121 rule_def_0_2 -- resolution 121,69
  have eq157 : (old sk2 sk2 sk1) ∨ c = sk2 ∨ c = sk1 := resolve eq131 rule_def_0_2 -- resolution 131,69
  have eq159 : (old sk2 sk2 sk1) ∨ c = sk2 ∨ a = sk2 := resolve eq131 rule_def_0_0 -- resolution 131,67
  have eq172 (X0 : G) : ¬(old sk2 X0 sk1) ∨ c = sk1 ∨ sk2 = X0 ∨ c = sk2 ∨ ¬(old X0 X0 sk1) := resolve eq157 old_3 -- resolution 157,62
  have eq175 : (old sk0 sk1 a) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq114 rule_def_0_1 -- resolution 114,68
  have eq206 : (old sk2 sk2 sk1) ∨ (old sk1 sk1 b) ∨ b = sk2 := resolve eq129 rule_def_0_1 -- resolution 129,68
  have eq716 : c = sk1 ∨ sk0 = sk2 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq172 eq146 -- resolution 172,146
  have eq731 : c = sk1 ∨ sk0 = sk2 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk0 := resolve eq716 rfl -- duplicate literal removal 716
  have eq743 : c = sk1 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk0 := resolve eq731 preserve_3 -- subsumption resolution 731,82
  have eq744 : c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq743 eq116 -- subsumption resolution 743,116
  have eq751 : (sP1 c sk0 sk1) ∨ (old c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ c = sk1 ∨ c = sk0 := Or.assoc3 (eq744.imp_left (fun h : c = sk2 ↦ superpose h eq98)) -- superposition 98,744, 744 into 98, unify on (0).2 in 744 and (0).1 in 98
  have eq808 : (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq751 p4YZ -- subsumption resolution 751,58
  have eq809 : (sP1 c sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq808 rule_def_0_2 -- subsumption resolution 808,69
  have eq810 : c = sk1 ∨ c = sk0 := resolve eq809 rule_def_1_0 -- subsumption resolution 809,71
  have eq828 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq810.imp_left (fun h : c = sk1 ↦ superpose h eq118)) -- superposition 118,810, 810 into 118, unify on (0).2 in 810 and (0).3 in 118
  have eq883 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq828 rfl -- duplicate literal removal 828
  have eq892 : c = sk0 ∨ a = sk0 := resolve eq883 p4XY -- subsumption resolution 883,56
  have eq992 : (old c sk1 a) ∨ (old c c sk1) ∨ c = b ∨ a = sk0 := Or.assoc3 (eq892.imp_left (fun h : c = sk0 ↦ superpose h eq175)) -- superposition 175,892, 892 into 175, unify on (0).2 in 892 and (0).1 in 175
  have eq1023 : (old c c sk1) ∨ c = b ∨ a = sk0 := resolve eq992 p4YZ -- subsumption resolution 992,58
  have eq1024 : c = b ∨ a = sk0 := resolve eq1023 p4YZ -- subsumption resolution 1023,58
  have eq1025 : a = sk0 := resolve eq1024 bc -- subsumption resolution 1024,54
  have eq1028 : a ≠ sk2 := Eq.mp (by simp only [eq1025, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 82,1025
  have eq1204 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq1025, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq810 -- backward demodulation 810,1025
  have eq1397 : c = sk1 := resolve eq1204 ac -- subsumption resolution 1204,53
  have eq1408 : (old sk2 sk2 c) ∨ c = sk2 ∨ a = sk2 := Eq.mp (by simp only [eq1397, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq159 -- backward demodulation 159,1397
  have eq1423 : (old sk2 sk2 c) ∨ (old sk1 sk1 b) ∨ b = sk2 := Eq.mp (by simp only [eq1397, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq206 -- backward demodulation 206,1397
  have eq1505 : c = sk2 ∨ a = sk2 := resolve eq1408 p4XY -- subsumption resolution 1408,56
  have eq1506 : c = sk2 := resolve eq1505 eq1028 -- subsumption resolution 1505,1028
  have eq1516 : (old sk1 sk1 b) ∨ b = sk2 := resolve eq1423 p4XY -- subsumption resolution 1423,56
  have eq1517 : (old c c b) ∨ b = sk2 := Eq.mp (by simp only [eq1397, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1516 -- forward demodulation 1516,1397
  have eq1518 : b = sk2 := resolve eq1517 p4YZ -- subsumption resolution 1517,58
  have eq1519 : c = b := Eq.mp (by simp only [eq1506, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1518 -- forward demodulation 1518,1506
  subsumption bc eq1519 -- subsumption resolution 1519,54

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_4 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X2 ∨ ¬ old X1 X1 X4 ∨ ¬ old X3 X3 X4 ∨ X1 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X2 ∨ ¬ new X1 X1 X4 ∨ ¬ new X3 X3 X4 ∨ X1 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq107 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 78,83
  have eq108 : (sP1 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) := resolve new_imp preserve_1 -- resolution 78,84
  have eq109 : (sP1 sk1 sk1 sk4) ∨ (old sk1 sk1 sk4) ∨ (sP0 sk1 sk1 sk4) := resolve new_imp preserve_2 -- resolution 78,85
  have eq110 : (sP1 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ (sP0 sk3 sk3 sk4) := resolve new_imp preserve_3 -- resolution 78,86
  have eq128 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq107 rule_def_1_0 -- resolution 107,74
  have eq129 : (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (old sk2 sk2 b) := resolve eq108 rule_def_1_2 -- resolution 108,76
  have eq131 : (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ c = sk3 := resolve eq108 rule_def_1_0 -- resolution 108,74
  have eq132 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq128 rule_def_0_2 -- resolution 128,72
  have eq133 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq128 rule_def_0_1 -- resolution 128,71
  have eq136 : (sP0 sk1 sk1 sk4) ∨ (old sk1 sk1 sk4) ∨ (old sk1 sk4 a) := resolve eq109 rule_def_1_1 -- resolution 109,75
  have eq137 : (sP0 sk1 sk1 sk4) ∨ (old sk1 sk1 sk4) ∨ c = sk1 := resolve eq109 rule_def_1_0 -- resolution 109,74
  have eq143 : (sP0 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ (old sk3 sk4 a) := resolve eq110 rule_def_1_1 -- resolution 110,75
  have eq144 : (sP0 sk3 sk3 sk4) ∨ (old sk3 sk3 sk4) ∨ c = sk3 := resolve eq110 rule_def_1_0 -- resolution 110,74
  have eq153 : (old sk0 sk3 sk2) ∨ c = sk3 ∨ c = sk2 := resolve eq131 rule_def_0_2 -- resolution 131,72
  have eq154 : (old sk0 sk3 sk2) ∨ c = sk3 ∨ b = sk3 := resolve eq131 rule_def_0_1 -- resolution 131,71
  have eq168 : (old sk1 sk1 sk4) ∨ c = sk1 ∨ c = sk4 := resolve eq137 rule_def_0_2 -- resolution 137,72
  have eq169 : (old sk1 sk1 sk4) ∨ c = sk1 ∨ b = sk1 := resolve eq137 rule_def_0_1 -- resolution 137,71
  have eq170 : (old sk1 sk1 sk4) ∨ c = sk1 ∨ a = sk1 := resolve eq137 rule_def_0_0 -- resolution 137,70
  have eq175 (X0 X1 X2 : G) : ¬(old X1 sk1 X2) ∨ c = sk4 ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ ¬(old X1 X0 X2) := resolve eq168 old_4 -- resolution 168,66
  have eq178 : (old sk3 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq144 rule_def_0_2 -- resolution 144,72
  have eq179 : (old sk3 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq144 rule_def_0_1 -- resolution 144,71
  have eq185 (X0 X1 X2 : G) : ¬(old X1 sk1 X2) ∨ b = sk1 ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ ¬(old X1 X0 X2) := resolve eq169 old_4 -- resolution 169,66
  have eq209 : (old sk2 sk2 b) ∨ (old sk0 sk3 sk2) ∨ b = sk3 := resolve eq129 rule_def_0_1 -- resolution 129,71
  have eq240 : (old sk1 sk4 a) ∨ (old sk1 sk1 sk4) ∨ b = sk1 := resolve eq136 rule_def_0_1 -- resolution 136,71
  have eq261 : (old sk3 sk4 a) ∨ (old sk3 sk3 sk4) ∨ c = sk4 := resolve eq143 rule_def_0_2 -- resolution 143,72
  have eq262 : (old sk3 sk4 a) ∨ (old sk3 sk3 sk4) ∨ b = sk3 := resolve eq143 rule_def_0_1 -- resolution 143,71
  have eq263 : (old sk3 sk4 a) ∨ (old sk3 sk3 sk4) ∨ a = sk3 := resolve eq143 rule_def_0_0 -- resolution 143,70
  have eq1931 (X0 : G) : c = sk4 ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ ¬(old sk0 X0 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq175 eq132 -- resolution 175,132
  have eq1938 (X0 : G) : ¬(old sk0 X0 sk2) ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 := resolve eq1931 rfl -- duplicate literal removal 1931
  have eq1942 (X0 : G) : b = sk1 ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ ¬(old sk0 X0 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq185 eq133 -- resolution 185,133
  have eq1951 (X0 : G) : ¬(old sk0 X0 sk2) ∨ sk1 = X0 ∨ ¬(old X0 X0 sk4) ∨ c = sk1 ∨ b = sk1 := resolve eq1942 rfl -- duplicate literal removal 1942
  have eq1961 : sk1 = sk3 ∨ ¬(old sk3 sk3 sk4) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 := resolve eq1951 eq153 -- resolution 1951,153
  have eq1971 : ¬(old sk3 sk3 sk4) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 := resolve eq1961 preserve_4 -- subsumption resolution 1961,87
  have eq3309 : c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk3 ∨ c = sk4 := resolve eq1971 eq178 -- resolution 1971,178
  have eq3316 : c = sk4 ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq3309 rfl -- duplicate literal removal 3309
  have eq3329 : (sP1 sk1 sk1 c) ∨ (old sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq3316.imp_left (fun h : c = sk4 ↦ superpose h eq109)) -- superposition 109,3316, 3316 into 109, unify on (0).2 in 3316 and (0).3 in 109
  have eq3506 : (sP1 sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq3329 p4XY -- subsumption resolution 3329,59
  have eq3507 : (sP0 sk1 sk1 c) ∨ b = sk1 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq3506 rule_def_1_0 -- subsumption resolution 3506,74
  have eq3508 : c = sk3 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq3507 rule_def_0_1 -- subsumption resolution 3507,71
  have eq3529 : (old c sk4 a) ∨ (old c c sk4) ∨ c = b ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq3508.imp_left (fun h : c = sk3 ↦ superpose h eq262)) -- superposition 262,3508, 3508 into 262, unify on (0).2 in 3508 and (0).1 in 262
  have eq3600 : (old c c sk4) ∨ c = b ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq3529 p4YZ -- subsumption resolution 3529,61
  have eq3601 : c = b ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq3600 p4YZ -- subsumption resolution 3600,61
  have eq3602 : c = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq3601 bc -- subsumption resolution 3601,57
  have eq3605 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq3602.imp_left (fun h : c = sk2 ↦ superpose h eq107)) -- superposition 107,3602, 3602 into 107, unify on (0).2 in 3602 and (0).3 in 107
  have eq3750 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 := resolve eq3605 p4XY -- subsumption resolution 3605,59
  have eq3751 : (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk1 := resolve eq3750 rule_def_1_0 -- subsumption resolution 3750,74
  have eq3752 : b = sk1 ∨ c = sk1 := resolve eq3751 rule_def_0_1 -- subsumption resolution 3751,71
  have eq4287 : sk1 = sk3 ∨ ¬(old sk3 sk3 sk4) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ c = sk2 := resolve eq1938 eq153 -- resolution 1938,153
  have eq4292 : sk1 = sk3 ∨ ¬(old sk3 sk3 sk4) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 := resolve eq4287 rfl -- duplicate literal removal 4287
  have eq4304 : ¬(old sk3 sk3 sk4) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 := resolve eq4292 preserve_4 -- subsumption resolution 4292,87
  have eq4305 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq4304 eq178 -- subsumption resolution 4304,178
  have eq4321 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := Or.assoc3 (eq4305.imp_left (fun h : c = sk4 ↦ superpose h eq170)) -- superposition 170,4305, 4305 into 170, unify on (0).2 in 4305 and (0).3 in 170
  have eq4322 : (old sk3 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := Or.assoc3 (eq4305.imp_left (fun h : c = sk4 ↦ superpose h eq179)) -- superposition 179,4305, 4305 into 179, unify on (0).2 in 4305 and (0).3 in 179
  have eq4473 : (old sk3 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq4322 rfl -- duplicate literal removal 4322
  have eq4474 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq4321 rfl -- duplicate literal removal 4321
  have eq4482 : c = sk3 ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq4474 p4XY -- subsumption resolution 4474,59
  have eq4483 : c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq4473 p4XY -- subsumption resolution 4473,59
  have eq4527 : (old c sk4 a) ∨ (old c c sk4) ∨ c = b ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq4482.imp_left (fun h : c = sk3 ↦ superpose h eq262)) -- superposition 262,4482, 4482 into 262, unify on (0).2 in 4482 and (0).1 in 262
  have eq4600 : (old c c sk4) ∨ c = b ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq4527 p4YZ -- subsumption resolution 4527,61
  have eq4601 : c = b ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := resolve eq4600 p4YZ -- subsumption resolution 4600,61
  have eq4602 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq4601 bc -- subsumption resolution 4601,57
  have eq4648 : (old c c b) ∨ (old sk0 sk3 c) ∨ b = sk3 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq4602.imp_left (fun h : c = sk2 ↦ superpose h eq209)) -- superposition 209,4602, 4602 into 209, unify on (0).2 in 4602 and (0).1 in 209
  have eq4766 : (old sk0 sk3 c) ∨ b = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq4648 p4YZ -- subsumption resolution 4648,61
  have eq4767 : b = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq4766 p4XY -- subsumption resolution 4766,59
  have eq5263 : b ≠ sk1 ∨ a = sk1 ∨ c = sk1 := eq4767.imp_left (fun h : b = sk3 ↦ superpose h preserve_4) -- superposition 87,4767, 4767 into 87, unify on (0).2 in 4767 and (0).2 in 87
  have eq5366 : c = sk1 ∨ a = sk1 := resolve eq5263 eq3752 -- subsumption resolution 5263,3752
  have eq5398 : (old c sk4 a) ∨ (old c c sk4) ∨ c = b ∨ a = sk1 := Or.assoc3 (eq5366.imp_left (fun h : c = sk1 ↦ superpose h eq240)) -- superposition 240,5366, 5366 into 240, unify on (0).2 in 5366 and (0).1 in 240
  have eq5438 : (old c c sk4) ∨ c = b ∨ a = sk1 := resolve eq5398 p4YZ -- subsumption resolution 5398,61
  have eq5439 : c = b ∨ a = sk1 := resolve eq5438 p4YZ -- subsumption resolution 5438,61
  have eq5440 : a = sk1 := resolve eq5439 bc -- subsumption resolution 5439,57
  have eq5443 : a ≠ sk3 := Eq.mp (by simp only [eq5440, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_4 -- backward demodulation 87,5440
  have eq5880 : a = c ∨ b = sk1 := Eq.mp (by simp only [eq5440, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3752 -- backward demodulation 3752,5440
  have eq5968 : a = c ∨ c = sk3 ∨ b = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq5440, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4483 -- backward demodulation 4483,5440
  have eq6522 : b = sk1 := resolve eq5880 ac -- subsumption resolution 5880,56
  have eq6523 : a = b := Eq.mp (by simp only [eq5440, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6522 -- forward demodulation 6522,5440
  have eq6536 : a = sk3 ∨ (old sk0 sk3 sk2) ∨ c = sk3 := Eq.mp (by simp only [eq6523, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq154 -- backward demodulation 154,6523
  have eq6749 : (old sk0 sk3 sk2) ∨ c = sk3 := resolve eq6536 eq5443 -- subsumption resolution 6536,5443
  have eq7015 : c = sk3 ∨ b = sk3 ∨ c = sk2 := resolve eq5968 ac -- subsumption resolution 5968,56
  have eq7016 : a = sk3 ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq6523, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7015 -- forward demodulation 7015,6523
  have eq7017 : c = sk3 ∨ c = sk2 := resolve eq7016 eq5443 -- subsumption resolution 7016,5443
  have eq7088 : (old c sk4 a) ∨ (old c c sk4) ∨ a = c ∨ c = sk2 := Or.assoc3 (eq7017.imp_left (fun h : c = sk3 ↦ superpose h eq263)) -- superposition 263,7017, 7017 into 263, unify on (0).2 in 7017 and (0).1 in 263
  have eq7123 : (old c c sk4) ∨ a = c ∨ c = sk2 := resolve eq7088 p4YZ -- subsumption resolution 7088,61
  have eq7124 : a = c ∨ c = sk2 := resolve eq7123 p4YZ -- subsumption resolution 7123,61
  have eq7125 : c = sk2 := resolve eq7124 ac -- subsumption resolution 7124,56
  have eq7183 : (old sk0 sk3 c) ∨ c = sk3 := Eq.mp (by simp only [eq7125, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6749 -- backward demodulation 6749,7125
  have eq7251 : c = sk3 := resolve eq7183 p4XY -- subsumption resolution 7183,59
  have eq7268 : (old c c sk4) ∨ (old sk3 sk4 a) ∨ c = sk4 := Eq.mp (by simp only [eq7251, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq261 -- backward demodulation 261,7251
  have eq7269 : (old c c sk4) ∨ (old sk3 sk4 a) ∨ a = sk3 := Eq.mp (by simp only [eq7251, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq263 -- backward demodulation 263,7251
  have eq7345 : (old sk3 sk4 a) ∨ c = sk4 := resolve eq7268 p4YZ -- subsumption resolution 7268,61
  have eq7346 : (old c sk4 a) ∨ c = sk4 := Eq.mp (by simp only [eq7251, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7345 -- forward demodulation 7345,7251
  have eq7347 : c = sk4 := resolve eq7346 p4YZ -- subsumption resolution 7346,61
  have eq7379 : (old sk3 sk4 a) ∨ a = sk3 := resolve eq7269 p4YZ -- subsumption resolution 7269,61
  have eq7380 : (old sk3 sk4 a) := resolve eq7379 eq5443 -- subsumption resolution 7379,5443
  have eq7381 : (old sk3 c a) := Eq.mp (by simp only [eq7347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7380 -- forward demodulation 7380,7347
  subsumption p4XZ eq7381 -- subsumption resolution 7381,60

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_5 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X1 X2 ∨ ¬ old X3 X2 X0 ∨ old X3 X1 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X2 ∨ ¬ new X3 X2 X0 ∨ new X3 X1 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq104 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 79,85
  have eq105 : (sP1 sk1 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ (sP0 sk1 sk1 sk2) := resolve new_imp preserve_1 -- resolution 79,86
  have eq106 : (sP1 sk3 sk2 sk0) ∨ (old sk3 sk2 sk0) ∨ (sP0 sk3 sk2 sk0) := resolve new_imp preserve_2 -- resolution 79,87
  have eq121 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk2 a) := resolve eq104 rule_def_1_1 -- resolution 104,76
  have eq122 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq104 rule_def_1_0 -- resolution 104,75
  have eq124 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq122 rule_def_0_2 -- resolution 122,73
  have eq126 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq122 rule_def_0_0 -- resolution 122,71
  have eq128 : (sP0 sk1 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ (old sk1 sk2 a) := resolve eq105 rule_def_1_1 -- resolution 105,76
  have eq129 : (sP0 sk1 sk1 sk2) ∨ (old sk1 sk1 sk2) ∨ c = sk1 := resolve eq105 rule_def_1_0 -- resolution 105,75
  have eq134 : (sP0 sk3 sk2 sk0) ∨ (old sk3 sk2 sk0) ∨ (old sk0 sk0 b) := resolve eq106 rule_def_1_2 -- resolution 106,77
  have eq136 : (sP0 sk3 sk2 sk0) ∨ (old sk3 sk2 sk0) ∨ c = sk2 := resolve eq106 rule_def_1_0 -- resolution 106,75
  have eq145 : (old sk1 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq129 rule_def_0_2 -- resolution 129,73
  have eq146 : (old sk1 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq129 rule_def_0_1 -- resolution 129,72
  have eq147 : (old sk1 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq129 rule_def_0_0 -- resolution 129,71
  have eq165 : (old sk3 sk2 sk0) ∨ c = sk2 ∨ c = sk0 := resolve eq136 rule_def_0_2 -- resolution 136,73
  have eq176 (X0 : G) : ¬(old sk0 X0 sk2) ∨ c = sk0 ∨ (old sk3 X0 sk2) ∨ ¬(old X0 X0 sk2) ∨ c = sk2 := resolve eq165 old_5 -- resolution 165,68
  have eq189 : (old sk0 sk2 a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq121 rule_def_0_0 -- resolution 121,71
  have eq206 : (old sk1 sk2 a) ∨ (old sk1 sk1 sk2) ∨ b = sk1 := resolve eq128 rule_def_0_1 -- resolution 128,72
  have eq216 : (old sk3 sk2 sk0) ∨ (old sk0 sk0 b) ∨ c = sk0 := resolve eq134 rule_def_0_2 -- resolution 134,73
  have eq856 : c = sk0 ∨ (old sk3 sk1 sk2) ∨ ¬(old sk1 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq176 eq124 -- resolution 176,124
  have eq857 : c = sk0 ∨ (old sk3 sk1 sk2) ∨ ¬(old sk1 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq856 rfl -- duplicate literal removal 856
  have eq860 : (old sk3 sk1 sk2) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq857 eq145 -- subsumption resolution 857,145
  have eq864 : c = sk0 ∨ c = sk2 ∨ c = sk1 ∨ (new sk3 sk1 sk2) := resolve eq860 imp_new_0 -- resolution 860,69
  have eq865 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq864 preserve_3 -- subsumption resolution 864,88
  have eq885 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq865.imp_left (fun h : c = sk2 ↦ superpose h eq126)) -- superposition 126,865, 865 into 126, unify on (0).2 in 865 and (0).3 in 126
  have eq894 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq865.imp_left (fun h : c = sk2 ↦ superpose h eq147)) -- superposition 147,865, 865 into 147, unify on (0).2 in 865 and (0).3 in 147
  have eq968 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq894 rfl -- duplicate literal removal 894
  have eq973 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq885 rfl -- duplicate literal removal 885
  have eq983 : c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq973 p4XY -- subsumption resolution 973,60
  have eq988 : c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq968 p4XY -- subsumption resolution 968,60
  have eq1081 : (old c sk2 a) ∨ (old c c sk2) ∨ c = b ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq983.imp_left (fun h : c = sk1 ↦ superpose h eq206)) -- superposition 206,983, 983 into 206, unify on (0).2 in 983 and (0).1 in 206
  have eq1109 : (old c c sk2) ∨ c = b ∨ a = sk0 ∨ c = sk0 := resolve eq1081 p4YZ -- subsumption resolution 1081,62
  have eq1110 : c = b ∨ a = sk0 ∨ c = sk0 := resolve eq1109 p4YZ -- subsumption resolution 1109,62
  have eq1111 : c = sk0 ∨ a = sk0 := resolve eq1110 bc -- subsumption resolution 1110,58
  have eq1142 : (old c sk2 a) ∨ (old c sk1 sk2) ∨ a = c ∨ a = sk0 := Or.assoc3 (eq1111.imp_left (fun h : c = sk0 ↦ superpose h eq189)) -- superposition 189,1111, 1111 into 189, unify on (0).2 in 1111 and (0).1 in 189
  have eq1180 : (old c sk1 sk2) ∨ a = c ∨ a = sk0 := resolve eq1142 p4YZ -- subsumption resolution 1142,62
  have eq1181 : a = c ∨ a = sk0 := resolve eq1180 p4YZ -- subsumption resolution 1180,62
  have eq1182 : a = sk0 := resolve eq1181 ac -- subsumption resolution 1181,57
  have eq1242 : (old sk3 sk2 a) ∨ (old sk0 sk0 b) ∨ c = sk0 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq216 -- backward demodulation 216,1182
  have eq1336 : a = c ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq865 -- backward demodulation 865,1182
  have eq1352 : a = c ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq988 -- backward demodulation 988,1182
  have eq1405 : (old a a b) ∨ (old sk3 sk2 a) ∨ c = sk0 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1242 -- forward demodulation 1242,1182
  have eq1406 : a = c ∨ (old a a b) ∨ (old sk3 sk2 a) := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1405 -- forward demodulation 1405,1182
  have eq1407 : (old a a b) ∨ (old sk3 sk2 a) := resolve eq1406 ac -- subsumption resolution 1406,57
  have eq1472 : c = sk2 ∨ c = sk1 := resolve eq1336 ac -- subsumption resolution 1336,57
  have eq1497 : c = sk1 ∨ a = sk1 := resolve eq1352 ac -- subsumption resolution 1352,57
  have eq1651 : (old c sk2 a) ∨ (old c c sk2) ∨ c = b ∨ a = sk1 := Or.assoc3 (eq1497.imp_left (fun h : c = sk1 ↦ superpose h eq206)) -- superposition 206,1497, 1497 into 206, unify on (0).2 in 1497 and (0).1 in 206
  have eq1677 : (old c c sk2) ∨ c = b ∨ a = sk1 := resolve eq1651 p4YZ -- subsumption resolution 1651,62
  have eq1678 : c = b ∨ a = sk1 := resolve eq1677 p4YZ -- subsumption resolution 1677,62
  have eq1679 : a = sk1 := resolve eq1678 bc -- subsumption resolution 1678,58
  have eq1692 : (old a a sk2) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq1679, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq146 -- backward demodulation 146,1679
  have eq1872 : a = c ∨ c = sk2 := Eq.mp (by simp only [eq1679, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1472 -- backward demodulation 1472,1679
  have eq1929 : a = c ∨ (old a a sk2) ∨ b = sk1 := Eq.mp (by simp only [eq1679, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1692 -- forward demodulation 1692,1679
  have eq1930 : (old a a sk2) ∨ b = sk1 := resolve eq1929 ac -- subsumption resolution 1929,57
  have eq1931 : a = b ∨ (old a a sk2) := Eq.mp (by simp only [eq1679, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1930 -- forward demodulation 1930,1679
  have eq2085 : c = sk2 := resolve eq1872 ac -- subsumption resolution 1872,57
  have eq2092 : (old sk3 c a) ∨ (old a a b) := Eq.mp (by simp only [eq2085, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1407 -- backward demodulation 1407,2085
  have eq2111 : (old a a c) ∨ a = b := Eq.mp (by simp only [eq2085, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1931 -- backward demodulation 1931,2085
  have eq2127 : (old a a b) := resolve eq2092 p4XZ -- subsumption resolution 2092,61
  have eq2142 : a = b := resolve eq2111 p4XY -- subsumption resolution 2111,60
  have eq2144 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq2142, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 59,2142
  have eq2154 : (old a a a) := Eq.mp (by simp only [eq2142, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2127 -- backward demodulation 2127,2142
  subsumption eq2144 eq2154 -- subsumption resolution 2154,2144

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (bc : c ≠ b) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old X Z a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq89 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq97 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk2 a) := resolve eq89 rule_def_1_1 -- resolution 89,73
  have eq98 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq89 rule_def_1_0 -- resolution 89,72
  have eq104 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq98 rule_def_0_0 -- resolution 98,68
  have eq105 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq104 preserve_1 -- subsumption resolution 104,81
  have eq110 : c = sk1 ∨ memold sk0 := resolve eq105 old_mem1 -- resolution 105,77
  have eq113 : c = sk1 := resolve eq110 preserve_3 -- subsumption resolution 110,83
  have eq117 : (sP0 sk0 c sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk2 a) := Eq.mp (by simp only [eq113, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq97 -- backward demodulation 97,113
  have eq127 : (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 sk2 a) := Eq.mp (by simp only [eq113, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq117 -- forward demodulation 117,113
  have eq128 : (sP0 sk0 c sk2) ∨ (old sk0 sk2 a) := resolve eq127 p4XZ -- subsumption resolution 127,58
  have eq138 : (old sk0 sk2 a) ∨ c = b := resolve eq128 rule_def_0_1 -- resolution 128,69
  have eq140 : (old sk0 sk2 a) := resolve eq138 bc -- subsumption resolution 138,55
  have eq156 : memold sk0 := resolve eq140 old_mem1 -- resolution 140,77
  subsumption preserve_3 eq156 -- subsumption resolution 156,83

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq89 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq98 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq89 rule_def_1_0 -- resolution 89,72
  have eq99 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq98 preserve_4 -- subsumption resolution 98,84
  have eq104 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq99 rule_def_0_1 -- resolution 99,69
  have eq106 : (old sk0 sk1 sk2) := resolve eq104 preserve_2 -- subsumption resolution 104,82
  have eq112 : memold sk1 := resolve eq106 old_mem2 -- resolution 106,78
  subsumption preserve_3 eq112 -- subsumption resolution 112,83

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z Z b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq89 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq96 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk2 sk2 b) := resolve eq89 rule_def_1_2 -- resolution 89,74
  have eq98 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq89 rule_def_1_0 -- resolution 89,72
  have eq102 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq98 rule_def_0_2 -- resolution 98,70
  have eq105 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq102 preserve_4 -- subsumption resolution 102,84
  have eq112 : c = sk1 ∨ memold sk2 := resolve eq105 old_mem3 -- resolution 105,79
  have eq113 : c = sk1 := resolve eq112 preserve_3 -- subsumption resolution 112,83
  have eq116 : (sP0 sk0 c sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 sk2 b) := Eq.mp (by simp only [eq113, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq96 -- backward demodulation 96,113
  have eq123 : (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk2 sk2 b) := Eq.mp (by simp only [eq113, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq116 -- forward demodulation 116,113
  have eq124 : (sP0 sk0 c sk2) ∨ (old sk2 sk2 b) := resolve eq123 p4XZ -- subsumption resolution 123,58
  have eq131 : (old sk2 sk2 b) ∨ c = sk2 := resolve eq124 rule_def_0_2 -- resolution 124,70
  have eq134 : (old sk2 sk2 b) := resolve eq131 preserve_4 -- subsumption resolution 131,84
  have eq143 : memold sk2 := resolve eq134 old_mem1 -- resolution 134,77
  subsumption preserve_3 eq143 -- subsumption resolution 143,83

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X3 ∨ ¬ R X2 X3 X4 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X1 X0 ∨ ¬ R X2 X2 X1 ∨ X0 = X2)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X0 X1 ∨ ¬ R X2 X2 X1 ∨ X2 = X0)
  rule_4 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X2 ∨ ¬ R X1 X1 X4 ∨ ¬ R X3 X3 X4 ∨ X1 = X3)
  rule_5 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X2 ∨ ¬ R X3 X2 X0 ∨ R X3 X1 X2)
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
  let sP1 (X Y Z) := c = Y ∧ ps.R X Z a ∧ ps.R Z Z b
  have hsP1 (X Y Z) (h : sP1 X Y Z) : c = Y ∧ ps.R X Z a ∧ ps.R Z Z b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sP1 bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sP1 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sP1 ac bc p4XY p4YZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sP1 ac bc p4XY p4YZ ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sP1 ac bc p4XY p4XZ p4YZ ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sP1 ac bc p3 p4XY p4XZ p4YZ ps.rule_5 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) bc p4XZ rule_def_0_0 rule_def_0_1 rule_def_1_0 rule_def_1_1 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_0 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) p4XZ rule_def_0_2 rule_def_1_0 rule_def_1_2 new_imp ps.mem_1 ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X1 X3 ∨ ¬ ps.compl X2 X3 X4 ∨ ps.compl X0 X4 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X1) (max (Nat.pair X2 X3) (max (Nat.pair X0 X4) 0)))
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

theorem PartialSolution.toMagma_equation906 :
    letI := ps.toMagma
    Equation906 ℕ := by
  simp only [Equation906, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun X0 X0) (ps.complFun (ps.complFun X1 X0) (ps.complFun X0 X0))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3862 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation906_not_implies_Equation3862 : ∃ (G : Type) (_ : Magma G), Equation906 G ∧ ¬Equation3862 G := by
  use ℕ, PartialSolution.counter3862.toMagma, PartialSolution.counter3862.toMagma_equation906
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3862.of_R 1 1 2] | rw [PartialSolution.counter3862.of_R 1 2 2] | rw [PartialSolution.counter3862.of_R 2 1 3])
  all_goals simp [PartialSolution.counter3862]

end Eq906