import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq883

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old Z X a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq73 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 65,66
  have eq74 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 65,67
  have eq82 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 sk0 a) := resolve eq73 rule_def_1_1 -- resolution 73,62
  have eq83 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq73 rule_def_1_0 -- resolution 73,61
  have eq88 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (old sk3 sk0 a) := resolve eq74 rule_def_1_1 -- resolution 74,62
  have eq89 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq74 rule_def_1_0 -- resolution 74,61
  have eq93 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq83 rule_def_0_2 -- resolution 83,59
  have eq94 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq83 rule_def_0_1 -- resolution 83,58
  have eq99 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq93 old_0 -- resolution 93,50
  have eq101 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq89 rule_def_0_2 -- resolution 89,59
  have eq102 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq89 rule_def_0_1 -- resolution 89,58
  have eq103 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq89 rule_def_0_0 -- resolution 89,57
  have eq107 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ c = sk1 := resolve eq94 old_0 -- resolution 94,50
  have eq117 : (old sk2 sk0 a) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq82 rule_def_0_2 -- resolution 82,59
  have eq118 : (old sk2 sk0 a) ∨ (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq82 rule_def_0_1 -- resolution 82,58
  have eq119 : (old sk2 sk0 a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq82 rule_def_0_0 -- resolution 82,57
  have eq134 : (old sk3 sk0 a) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := resolve eq88 rule_def_0_1 -- resolution 88,58
  have eq159 (X0 : G) : ¬(old X0 sk0 a) ∨ c = sk2 ∨ sk2 = X0 ∨ (old sk0 sk1 sk2) := resolve eq117 old_2 -- resolution 117,52
  have eq173 (X0 : G) : ¬(old X0 sk0 a) ∨ a = sk0 ∨ sk2 = X0 ∨ (old sk0 sk1 sk2) := resolve eq119 old_2 -- resolution 119,52
  have eq257 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq99 eq103 -- resolution 99,103
  have eq262 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq257 rfl -- duplicate literal removal 257
  have eq270 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq262 preserve_2 -- subsumption resolution 262,68
  have eq274 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := Or.assoc3 (eq270.imp_left (fun h : c = sk2 ↦ superpose h eq73)) -- superposition 73,270, 270 into 73, unify on (0).2 in 270 and (0).3 in 73
  have eq295 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq274 p4XY -- subsumption resolution 274,47
  have eq296 : (sP1 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq295 rule_def_0_0 -- subsumption resolution 295,57
  have eq297 : c = sk1 ∨ a = sk0 := resolve eq296 rule_def_1_0 -- subsumption resolution 296,61
  have eq317 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (old sk3 sk0 a) ∨ a = sk0 := Or.assoc3 (eq297.imp_left (fun h : c = sk1 ↦ superpose h eq88)) -- superposition 88,297, 297 into 88, unify on (0).2 in 297 and (0).2 in 88
  have eq334 : (sP0 sk0 c sk3) ∨ (old sk3 sk0 a) ∨ a = sk0 := resolve eq317 p4XZ -- subsumption resolution 317,48
  have eq335 : (old sk3 sk0 a) ∨ a = sk0 := resolve eq334 rule_def_0_0 -- subsumption resolution 334,57
  have eq346 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq107 eq102 -- resolution 107,102
  have eq349 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq346 rfl -- duplicate literal removal 346
  have eq357 : b = sk1 ∨ c = sk1 := resolve eq349 preserve_2 -- subsumption resolution 349,68
  have eq368 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq357.imp_left (fun h : b = sk1 ↦ superpose h eq93)) -- superposition 93,357, 357 into 93, unify on (0).2 in 357 and (0).2 in 93
  have eq372 : (old sk0 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq357.imp_left (fun h : b = sk1 ↦ superpose h eq101)) -- superposition 101,357, 357 into 101, unify on (0).2 in 357 and (0).2 in 101
  have eq382 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq368 bc -- subsumption resolution 368,45
  have eq385 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq372 bc -- subsumption resolution 372,45
  have eq780 : c = sk2 ∨ sk2 = sk3 ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := resolve eq159 eq134 -- resolution 159,134
  have eq786 : c = sk2 ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := resolve eq780 preserve_2 -- subsumption resolution 780,68
  have eq840 : a = sk0 ∨ sk2 = sk3 ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq173 eq335 -- resolution 173,335
  have eq845 : a = sk0 ∨ sk2 = sk3 ∨ (old sk0 sk1 sk2) := resolve eq840 rfl -- duplicate literal removal 840
  have eq850 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq845 preserve_2 -- subsumption resolution 845,68
  have eq872 : (old sk0 c sk2) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq297.imp_left (fun h : c = sk1 ↦ superpose h eq850)) -- superposition 850,297, 297 into 850, unify on (0).2 in 297 and (0).2 in 850
  have eq876 : (old sk0 c sk2) ∨ a = sk0 := resolve eq872 rfl -- duplicate literal removal 872
  have eq882 : a = sk0 := resolve eq876 p4XZ -- subsumption resolution 876,48
  have eq911 : (old a sk1 sk2) ∨ (old sk2 sk0 a) ∨ b = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq118 -- backward demodulation 118,882
  have eq1010 : (old a b sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq382 -- backward demodulation 382,882
  have eq1013 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq385 -- backward demodulation 385,882
  have eq1043 : (old a sk1 sk2) ∨ c = sk2 ∨ (old sk0 sk1 sk3) ∨ b = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq786 -- backward demodulation 786,882
  have eq1068 : (old sk2 a a) ∨ (old a sk1 sk2) ∨ b = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq911 -- forward demodulation 911,882
  have eq1145 : c = sk2 ∨ c = sk1 := resolve eq1010 p3 -- subsumption resolution 1010,46
  have eq1146 : c = sk3 ∨ c = sk1 := resolve eq1013 p3 -- subsumption resolution 1013,46
  have eq1162 : (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ c = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq882, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1043 -- forward demodulation 1043,882
  have eq1180 : c ≠ sk2 ∨ c = sk1 := eq1146.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 68,1146, 1146 into 68, unify on (0).2 in 1146 and (0).2 in 68
  have eq1182 : c = sk1 := resolve eq1180 eq1145 -- subsumption resolution 1180,1145
  have eq1200 : c = b ∨ (old sk2 a a) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1068 -- backward demodulation 1068,1182
  have eq1257 : c = b ∨ (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1162 -- backward demodulation 1162,1182
  have eq1277 : (old sk2 a a) ∨ (old a sk1 sk2) := resolve eq1200 bc -- subsumption resolution 1200,45
  have eq1278 : (old a c sk2) ∨ (old sk2 a a) := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1277 -- forward demodulation 1277,1182
  have eq1279 : (old sk2 a a) := resolve eq1278 p4XZ -- subsumption resolution 1278,48
  have eq1334 : (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ c = sk2 := resolve eq1257 bc -- subsumption resolution 1257,45
  have eq1335 : (old a c sk3) ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1334 -- forward demodulation 1334,1182
  have eq1336 : (old a sk1 sk2) ∨ c = sk2 := resolve eq1335 p4XZ -- subsumption resolution 1335,48
  have eq1337 : (old a c sk2) ∨ c = sk2 := Eq.mp (by simp only [eq1182, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1336 -- forward demodulation 1336,1182
  have eq1338 : c = sk2 := resolve eq1337 p4XZ -- subsumption resolution 1337,48
  have eq1343 : (old c a a) := Eq.mp (by simp only [eq1338, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1279 -- backward demodulation 1279,1338
  subsumption p4YZ eq1343 -- subsumption resolution 1343,49

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X1 X3 ∨ ¬ old X2 X3 X4 ∨ old X1 X4 X0)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X1 X0 ∨ old X1 X0 X2)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, c ≠ Y ∨ ¬ old Z X a ∨ ¬ old X X b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X3 ∨ ¬ new X2 X3 X4 ∨ new X1 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq74 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 59
  have eq75 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq74 rfl -- equality resolution 74
  have eq76 : (new a b c) := resolve eq75 rfl -- equality resolution 75
  have eq77 (X0 X2 : G) : ¬(old X2 X0 a) ∨ ¬(old X0 X0 b) ∨ (new X0 c X2) := resolve imp_new_2 rfl -- equality resolution 63
  have eq79 (X0 : G) : ¬(new sk1 sk1 X0) ∨ sk3 = X0 := resolve prev_0 preserve_1 -- resolution 69,71
  have eq80 (X0 : G) : ¬(new sk2 sk3 X0) ∨ sk4 = X0 := resolve prev_0 preserve_2 -- resolution 69,72
  have eq85 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 68,70
  have eq86 : (sP1 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ (sP0 sk1 sk1 sk3) := resolve new_imp preserve_1 -- resolution 68,71
  have eq87 : (sP1 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ (sP0 sk2 sk3 sk4) := resolve new_imp preserve_2 -- resolution 68,72
  have eq97 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq85 rule_def_1_0 -- resolution 85,64
  have eq101 : (sP0 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ (old sk1 sk1 b) := resolve eq86 rule_def_1_2 -- resolution 86,66
  have eq103 : (sP0 sk1 sk1 sk3) ∨ (old sk1 sk1 sk3) ∨ c = sk1 := resolve eq86 rule_def_1_0 -- resolution 86,64
  have eq107 : (sP0 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ (old sk2 sk2 b) := resolve eq87 rule_def_1_2 -- resolution 87,66
  have eq109 : (sP0 sk2 sk3 sk4) ∨ (old sk2 sk3 sk4) ∨ c = sk3 := resolve eq87 rule_def_1_0 -- resolution 87,64
  have eq110 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq97 rule_def_0_2 -- resolution 97,62
  have eq111 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq97 rule_def_0_1 -- resolution 97,61
  have eq113 : (old sk1 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq103 rule_def_0_2 -- resolution 103,62
  have eq115 : (old sk1 sk1 sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq103 rule_def_0_0 -- resolution 103,60
  have eq117 : ¬(old sk2 sk2 sk1) ∨ c = sk2 ∨ (old sk1 sk2 sk0) ∨ c = sk1 := resolve eq110 old_3 -- resolution 110,56
  have eq121 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq109 rule_def_0_2 -- resolution 109,62
  have eq122 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq109 rule_def_0_1 -- resolution 109,61
  have eq123 : (old sk2 sk3 sk4) ∨ c = sk3 ∨ a = sk2 := resolve eq109 rule_def_0_0 -- resolution 109,60
  have eq147 : (old sk1 sk1 sk3) ∨ (old sk1 sk1 b) ∨ b = sk1 := resolve eq101 rule_def_0_1 -- resolution 101,61
  have eq165 : (old sk2 sk3 sk4) ∨ (old sk2 sk2 b) ∨ b = sk3 := resolve eq107 rule_def_0_1 -- resolution 107,61
  have eq166 : (old sk2 sk3 sk4) ∨ (old sk2 sk2 b) ∨ a = sk2 := resolve eq107 rule_def_0_0 -- resolution 107,60
  have eq167 (X0 X1 : G) : ¬(old X1 X0 sk2) ∨ c = sk4 ∨ (old X0 sk4 X1) ∨ ¬(old X0 X0 sk3) ∨ c = sk3 := resolve eq121 old_1 -- resolution 121,54
  have eq954 : c = sk4 ∨ (old sk1 sk4 sk0) ∨ ¬(old sk1 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq167 eq111 -- resolution 167,111
  have eq955 : c = sk4 ∨ (old sk1 sk4 sk0) ∨ ¬(old sk1 sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq167 eq110 -- resolution 167,110
  have eq957 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq954 eq113 -- subsumption resolution 954,113
  have eq958 : (old sk1 sk4 sk0) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq955 eq113 -- subsumption resolution 955,113
  have eq1840 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 ∨ (new sk1 sk4 sk0) := resolve eq957 imp_new_0 -- resolution 957,58
  have eq1845 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq1840 preserve_3 -- subsumption resolution 1840,73
  have eq1847 : ¬(new sk1 c sk0) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := eq1845.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 73,1845, 1845 into 73, unify on (0).2 in 1845 and (0).2 in 73
  have eq1852 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq1845.imp_left (fun h : c = sk4 ↦ superpose h eq122)) -- superposition 122,1845, 1845 into 122, unify on (0).2 in 1845 and (0).3 in 122
  have eq1853 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq1845.imp_left (fun h : c = sk4 ↦ superpose h eq123)) -- superposition 123,1845, 1845 into 123, unify on (0).2 in 1845 and (0).3 in 123
  have eq1894 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq1853 rfl -- duplicate literal removal 1853
  have eq1895 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq1852 rfl -- duplicate literal removal 1852
  have eq1899 : b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq1895 p4XY -- subsumption resolution 1895,50
  have eq1900 : c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq1894 p4XY -- subsumption resolution 1894,50
  have eq1911 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk4 sk0) := resolve eq958 imp_new_0 -- resolution 958,58
  have eq1916 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1911 preserve_3 -- subsumption resolution 1911,73
  have eq1917 : (new sk2 sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := eq1916.imp_left (fun h : c = sk4 ↦ superpose h preserve_2) -- superposition 72,1916, 1916 into 72, unify on (0).2 in 1916 and (0).3 in 72
  have eq1924 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1916.imp_left (fun h : c = sk4 ↦ superpose h eq123)) -- superposition 123,1916, 1916 into 123, unify on (0).2 in 1916 and (0).3 in 123
  have eq1965 : (old sk2 sk3 c) ∨ c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq1924 rfl -- duplicate literal removal 1924
  have eq1971 : c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq1965 p4XY -- subsumption resolution 1965,50
  have eq1996 : (sP1 sk1 sk1 b) ∨ (old sk1 sk1 b) ∨ (sP0 sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq1899.imp_left (fun h : b = sk3 ↦ superpose h eq86)) -- superposition 86,1899, 1899 into 86, unify on (0).2 in 1899 and (0).3 in 86
  have eq2093 : (sP1 sk1 sk1 b) ∨ (old sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq1996 rule_def_0_1 -- subsumption resolution 1996,61
  have eq2094 : (old sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq2093 rule_def_1_0 -- subsumption resolution 2093,64
  have eq2125 : (sP1 sk1 sk1 c) ∨ (old sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq1900.imp_left (fun h : c = sk3 ↦ superpose h eq86)) -- superposition 86,1900, 1900 into 86, unify on (0).2 in 1900 and (0).3 in 86
  have eq2197 : (sP1 sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq2125 p4XY -- subsumption resolution 2125,50
  have eq2198 : (sP1 sk1 sk1 c) ∨ a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq2197 rule_def_0_1 -- subsumption resolution 2197,61
  have eq2199 : a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq2198 rule_def_1_0 -- subsumption resolution 2198,64
  have eq2224 : (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP0 sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq2199.imp_left (fun h : a = sk2 ↦ superpose h eq85)) -- superposition 85,2199, 2199 into 85, unify on (0).2 in 2199 and (0).3 in 85
  have eq2331 : (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq2224 rule_def_0_1 -- subsumption resolution 2224,61
  have eq2332 : (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq2331 rule_def_1_0 -- subsumption resolution 2331,64
  have eq2432 : ¬(old sk1 sk1 b) ∨ b = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) := resolve eq2332 eq77 -- resolution 2332,77
  have eq2585 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1971.imp_left (fun h : c = sk3 ↦ superpose h eq115)) -- superposition 115,1971, 1971 into 115, unify on (0).2 in 1971 and (0).3 in 115
  have eq2636 : (old sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk2 ∨ c = sk2 := resolve eq2585 rfl -- duplicate literal removal 2585
  have eq2650 : c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq2636 p4XY -- subsumption resolution 2636,50
  have eq2683 : (old c sk3 sk4) ∨ (old c c b) ∨ a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := Or.assoc3 (eq2650.imp_left (fun h : c = sk2 ↦ superpose h eq166)) -- superposition 166,2650, 2650 into 166, unify on (0).2 in 2650 and (0).1 in 166
  have eq2790 : (old c c b) ∨ a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq2683 p4YZ -- subsumption resolution 2683,52
  have eq2791 : a = c ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq2790 p4YZ -- subsumption resolution 2790,52
  have eq2792 : a = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq2791 ac -- subsumption resolution 2791,47
  have eq2814 (X0 : G) : ¬(new a sk3 X0) ∨ sk4 = X0 ∨ a = sk1 ∨ c = sk1 := Or.assoc2 (eq2792.imp_left (fun h : a = sk2 ↦ superpose h eq80)) -- superposition 80,2792, 2792 into 80, unify on (0).2 in 2792 and (0).1 in 80
  have eq2823 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq2792.imp_left (fun h : a = sk2 ↦ superpose h eq110)) -- superposition 110,2792, 2792 into 110, unify on (0).2 in 2792 and (0).3 in 110
  have eq2916 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c ∨ a = sk1 := resolve eq2823 rfl -- duplicate literal removal 2823
  have eq2920 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = sk1 := resolve eq2916 ac -- subsumption resolution 2916,47
  have eq3020 : ¬(old sk1 sk1 b) ∨ a = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) := resolve eq2920 eq77 -- resolution 2920,77
  have eq3470 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq2792.imp_left (fun h : a = sk2 ↦ superpose h eq1917)) -- superposition 1917,2792, 2792 into 1917, unify on (0).2 in 2792 and (0).1 in 1917
  have eq3485 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = c ∨ a = sk1 := resolve eq3470 rfl -- duplicate literal removal 3470
  have eq3486 : (new a sk3 c) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq3485 ac -- subsumption resolution 3485,47
  have eq4650 : c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk4 ∨ a = sk1 ∨ c = sk1 := resolve eq3486 eq2814 -- resolution 3486,2814
  have eq4663 : c = sk4 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := resolve eq4650 rfl -- duplicate literal removal 4650
  have eq4683 : ¬(new sk1 c sk0) ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := eq4663.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 73,4663, 4663 into 73, unify on (0).2 in 4663 and (0).2 in 73
  have eq4688 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := Or.assoc3 (eq4663.imp_left (fun h : c = sk4 ↦ superpose h eq122)) -- superposition 122,4663, 4663 into 122, unify on (0).2 in 4663 and (0).3 in 122
  have eq4769 : (old sk2 sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq4688 rfl -- duplicate literal removal 4688
  have eq4773 : b = sk3 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq4769 p4XY -- subsumption resolution 4769,50
  have eq4795 : (sP1 sk1 sk1 b) ∨ (old sk1 sk1 b) ∨ (sP0 sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq4773.imp_left (fun h : b = sk3 ↦ superpose h eq86)) -- superposition 86,4773, 4773 into 86, unify on (0).2 in 4773 and (0).3 in 86
  have eq4942 : (sP1 sk1 sk1 b) ∨ (old sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq4795 rule_def_0_0 -- subsumption resolution 4795,60
  have eq4943 : (old sk1 sk1 b) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq4942 rule_def_1_0 -- subsumption resolution 4942,64
  have eq5304 : b = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq2432 eq2094 -- resolution 2432,2094
  have eq5307 : b = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) ∨ c = sk3 := resolve eq5304 rfl -- duplicate literal removal 5304
  have eq5312 : c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq5307 eq1847 -- subsumption resolution 5307,1847
  have eq5333 : (sP1 sk1 sk1 c) ∨ (old sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq5312.imp_left (fun h : c = sk3 ↦ superpose h eq86)) -- superposition 86,5312, 5312 into 86, unify on (0).2 in 5312 and (0).3 in 86
  have eq5440 : (sP1 sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq5333 p4XY -- subsumption resolution 5333,50
  have eq5441 : (sP1 sk1 sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq5440 rule_def_0_1 -- subsumption resolution 5440,61
  have eq5442 : b = sk1 ∨ c = sk1 := resolve eq5441 rule_def_1_0 -- subsumption resolution 5441,64
  have eq10741 : a = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq3020 eq4943 -- resolution 3020,4943
  have eq10754 : a = sk1 ∨ c = sk1 ∨ (new sk1 c sk0) ∨ c = sk3 := resolve eq10741 rfl -- duplicate literal removal 10741
  have eq10760 : c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq10754 eq4683 -- subsumption resolution 10754,4683
  have eq10841 : (sP1 sk1 sk1 c) ∨ (old sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq10760.imp_left (fun h : c = sk3 ↦ superpose h eq86)) -- superposition 86,10760, 10760 into 86, unify on (0).2 in 10760 and (0).3 in 86
  have eq10958 : (sP1 sk1 sk1 c) ∨ (sP0 sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq10841 p4XY -- subsumption resolution 10841,50
  have eq10959 : (sP1 sk1 sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq10958 rule_def_0_0 -- subsumption resolution 10958,60
  have eq10960 : c = sk1 ∨ a = sk1 := resolve eq10959 rule_def_1_0 -- subsumption resolution 10959,64
  have eq11048 : (old c c sk3) ∨ (old c c b) ∨ c = b ∨ a = sk1 := Or.assoc3 (eq10960.imp_left (fun h : c = sk1 ↦ superpose h eq147)) -- superposition 147,10960, 10960 into 147, unify on (0).2 in 10960 and (0).1 in 147
  have eq11167 : (old c c b) ∨ c = b ∨ a = sk1 := resolve eq11048 p4YZ -- subsumption resolution 11048,52
  have eq11168 : c = b ∨ a = sk1 := resolve eq11167 p4YZ -- subsumption resolution 11167,52
  have eq11169 : a = sk1 := resolve eq11168 bc -- subsumption resolution 11168,48
  have eq11172 : ¬(new a sk4 sk0) := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 73,11169
  have eq11174 : ∀ (X0 : G) , ¬(new a a X0) ∨ sk3 = X0 := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq79 -- backward demodulation 79,11169
  have eq11190 : a = c ∨ ¬(old sk2 sk2 sk1) ∨ c = sk2 ∨ (old sk1 sk2 sk0) := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq117 -- backward demodulation 117,11169
  have eq11847 : a = c ∨ b = sk1 := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5442 -- backward demodulation 5442,11169
  have eq12271 : ¬(old sk2 sk2 sk1) ∨ c = sk2 ∨ (old sk1 sk2 sk0) := resolve eq11190 ac -- subsumption resolution 11190,47
  have eq12272 : ¬(old sk2 sk2 a) ∨ c = sk2 ∨ (old sk1 sk2 sk0) := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12271 -- forward demodulation 12271,11169
  have eq12273 : ¬(old sk2 sk2 a) ∨ (old a sk2 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12272 -- forward demodulation 12272,11169
  have eq13070 : b = sk1 := resolve eq11847 ac -- subsumption resolution 11847,47
  have eq13071 : a = b := Eq.mp (by simp only [eq11169, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13070 -- forward demodulation 13070,11169
  have eq13076 : (new a a c) := Eq.mp (by simp only [eq13071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq76 -- backward demodulation 76,13071
  have eq13077 : ∀ (X0 X2 : G) , ¬(old X2 X0 a) ∨ ¬(old X0 X0 a) ∨ (new X0 c X2) := Eq.mp (by simp only [eq13071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq77 -- backward demodulation 77,13071
  have eq13085 : (old sk2 sk2 a) ∨ (old sk2 sk3 sk4) ∨ b = sk3 := Eq.mp (by simp only [eq13071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq165 -- backward demodulation 165,13071
  have eq13086 : (old sk2 sk2 a) ∨ (old sk2 sk3 sk4) ∨ a = sk2 := Eq.mp (by simp only [eq13071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq166 -- backward demodulation 166,13071
  have eq13274 : a = sk3 ∨ (old sk2 sk2 a) ∨ (old sk2 sk3 sk4) := Eq.mp (by simp only [eq13071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13085 -- forward demodulation 13085,13071
  have eq13603 : c = sk3 := resolve eq11174 eq13076 -- resolution 11174,13076
  have eq13605 : ∀ (X0 : G) , ¬(new sk2 c X0) ∨ sk4 = X0 := Eq.mp (by simp only [eq13603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq80 -- backward demodulation 80,13603
  have eq13642 : (old sk2 c sk4) ∨ (old sk2 sk2 a) ∨ a = sk2 := Eq.mp (by simp only [eq13603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13086 -- backward demodulation 13086,13603
  have eq13660 : (old sk2 c sk4) ∨ a = sk3 ∨ (old sk2 sk2 a) := Eq.mp (by simp only [eq13603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13274 -- backward demodulation 13274,13603
  have eq13688 : (old sk2 sk2 a) ∨ a = sk2 := resolve eq13642 p4XZ -- subsumption resolution 13642,51
  have eq13707 : a = sk3 ∨ (old sk2 sk2 a) := resolve eq13660 p4XZ -- subsumption resolution 13660,51
  have eq13708 : a = c ∨ (old sk2 sk2 a) := Eq.mp (by simp only [eq13603, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13707 -- forward demodulation 13707,13603
  have eq13709 : (old sk2 sk2 a) := resolve eq13708 ac -- subsumption resolution 13708,47
  have eq13720 : ¬(old sk2 sk2 a) ∨ (new sk2 c sk2) := resolve eq13709 eq13077 -- resolution 13709,13077
  have eq13726 : (new sk2 c sk2) := resolve eq13720 eq13709 -- subsumption resolution 13720,13709
  have eq13738 : sk2 = sk4 := resolve eq13726 eq13605 -- resolution 13726,13605
  have eq13741 : ¬(new a sk2 sk0) := Eq.mp (by simp only [eq13738, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq11172 -- backward demodulation 11172,13738
  have eq13859 : (old a sk2 sk0) ∨ c = sk2 := resolve eq12273 eq13709 -- resolution 12273,13709
  have eq13864 : c = sk2 ∨ (new a sk2 sk0) := resolve eq13859 imp_new_0 -- resolution 13859,58
  have eq13865 : c = sk2 := resolve eq13864 eq13741 -- subsumption resolution 13864,13741
  have eq13890 : a = c ∨ (old sk2 sk2 a) := Eq.mp (by simp only [eq13865, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13688 -- backward demodulation 13688,13865
  have eq13926 : (old sk2 sk2 a) := resolve eq13890 ac -- subsumption resolution 13890,47
  have eq13927 : (old c c a) := Eq.mp (by simp only [eq13865, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13926 -- forward demodulation 13926,13865
  subsumption p4YZ eq13927 -- subsumption resolution 13927,52

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (old_4 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X3 ∨ ¬ old X2 X4 X3 ∨ ¬ old X4 X4 X1 ∨ X4 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old Z X a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X0 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq85 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 69,72
  have eq86 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 69,73
  have eq99 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk0 b) := resolve eq85 rule_def_1_2 -- resolution 85,67
  have eq100 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 sk0 a) := resolve eq85 rule_def_1_1 -- resolution 85,66
  have eq101 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq85 rule_def_1_0 -- resolution 85,65
  have eq105 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (old sk3 sk3 b) := resolve eq86 rule_def_1_2 -- resolution 86,67
  have eq106 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (old sk2 sk3 a) := resolve eq86 rule_def_1_1 -- resolution 86,66
  have eq107 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 := resolve eq86 rule_def_1_0 -- resolution 86,65
  have eq108 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq101 rule_def_0_2 -- resolution 101,63
  have eq110 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq101 rule_def_0_0 -- resolution 101,61
  have eq113 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 := resolve eq108 old_2 -- resolution 108,56
  have eq126 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq107 rule_def_0_2 -- resolution 107,63
  have eq128 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ a = sk3 := resolve eq107 rule_def_0_0 -- resolution 107,61
  have eq135 : (old sk0 sk1 sk2) ∨ (old sk0 sk0 b) ∨ b = sk1 := resolve eq99 rule_def_0_1 -- resolution 99,62
  have eq142 : (old sk2 sk0 a) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq100 rule_def_0_2 -- resolution 100,63
  have eq151 : (old sk3 sk3 b) ∨ (old sk3 sk1 sk2) ∨ b = sk1 := resolve eq105 rule_def_0_1 -- resolution 105,62
  have eq159 : (old sk3 sk1 sk2) ∨ (old sk2 sk3 a) ∨ b = sk1 := resolve eq106 rule_def_0_1 -- resolution 106,62
  have eq203 (X0 X1 X2 : G) : (old sk3 sk1 sk2) ∨ b = sk1 ∨ sk3 = X0 ∨ ¬(old X1 sk3 X2) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 b) := resolve eq151 old_4 -- resolution 151,58
  have eq274 : c = sk2 ∨ sk0 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq113 eq126 -- resolution 113,126
  have eq275 : c = sk2 ∨ sk0 = sk3 ∨ c = sk1 := resolve eq274 rfl -- duplicate literal removal 274
  have eq288 : c = sk2 ∨ c = sk1 := resolve eq275 preserve_2 -- subsumption resolution 275,74
  have eq300 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 := Or.assoc3 (eq288.imp_left (fun h : c = sk2 ↦ superpose h eq110)) -- superposition 110,288, 288 into 110, unify on (0).2 in 288 and (0).3 in 110
  have eq302 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 := Or.assoc3 (eq288.imp_left (fun h : c = sk2 ↦ superpose h eq128)) -- superposition 128,288, 288 into 128, unify on (0).2 in 288 and (0).3 in 128
  have eq313 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 := resolve eq302 rfl -- duplicate literal removal 302
  have eq315 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq300 rfl -- duplicate literal removal 300
  have eq324 : c = sk1 ∨ a = sk0 := resolve eq315 p4XY -- subsumption resolution 315,51
  have eq325 : a = sk3 ∨ c = sk1 := resolve eq313 p4XY -- subsumption resolution 313,51
  have eq391 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (old sk2 sk0 a) ∨ a = sk0 := Or.assoc3 (eq324.imp_left (fun h : c = sk1 ↦ superpose h eq100)) -- superposition 100,324, 324 into 100, unify on (0).2 in 324 and (0).2 in 100
  have eq406 : (sP0 sk0 c sk2) ∨ (old sk2 sk0 a) ∨ a = sk0 := resolve eq391 p4XZ -- subsumption resolution 391,52
  have eq407 : (old sk2 sk0 a) ∨ a = sk0 := resolve eq406 rule_def_0_0 -- subsumption resolution 406,61
  have eq424 : a ≠ sk0 ∨ c = sk1 := eq325.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 74,325, 325 into 74, unify on (0).2 in 325 and (0).2 in 74
  have eq442 : c = sk1 := resolve eq424 eq324 -- subsumption resolution 424,324
  have eq464 : (old sk0 c sk2) ∨ (old sk0 sk0 b) ∨ b = sk1 := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq135 -- backward demodulation 135,442
  have eq466 : (old sk0 c sk2) ∨ (old sk2 sk0 a) ∨ c = sk2 := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq142 -- backward demodulation 142,442
  have eq477 : (old sk3 c sk2) ∨ (old sk2 sk3 a) ∨ b = sk1 := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq159 -- backward demodulation 159,442
  have eq516 : ∀ (X0 X1 X2 : G) , (old sk3 c sk2) ∨ b = sk1 ∨ sk3 = X0 ∨ ¬(old X1 sk3 X2) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 b) := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq203 -- backward demodulation 203,442
  have eq571 : (old sk0 sk0 b) ∨ b = sk1 := resolve eq464 p4XZ -- subsumption resolution 464,52
  have eq572 : c = b ∨ (old sk0 sk0 b) := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq571 -- forward demodulation 571,442
  have eq573 : (old sk0 sk0 b) := resolve eq572 bc -- subsumption resolution 572,49
  have eq574 : (old sk2 sk0 a) ∨ c = sk2 := resolve eq466 p4XZ -- subsumption resolution 466,52
  have eq583 : (old sk2 sk3 a) ∨ b = sk1 := resolve eq477 p4XZ -- subsumption resolution 477,52
  have eq584 : c = b ∨ (old sk2 sk3 a) := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq583 -- forward demodulation 583,442
  have eq585 : (old sk2 sk3 a) := resolve eq584 bc -- subsumption resolution 584,49
  have eq627 (X0 X1 X2 : G) : b = sk1 ∨ sk3 = X0 ∨ ¬(old X1 sk3 X2) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 b) := resolve eq516 p4XZ -- subsumption resolution 516,52
  have eq628 : ∀ (X0 X1 X2 : G) , c = b ∨ sk3 = X0 ∨ ¬(old X1 sk3 X2) ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 b) := Eq.mp (by simp only [eq442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq627 -- forward demodulation 627,442
  have eq629 (X0 X1 X2 : G) : ¬(old X1 sk3 X2) ∨ sk3 = X0 ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 b) := resolve eq628 bc -- subsumption resolution 628,49
  have eq844 (X0 : G) : ¬(old sk2 X0 a) ∨ sk3 = X0 ∨ ¬(old X0 X0 b) := resolve eq629 eq585 -- resolution 629,585
  have eq845 : sk0 = sk3 ∨ ¬(old sk0 sk0 b) ∨ a = sk0 := resolve eq844 eq407 -- resolution 844,407
  have eq846 : sk0 = sk3 ∨ ¬(old sk0 sk0 b) ∨ c = sk2 := resolve eq844 eq574 -- resolution 844,574
  have eq852 : ¬(old sk0 sk0 b) ∨ a = sk0 := resolve eq845 preserve_2 -- subsumption resolution 845,74
  have eq853 : a = sk0 := resolve eq852 eq573 -- subsumption resolution 852,573
  have eq854 : a ≠ sk3 := Eq.mp (by simp only [eq853, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 74,853
  have eq864 : (old a a b) := Eq.mp (by simp only [eq853, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq573 -- backward demodulation 573,853
  have eq901 : a = sk3 ∨ ¬(old sk0 sk0 b) ∨ c = sk2 := Eq.mp (by simp only [eq853, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq846 -- forward demodulation 846,853
  have eq902 : ¬(old sk0 sk0 b) ∨ c = sk2 := resolve eq901 eq854 -- subsumption resolution 901,854
  have eq903 : ¬(old a a b) ∨ c = sk2 := Eq.mp (by simp only [eq853, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq902 -- forward demodulation 902,853
  have eq904 : c = sk2 := resolve eq903 eq864 -- subsumption resolution 903,864
  have eq912 : (old c sk3 a) := Eq.mp (by simp only [eq904, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq585 -- backward demodulation 585,904
  subsumption p4YZ eq912 -- subsumption resolution 912,53

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X1 X0 ∨ old X1 X0 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, c ≠ Y ∨ ¬ old Z X a ∨ ¬ old X X b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X1 X0 ∨ new X1 X0 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq81 (X0 X2 : G) : ¬(old X2 X0 a) ∨ ¬(old X0 X0 b) ∨ (new X0 c X2) := resolve imp_new_2 rfl -- equality resolution 66
  have eq83 (X0 : G) : ¬(new sk2 sk1 X0) ∨ sk0 = X0 := resolve prev_0 preserve_1 -- resolution 72,76
  have eq93 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 71,75
  have eq94 : (sP1 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ (sP0 sk2 sk1 sk0) := resolve new_imp preserve_1 -- resolution 71,76
  have eq108 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (old sk0 sk0 b) := resolve eq93 rule_def_1_2 -- resolution 93,69
  have eq110 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq93 rule_def_1_0 -- resolution 93,67
  have eq114 : (sP0 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ (old sk2 sk2 b) := resolve eq94 rule_def_1_2 -- resolution 94,69
  have eq116 : (sP0 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ c = sk1 := resolve eq94 rule_def_1_0 -- resolution 94,67
  have eq117 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq110 rule_def_0_2 -- resolution 110,65
  have eq118 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ b = sk0 := resolve eq110 rule_def_0_1 -- resolution 110,64
  have eq119 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq110 rule_def_0_0 -- resolution 110,63
  have eq133 : (old sk2 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq116 rule_def_0_2 -- resolution 116,65
  have eq143 : (old sk0 sk0 sk1) ∨ (old sk0 sk0 b) ∨ b = sk0 := resolve eq108 rule_def_0_1 -- resolution 108,64
  have eq146 : c = sk1 ∨ c = sk0 ∨ (old sk1 sk0 sk2) ∨ ¬(old sk0 sk0 sk1) := resolve eq133 old_3 -- resolution 133,59
  have eq150 : (old sk1 sk0 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq146 eq117 -- subsumption resolution 146,117
  have eq159 : (old sk2 sk1 sk0) ∨ (old sk2 sk2 b) ∨ c = sk0 := resolve eq114 rule_def_0_2 -- resolution 114,65
  have eq174 : c = sk0 ∨ c = sk1 ∨ (new sk1 sk0 sk2) := resolve eq150 imp_new_0 -- resolution 150,61
  have eq175 : c = sk1 ∨ c = sk0 := resolve eq174 preserve_2 -- subsumption resolution 174,77
  have eq196 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq175.imp_left (fun h : c = sk1 ↦ superpose h eq119)) -- superposition 119,175, 175 into 119, unify on (0).2 in 175 and (0).3 in 119
  have eq198 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq196 rfl -- duplicate literal removal 196
  have eq210 : c = sk0 ∨ a = sk0 := resolve eq198 p4XY -- subsumption resolution 198,53
  have eq271 : (old c c sk1) ∨ (old c c b) ∨ c = b ∨ a = sk0 := Or.assoc3 (eq210.imp_left (fun h : c = sk0 ↦ superpose h eq143)) -- superposition 143,210, 210 into 143, unify on (0).2 in 210 and (0).1 in 143
  have eq286 : (old c c b) ∨ c = b ∨ a = sk0 := resolve eq271 p4YZ -- subsumption resolution 271,55
  have eq287 : c = b ∨ a = sk0 := resolve eq286 p4YZ -- subsumption resolution 286,55
  have eq288 : a = sk0 := resolve eq287 bc -- subsumption resolution 287,51
  have eq293 : ∀ (X0 : G) , a = X0 ∨ ¬(new sk2 sk1 X0) := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq83 -- backward demodulation 83,288
  have eq307 : (old a a sk1) ∨ c = sk0 ∨ b = sk0 := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq118 -- backward demodulation 118,288
  have eq342 : (old sk2 sk1 a) ∨ (old sk2 sk2 b) ∨ c = sk0 := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq159 -- backward demodulation 159,288
  have eq356 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq175 -- backward demodulation 175,288
  have eq420 : a = c ∨ (old a a sk1) ∨ b = sk0 := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq307 -- forward demodulation 307,288
  have eq421 : (old a a sk1) ∨ b = sk0 := resolve eq420 ac -- subsumption resolution 420,50
  have eq422 : a = b ∨ (old a a sk1) := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq421 -- forward demodulation 421,288
  have eq470 : a = c ∨ (old sk2 sk1 a) ∨ (old sk2 sk2 b) := Eq.mp (by simp only [eq288, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq342 -- forward demodulation 342,288
  have eq471 : (old sk2 sk1 a) ∨ (old sk2 sk2 b) := resolve eq470 ac -- subsumption resolution 470,50
  have eq486 : c = sk1 := resolve eq356 ac -- subsumption resolution 356,50
  have eq491 : ∀ (X0 : G) , ¬(new sk2 c X0) ∨ a = X0 := Eq.mp (by simp only [eq486, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq293 -- backward demodulation 293,486
  have eq504 : (old a a c) ∨ a = b := Eq.mp (by simp only [eq486, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq422 -- backward demodulation 422,486
  have eq511 : (old sk2 c a) ∨ (old sk2 sk2 b) := Eq.mp (by simp only [eq486, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq471 -- backward demodulation 471,486
  have eq531 : a = b := resolve eq504 p4XY -- subsumption resolution 504,53
  have eq533 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 52,531
  have eq537 : ∀ (X0 X2 : G) , ¬(old X2 X0 a) ∨ ¬(old X0 X0 a) ∨ (new X0 c X2) := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq81 -- backward demodulation 81,531
  have eq546 : (old sk2 sk2 b) := resolve eq511 p4XZ -- subsumption resolution 511,54
  have eq547 : (old sk2 sk2 a) := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq546 -- forward demodulation 546,531
  have eq659 : ¬(old sk2 sk2 a) ∨ (new sk2 c sk2) := resolve eq537 eq547 -- resolution 537,547
  have eq661 : (new sk2 c sk2) := resolve eq659 eq547 -- subsumption resolution 659,547
  have eq672 : a = sk2 := resolve eq661 eq491 -- resolution 661,491
  have eq686 : (old a a a) := Eq.mp (by simp only [eq672, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq547 -- backward demodulation 547,672
  subsumption eq533 eq686 -- subsumption resolution 686,533

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_4 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X3 ∨ ¬ old X2 X4 X3 ∨ ¬ old X4 X4 X1 ∨ X4 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old Z X a ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X0 X1 ∨ ¬ new X2 X0 X3 ∨ ¬ new X2 X4 X3 ∨ ¬ new X4 X4 X1 ∨ X4 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq110 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 75,80
  have eq111 : (sP1 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) := resolve new_imp preserve_1 -- resolution 75,81
  have eq112 : (sP1 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ (sP0 sk2 sk4 sk3) := resolve new_imp preserve_2 -- resolution 75,82
  have eq113 : (sP1 sk4 sk4 sk1) ∨ (old sk4 sk4 sk1) ∨ (sP0 sk4 sk4 sk1) := resolve new_imp preserve_3 -- resolution 75,83
  have eq132 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (old sk0 sk0 b) := resolve eq110 rule_def_1_2 -- resolution 110,73
  have eq134 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq110 rule_def_1_0 -- resolution 110,71
  have eq140 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ c = sk0 := resolve eq111 rule_def_1_0 -- resolution 111,71
  have eq141 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq134 rule_def_0_2 -- resolution 134,69
  have eq143 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq134 rule_def_0_0 -- resolution 134,67
  have eq145 : (sP0 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ (old sk3 sk2 a) := resolve eq112 rule_def_1_1 -- resolution 112,72
  have eq146 : (sP0 sk2 sk4 sk3) ∨ (old sk2 sk4 sk3) ∨ c = sk4 := resolve eq112 rule_def_1_0 -- resolution 112,71
  have eq152 (X0 X1 X2 : G) : ¬(old X1 sk0 X2) ∨ c = sk1 ∨ sk0 = X0 ∨ c = sk0 ∨ ¬(old X1 X0 X2) ∨ ¬(old X0 X0 sk1) := resolve eq141 old_4 -- resolution 141,64
  have eq153 : (sP0 sk4 sk4 sk1) ∨ (old sk4 sk4 sk1) ∨ (old sk4 sk4 b) := resolve eq113 rule_def_1_2 -- resolution 113,73
  have eq154 : (sP0 sk4 sk4 sk1) ∨ (old sk4 sk4 sk1) ∨ (old sk1 sk4 a) := resolve eq113 rule_def_1_1 -- resolution 113,72
  have eq155 : (sP0 sk4 sk4 sk1) ∨ (old sk4 sk4 sk1) ∨ c = sk4 := resolve eq113 rule_def_1_0 -- resolution 113,71
  have eq168 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq140 rule_def_0_2 -- resolution 140,69
  have eq169 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ b = sk0 := resolve eq140 rule_def_0_1 -- resolution 140,68
  have eq186 : (old sk2 sk4 sk3) ∨ c = sk4 ∨ c = sk3 := resolve eq146 rule_def_0_2 -- resolution 146,69
  have eq194 : (old sk4 sk4 sk1) ∨ c = sk4 ∨ c = sk1 := resolve eq155 rule_def_0_2 -- resolution 155,69
  have eq196 : (old sk4 sk4 sk1) ∨ c = sk4 ∨ a = sk4 := resolve eq155 rule_def_0_0 -- resolution 155,67
  have eq203 : (old sk0 sk0 sk1) ∨ (old sk0 sk0 b) ∨ b = sk0 := resolve eq132 rule_def_0_1 -- resolution 132,68
  have eq247 : (old sk3 sk2 a) ∨ (old sk2 sk4 sk3) ∨ b = sk4 := resolve eq145 rule_def_0_1 -- resolution 145,68
  have eq266 : (old sk4 sk4 sk1) ∨ (old sk1 sk4 a) ∨ a = sk4 := resolve eq154 rule_def_0_0 -- resolution 154,67
  have eq1741 (X0 : G) : c = sk1 ∨ sk0 = X0 ∨ c = sk0 ∨ ¬(old sk2 X0 sk3) ∨ ¬(old X0 X0 sk1) ∨ c = sk0 ∨ c = sk3 := resolve eq152 eq168 -- resolution 152,168
  have eq1746 (X0 : G) : ¬(old sk2 X0 sk3) ∨ sk0 = X0 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old X0 X0 sk1) ∨ c = sk3 := resolve eq1741 rfl -- duplicate literal removal 1741
  have eq3492 : sk0 = sk4 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old sk4 sk4 sk1) ∨ c = sk3 ∨ c = sk4 ∨ c = sk3 := resolve eq1746 eq186 -- resolution 1746,186
  have eq3497 : sk0 = sk4 ∨ c = sk0 ∨ c = sk1 ∨ ¬(old sk4 sk4 sk1) ∨ c = sk3 ∨ c = sk4 := resolve eq3492 rfl -- duplicate literal removal 3492
  have eq3510 : c = sk0 ∨ c = sk1 ∨ ¬(old sk4 sk4 sk1) ∨ c = sk3 ∨ c = sk4 := resolve eq3497 preserve_4 -- subsumption resolution 3497,84
  have eq3511 : c = sk4 ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 := resolve eq3510 eq194 -- subsumption resolution 3510,194
  have eq3529 : (sP0 c c sk1) ∨ (old c c sk1) ∨ (old c c b) ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 := Or.assoc3 (eq3511.imp_left (fun h : c = sk4 ↦ superpose h eq153)) -- superposition 153,3511, 3511 into 153, unify on (0).2 in 3511 and (0).1 in 153
  have eq3632 : (sP0 c c sk1) ∨ (old c c b) ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 := resolve eq3529 p4YZ -- subsumption resolution 3529,59
  have eq3633 : (sP0 c c sk1) ∨ c = sk1 ∨ c = sk3 ∨ c = sk0 := resolve eq3632 p4YZ -- subsumption resolution 3632,59
  have eq3634 : c = sk3 ∨ c = sk1 ∨ c = sk0 := resolve eq3633 rule_def_0_2 -- subsumption resolution 3633,69
  have eq3667 : (old sk2 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := Or.assoc3 (eq3634.imp_left (fun h : c = sk3 ↦ superpose h eq169)) -- superposition 169,3634, 3634 into 169, unify on (0).2 in 3634 and (0).3 in 169
  have eq3683 : (old c sk2 a) ∨ (old sk2 sk4 c) ∨ b = sk4 ∨ c = sk1 ∨ c = sk0 := Or.assoc3 (eq3634.imp_left (fun h : c = sk3 ↦ superpose h eq247)) -- superposition 247,3634, 3634 into 247, unify on (0).2 in 3634 and (0).1 in 247
  have eq3755 : (old sk2 sk0 c) ∨ c = sk0 ∨ b = sk0 ∨ c = sk1 := resolve eq3667 rfl -- duplicate literal removal 3667
  have eq3763 : c = sk1 ∨ b = sk0 ∨ c = sk0 := resolve eq3755 p4XY -- subsumption resolution 3755,57
  have eq3767 : (old sk2 sk4 c) ∨ b = sk4 ∨ c = sk1 ∨ c = sk0 := resolve eq3683 p4YZ -- subsumption resolution 3683,59
  have eq3768 : b = sk4 ∨ c = sk1 ∨ c = sk0 := resolve eq3767 p4XY -- subsumption resolution 3767,57
  have eq3793 : (sP1 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq3763.imp_left (fun h : c = sk1 ↦ superpose h eq110)) -- superposition 110,3763, 3763 into 110, unify on (0).2 in 3763 and (0).3 in 110
  have eq3882 : (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq3793 p4XY -- subsumption resolution 3793,57
  have eq3883 : (sP0 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq3882 rule_def_1_0 -- subsumption resolution 3882,71
  have eq3884 : b = sk0 ∨ c = sk0 := resolve eq3883 rule_def_0_1 -- subsumption resolution 3883,68
  have eq4276 : b ≠ sk0 ∨ c = sk1 ∨ c = sk0 := eq3768.imp_left (fun h : b = sk4 ↦ superpose h preserve_4) -- superposition 84,3768, 3768 into 84, unify on (0).2 in 3768 and (0).2 in 84
  have eq4405 : c = sk1 ∨ c = sk0 := resolve eq4276 eq3884 -- subsumption resolution 4276,3884
  have eq4436 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq4405.imp_left (fun h : c = sk1 ↦ superpose h eq143)) -- superposition 143,4405, 4405 into 143, unify on (0).2 in 4405 and (0).3 in 143
  have eq4504 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq4436 rfl -- duplicate literal removal 4436
  have eq4511 : c = sk0 ∨ a = sk0 := resolve eq4504 p4XY -- subsumption resolution 4504,57
  have eq4558 : (old c c sk1) ∨ (old c c b) ∨ c = b ∨ a = sk0 := Or.assoc3 (eq4511.imp_left (fun h : c = sk0 ↦ superpose h eq203)) -- superposition 203,4511, 4511 into 203, unify on (0).2 in 4511 and (0).1 in 203
  have eq4640 : (old c c b) ∨ c = b ∨ a = sk0 := resolve eq4558 p4YZ -- subsumption resolution 4558,59
  have eq4641 : c = b ∨ a = sk0 := resolve eq4640 p4YZ -- subsumption resolution 4640,59
  have eq4642 : a = sk0 := resolve eq4641 bc -- subsumption resolution 4641,55
  have eq4645 : a ≠ sk4 := Eq.mp (by simp only [eq4642, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_4 -- backward demodulation 84,4642
  have eq5202 : a = c ∨ b = sk4 ∨ c = sk1 := Eq.mp (by simp only [eq4642, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3768 -- backward demodulation 3768,4642
  have eq5209 : a = c ∨ b = sk0 := Eq.mp (by simp only [eq4642, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3884 -- backward demodulation 3884,4642
  have eq6114 : b = sk4 ∨ c = sk1 := resolve eq5202 ac -- subsumption resolution 5202,54
  have eq6131 : b = sk0 := resolve eq5209 ac -- subsumption resolution 5209,54
  have eq6132 : a = b := Eq.mp (by simp only [eq4642, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6131 -- forward demodulation 6131,4642
  have eq6317 : a = sk4 ∨ c = sk1 := Eq.mp (by simp only [eq6132, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6114 -- backward demodulation 6114,6132
  have eq6392 : c = sk1 := resolve eq6317 eq4645 -- subsumption resolution 6317,4645
  have eq6402 : (old sk4 sk4 c) ∨ c = sk4 ∨ a = sk4 := Eq.mp (by simp only [eq6392, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq196 -- backward demodulation 196,6392
  have eq6410 : (old sk4 sk4 c) ∨ (old sk1 sk4 a) ∨ a = sk4 := Eq.mp (by simp only [eq6392, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq266 -- backward demodulation 266,6392
  have eq6451 : c = sk4 ∨ a = sk4 := resolve eq6402 p4XY -- subsumption resolution 6402,57
  have eq6452 : c = sk4 := resolve eq6451 eq4645 -- subsumption resolution 6451,4645
  have eq6585 : (old sk1 sk4 a) ∨ a = sk4 := resolve eq6410 p4XY -- subsumption resolution 6410,57
  have eq6586 : (old sk1 sk4 a) := resolve eq6585 eq4645 -- subsumption resolution 6585,4645
  have eq6587 : (old sk1 c a) := Eq.mp (by simp only [eq6452, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6586 -- forward demodulation 6586,6452
  subsumption p4XZ eq6587 -- subsumption resolution 6587,58

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (bc : c ≠ b) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq86 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq96 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk0 b) := resolve eq86 rule_def_1_2 -- resolution 86,71
  have eq98 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq86 rule_def_1_0 -- resolution 86,69
  have eq104 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq98 rule_def_0_0 -- resolution 98,65
  have eq105 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq104 preserve_1 -- subsumption resolution 104,78
  have eq111 : c = sk1 ∨ memold sk0 := resolve eq105 old_mem1 -- resolution 105,74
  have eq114 : c = sk1 := resolve eq111 preserve_3 -- subsumption resolution 111,80
  have eq117 : (sP0 sk0 c sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk0 sk0 b) := Eq.mp (by simp only [eq114, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq96 -- backward demodulation 96,114
  have eq126 : (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 sk0 b) := Eq.mp (by simp only [eq114, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq117 -- forward demodulation 117,114
  have eq127 : (sP0 sk0 c sk2) ∨ (old sk0 sk0 b) := resolve eq126 p4XZ -- subsumption resolution 126,56
  have eq135 : (old sk0 sk0 b) ∨ c = b := resolve eq127 rule_def_0_1 -- resolution 127,66
  have eq137 : (old sk0 sk0 b) := resolve eq135 bc -- subsumption resolution 135,53
  have eq147 : memold sk0 := resolve eq137 old_mem1 -- resolution 137,74
  subsumption preserve_3 eq147 -- subsumption resolution 147,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq86 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq98 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq86 rule_def_1_0 -- resolution 86,69
  have eq99 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq98 preserve_4 -- subsumption resolution 98,81
  have eq101 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq99 rule_def_0_1 -- resolution 99,66
  have eq103 : (old sk0 sk1 sk2) := resolve eq101 preserve_2 -- subsumption resolution 101,79
  have eq113 : memold sk1 := resolve eq103 old_mem2 -- resolution 103,75
  subsumption preserve_3 eq113 -- subsumption resolution 113,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), old Z X a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq86 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq97 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk2 sk0 a) := resolve eq86 rule_def_1_1 -- resolution 86,70
  have eq98 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq86 rule_def_1_0 -- resolution 86,69
  have eq102 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq98 rule_def_0_2 -- resolution 98,67
  have eq105 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq102 preserve_4 -- subsumption resolution 102,81
  have eq113 : c = sk1 ∨ memold sk2 := resolve eq105 old_mem3 -- resolution 105,76
  have eq114 : c = sk1 := resolve eq113 preserve_3 -- subsumption resolution 113,80
  have eq118 : (sP0 sk0 c sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 sk0 a) := Eq.mp (by simp only [eq114, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq97 -- backward demodulation 97,114
  have eq126 : (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk2 sk0 a) := Eq.mp (by simp only [eq114, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq118 -- forward demodulation 118,114
  have eq127 : (sP0 sk0 c sk2) ∨ (old sk2 sk0 a) := resolve eq126 p4XZ -- subsumption resolution 126,56
  have eq136 : (old sk2 sk0 a) ∨ c = sk2 := resolve eq127 rule_def_0_2 -- resolution 127,67
  have eq139 : (old sk2 sk0 a) := resolve eq136 preserve_4 -- subsumption resolution 136,81
  have eq155 : memold sk2 := resolve eq139 old_mem1 -- resolution 139,74
  subsumption preserve_3 eq155 -- subsumption resolution 155,80

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X3 ∨ ¬ R X2 X3 X4 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X0 = X3)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X1 X0 ∨ R X1 X0 X2)
  rule_4 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X0 X1 ∨ ¬ R X2 X0 X3 ∨ ¬ R X2 X4 X3 ∨ ¬ R X4 X4 X1 ∨ X4 = X0)
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
  let sP1 (X Y Z) := c = Y ∧ ps.R Z X a ∧ ps.R X X b
  have hsP1 (X Y Z) (h : sP1 X Y Z) : c = Y ∧ ps.R Z X a ∧ ps.R X X b := h
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sP1 bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sP1 ac bc p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_3 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_2 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sP1 bc p4XY p4XZ p4YZ ps.rule_2 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sP1 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_2 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sP1 ac bc p4XY p4XZ p4YZ ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) bc p4XZ rule_def_0_0 rule_def_0_1 rule_def_1_0 rule_def_1_2 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_0 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) p4XZ rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp ps.mem_1 ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X1 X3 ∨ ¬ ps.compl X2 X3 X4 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X1) (max (Nat.pair X2 X3) (max (Nat.pair X1 X4) 0)))
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

theorem PartialSolution.toMagma_equation883 :
    letI := ps.toMagma
    Equation883 ℕ := by
  simp only [Equation883, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun X1 X1) (ps.complFun (ps.complFun X0 X1) (ps.complFun X1 X1))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2035 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (2, 1, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation883_not_implies_Equation2035 : ∃ (G : Type) (_ : Magma G), Equation883 G ∧ ¬Equation2035 G := by
  use ℕ, PartialSolution.counter2035.toMagma, PartialSolution.counter2035.toMagma_equation883
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2035.of_R 1 1 2] | rw [PartialSolution.counter2035.of_R 1 2 2] | rw [PartialSolution.counter2035.of_R 2 1 1])
  all_goals simp [PartialSolution.counter2035]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2101 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (2, 1, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation883_not_implies_Equation2101 : ∃ (G : Type) (_ : Magma G), Equation883 G ∧ ¬Equation2101 G := by
  use ℕ, PartialSolution.counter2101.toMagma, PartialSolution.counter2101.toMagma_equation883
  simp only [not_forall, PartialSolution.toMagma]
  use 1, 1
  repeat (first | rw [PartialSolution.counter2101.of_R 1 1 2] | rw [PartialSolution.counter2101.of_R 1 2 2] | rw [PartialSolution.counter2101.of_R 2 1 1])
  all_goals simp [PartialSolution.counter2101]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2238 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 2), (1, 3, 3), (2, 1, 3)} : Finset _)
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
theorem _root_.Equation883_not_implies_Equation2238 : ∃ (G : Type) (_ : Magma G), Equation883 G ∧ ¬Equation2238 G := by
  use ℕ, PartialSolution.counter2238.toMagma, PartialSolution.counter2238.toMagma_equation883
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2238.of_R 1 1 2] | rw [PartialSolution.counter2238.of_R 1 2 2] | rw [PartialSolution.counter2238.of_R 1 3 3] | rw [PartialSolution.counter2238.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2238]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2304 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 1), (1, 3, 1), (2, 1, 3)} : Finset _)
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
theorem _root_.Equation883_not_implies_Equation2304 : ∃ (G : Type) (_ : Magma G), Equation883 G ∧ ¬Equation2304 G := by
  use ℕ, PartialSolution.counter2304.toMagma, PartialSolution.counter2304.toMagma_equation883
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter2304.of_R 1 1 1] | rw [PartialSolution.counter2304.of_R 1 2 1] | rw [PartialSolution.counter2304.of_R 1 3 1] | rw [PartialSolution.counter2304.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2304]

end Eq883