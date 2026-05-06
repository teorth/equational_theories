import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq503

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_6 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X4 ∨ ¬ old X1 X2 X5 ∨ ¬ old X3 X4 X5 ∨ X1 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old a Z X2 ∨ ¬ old Z X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old Z (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq81 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 X3 b) ∨ ¬(old a X2 X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 68
  have eq82 (X2 X3 : G) : ¬(old a X2 X3) ∨ ¬(old X2 X3 b) ∨ (new a c X2) := resolve eq81 rfl -- equality resolution 81
  have eq86 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4XZ -- resolution 71,54
  have eq93 (X0 X1 X2 : G) : ¬(old X0 (sF0 X1 X2 X0) b) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq82 rule_def_1_2 -- resolution 82,71
  have eq95 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq93 rule_def_1_3 -- subsumption resolution 93,72
  have eq100 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 74,75
  have eq101 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 74,76
  have eq111 (X0 X1 X2 X3 X4 X5 : G) : ¬(old X3 X1 (sF0 X4 X5 X1)) ∨ ¬(old X0 X2 b) ∨ X0 = X1 ∨ ¬(old X3 X0 X2) ∨ ¬(sP1 X4 X5 X1) := resolve old_6 rule_def_1_3 -- resolution 62,72
  have eq113 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (new a c sk2) := resolve eq100 eq95 -- resolution 100,95
  have eq114 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq100 rule_def_1_1 -- resolution 100,70
  have eq115 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq100 rule_def_1_0 -- resolution 100,69
  have eq116 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq115 rule_def_0_0 -- subsumption resolution 115,65
  have eq119 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ c = sk1 := resolve eq101 rule_def_1_1 -- resolution 101,70
  have eq120 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ a = sk0 := resolve eq101 rule_def_1_0 -- resolution 101,69
  have eq121 : (old sk0 sk1 sk3) ∨ a = sk0 := resolve eq120 rule_def_0_0 -- subsumption resolution 120,65
  have eq126 (X0 : G) : ¬(old sk0 sk1 X0) ∨ sk2 = X0 ∨ a = sk0 := resolve eq116 old_0 -- resolution 116,56
  have eq138 : sk2 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq126 eq121 -- resolution 126,121
  have eq139 : sk2 = sk3 ∨ a = sk0 := resolve eq138 rfl -- duplicate literal removal 138
  have eq141 : a = sk0 := resolve eq139 preserve_2 -- subsumption resolution 139,77
  have eq144 : (sP0 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq100 -- backward demodulation 100,141
  have eq145 : (sP0 a sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq101 -- backward demodulation 101,141
  have eq147 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (new a c sk2) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq113 -- backward demodulation 113,141
  have eq148 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq114 -- backward demodulation 114,141
  have eq152 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq119 -- backward demodulation 119,141
  have eq154 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq144 -- forward demodulation 144,141
  have eq155 : (sP1 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq154 -- forward demodulation 154,141
  have eq156 : (sP1 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq145 -- forward demodulation 145,141
  have eq157 : (sP1 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a sk1 sk3) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq156 -- forward demodulation 156,141
  have eq160 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (new a c sk2) := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq147 -- forward demodulation 147,141
  have eq161 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq148 -- forward demodulation 148,141
  have eq165 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq141, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq152 -- forward demodulation 152,141
  have eq168 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq161 rule_def_0_2 -- resolution 161,67
  have eq180 (X0 : G) : ¬(old a sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq168 old_0 -- resolution 168,56
  have eq193 : (old a sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq165 rule_def_0_2 -- resolution 165,67
  have eq194 : (old a sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq165 rule_def_0_1 -- resolution 165,66
  have eq215 : (new a c sk2) ∨ (old a sk1 sk2) ∨ c = sk2 := resolve eq160 rule_def_0_2 -- resolution 160,67
  have eq220 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP0 a c sk2) ∨ (old a c sk2) ∨ (sP1 a c sk2) := resolve eq215 new_imp -- resolution 215,74
  have eq221 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) := resolve eq220 p4XZ -- subsumption resolution 220,54
  have eq222 : (sP1 a c sk2) ∨ c = sk2 ∨ (old a sk1 sk2) := resolve eq221 rule_def_0_2 -- subsumption resolution 221,67
  have eq250 (X0 X1 X2 X3 X4 : G) : ¬(old X0 X1 b) ∨ X0 = X2 ∨ ¬(old a X0 X1) ∨ ¬(sP1 X3 X4 X2) ∨ ¬(sP1 X3 X4 X2) := resolve eq111 rule_def_1_2 -- resolution 111,71
  have eq253 (X0 X1 X2 X3 X4 : G) : ¬(sP1 X3 X4 X2) ∨ X0 = X2 ∨ ¬(old a X0 X1) ∨ ¬(old X0 X1 b) := resolve eq250 rfl -- duplicate literal removal 250
  have eq273 (X0 X1 : G) : sk2 = X0 ∨ ¬(old a X0 X1) ∨ ¬(old X0 X1 b) ∨ c = sk2 ∨ (old a sk1 sk2) := resolve eq253 eq222 -- resolution 253,222
  have eq277 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq180 eq194 -- resolution 180,194
  have eq281 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq277 rfl -- duplicate literal removal 277
  have eq284 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq281 preserve_2 -- subsumption resolution 281,77
  have eq288 : (sP1 a sk1 c) ∨ (old a sk1 c) ∨ (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq284.imp_left (fun h : c = sk2 ↦ superpose h eq155)) -- superposition 155,284, 284 into 155, unify on (0).2 in 284 and (0).3 in 155
  have eq297 : (old a sk1 c) ∨ (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq288 eq86 -- subsumption resolution 288,86
  have eq298 : (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq297 p4XY -- subsumption resolution 297,53
  have eq299 : b = sk1 ∨ c = sk1 := resolve eq298 rule_def_0_1 -- subsumption resolution 298,66
  have eq309 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq299.imp_left (fun h : b = sk1 ↦ superpose h eq168)) -- superposition 168,299, 299 into 168, unify on (0).2 in 299 and (0).2 in 168
  have eq311 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq299.imp_left (fun h : b = sk1 ↦ superpose h eq193)) -- superposition 193,299, 299 into 193, unify on (0).2 in 299 and (0).2 in 193
  have eq321 : c = b ∨ c = sk2 ∨ c = sk1 := resolve eq309 p3 -- subsumption resolution 309,52
  have eq322 : c = sk2 ∨ c = sk1 := resolve eq321 bc -- subsumption resolution 321,51
  have eq323 : c = b ∨ c = sk3 ∨ c = sk1 := resolve eq311 p3 -- subsumption resolution 311,52
  have eq324 : c = sk3 ∨ c = sk1 := resolve eq323 bc -- subsumption resolution 323,51
  have eq337 : c ≠ sk2 ∨ c = sk1 := eq324.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 77,324, 324 into 77, unify on (0).2 in 324 and (0).2 in 77
  have eq347 : c = sk1 := resolve eq337 eq322 -- subsumption resolution 337,322
  have eq350 : (sP0 a c sk2) ∨ (sP1 a sk1 sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq155 -- backward demodulation 155,347
  have eq351 : (sP0 a c sk3) ∨ (sP1 a sk1 sk3) ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq157 -- backward demodulation 157,347
  have eq376 : ∀ (X0 X1 : G) , (old a c sk2) ∨ sk2 = X0 ∨ ¬(old a X0 X1) ∨ ¬(old X0 X1 b) ∨ c = sk2 := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq273 -- backward demodulation 273,347
  have eq380 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq350 -- forward demodulation 350,347
  have eq381 : (old a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq380 -- forward demodulation 380,347
  have eq382 : (sP1 a c sk2) ∨ (sP0 a c sk2) := resolve eq381 p4XZ -- subsumption resolution 381,54
  have eq383 : (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq351 -- forward demodulation 351,347
  have eq384 : (old a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) := Eq.mp (by simp only [eq347, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq383 -- forward demodulation 383,347
  have eq385 : (sP1 a c sk3) ∨ (sP0 a c sk3) := resolve eq384 p4XZ -- subsumption resolution 384,54
  have eq414 (X0 X1 : G) : ¬(old a X0 X1) ∨ sk2 = X0 ∨ ¬(old X0 X1 b) ∨ c = sk2 := resolve eq376 p4XZ -- subsumption resolution 376,54
  have eq467 (X0 X1 X2 : G) : sk2 = X0 ∨ ¬(old X0 (sF0 X1 X2 X0) b) ∨ c = sk2 ∨ ¬(sP1 X1 X2 X0) := resolve eq414 rule_def_1_2 -- resolution 414,71
  have eq470 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ c = sk2 ∨ sk2 = X0 := resolve eq467 rule_def_1_3 -- subsumption resolution 467,72
  have eq482 : c = sk2 ∨ sk2 = sk3 ∨ (sP0 a c sk3) := resolve eq470 eq385 -- resolution 470,385
  have eq485 : (sP0 a c sk3) ∨ c = sk2 := resolve eq482 preserve_2 -- subsumption resolution 482,77
  have eq502 : c = sk2 ∨ c = b := resolve eq485 rule_def_0_1 -- resolution 485,66
  have eq506 : c = sk2 := resolve eq502 bc -- subsumption resolution 502,51
  have eq509 : (sP0 a c c) ∨ (sP1 a c sk2) := Eq.mp (by simp only [eq506, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq382 -- backward demodulation 382,506
  have eq521 : (sP1 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq506, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq509 -- forward demodulation 509,506
  have eq522 : (sP0 a c c) := resolve eq521 eq86 -- subsumption resolution 521,86
  have eq527 : c = b := resolve eq522 rule_def_0_1 -- resolution 522,66
  subsumption bc eq527 -- subsumption resolution 527,51

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X4 ∨ ¬ old X1 X2 X3 ∨ old X0 X4 X1)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X0 ∨ old X0 X2 X0)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X2 X3 ∨ ¬ old X2 X3 X1 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old a Z X2 ∨ ¬ old Z X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old Z (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X4 ∨ ¬ new X1 X2 X3 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq86 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 X3 b) ∨ ¬(old a X2 X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 71
  have eq87 (X2 X3 : G) : ¬(old a X2 X3) ∨ ¬(old X2 X3 b) ∨ (new a c X2) := resolve eq86 rfl -- equality resolution 86
  have eq90 (X0 X1 X2 : G) : (new a X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_2 imp_new_0 -- resolution 74,66
  have eq91 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4XZ -- resolution 74,57
  have eq97 (X0 : G) : ¬(new sk0 sk3 X0) ∨ sk4 = X0 := resolve prev_0 preserve_1 -- resolution 78,80
  have eq102 (X0 X1 X2 : G) : ¬(old b X2 (sF0 X0 X1 X2)) ∨ (old b (sF0 X0 X1 X2) b) ∨ ¬(sP1 X0 X1 X2) := resolve old_3 rule_def_1_3 -- resolution 62,75
  have eq104 (X0 X1 X2 : G) : ¬(old X0 (sF0 X1 X2 X0) b) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq87 rule_def_1_2 -- resolution 87,74
  have eq106 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq104 rule_def_1_3 -- subsumption resolution 104,75
  have eq109 (X0 X1 X2 X3 : G) : ¬(old X0 X3 (sF0 X1 X2 X3)) ∨ (sF0 X1 X2 X3) = X0 ∨ ¬(old X0 X0 b) ∨ ¬(sP1 X1 X2 X3) := resolve old_4 rule_def_1_3 -- resolution 63,75
  have eq115 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 77,79
  have eq116 : (sP1 sk0 sk3 sk4) ∨ (old sk0 sk3 sk4) ∨ (sP0 sk0 sk3 sk4) := resolve new_imp preserve_1 -- resolution 77,80
  have eq117 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) := resolve new_imp preserve_2 -- resolution 77,81
  have eq130 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq115 rule_def_1_1 -- resolution 115,73
  have eq131 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq115 rule_def_1_0 -- resolution 115,72
  have eq132 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq131 rule_def_0_0 -- subsumption resolution 131,68
  have eq140 : (sP0 sk0 sk3 sk4) ∨ (old sk0 sk3 sk4) ∨ c = sk3 := resolve eq116 rule_def_1_1 -- resolution 116,73
  have eq141 : (old sk0 sk3 sk4) ∨ (sP0 sk0 sk3 sk4) ∨ a = sk0 := resolve eq116 rule_def_1_0 -- resolution 116,72
  have eq142 : (old sk0 sk3 sk4) ∨ a = sk0 := resolve eq141 rule_def_0_0 -- subsumption resolution 141,68
  have eq149 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (new a c sk3) := resolve eq117 eq106 -- resolution 117,106
  have eq150 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq117 rule_def_1_1 -- resolution 117,73
  have eq151 : (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ a = sk1 := resolve eq117 rule_def_1_0 -- resolution 117,72
  have eq152 : (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq151 rule_def_0_0 -- subsumption resolution 151,68
  have eq171 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq130 rule_def_0_2 -- resolution 130,70
  have eq172 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq130 rule_def_0_1 -- resolution 130,69
  have eq193 : (old sk0 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq140 rule_def_0_2 -- resolution 140,70
  have eq194 : (old sk0 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq140 rule_def_0_1 -- resolution 140,69
  have eq222 (X0 X1 X2 : G) : a = (sF0 X0 X1 X2) ∨ ¬(old a a b) ∨ ¬(sP1 X0 X1 X2) ∨ ¬(sP1 X0 X1 X2) := resolve eq109 rule_def_1_2 -- resolution 109,74
  have eq225 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old a a b) ∨ a = (sF0 X0 X1 X2) := resolve eq222 rfl -- duplicate literal removal 222
  have eq226 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq150 rule_def_0_2 -- resolution 150,70
  have eq227 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ b = sk2 := resolve eq150 rule_def_0_1 -- resolution 150,69
  have eq235 (X0 X1 : G) : ¬(old X0 sk3 X1) ∨ c = sk3 ∨ (old X0 X1 sk1) ∨ c = sk2 ∨ ¬(old X0 sk1 sk2) := resolve eq226 old_1 -- resolution 226,60
  have eq257 : (new a c sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk3 := resolve eq149 rule_def_0_2 -- resolution 149,70
  have eq258 : (new a c sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk2 := resolve eq149 rule_def_0_1 -- resolution 149,69
  have eq289 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ (sP0 a c sk3) ∨ (old a c sk3) ∨ (sP1 a c sk3) := resolve eq257 new_imp -- resolution 257,77
  have eq291 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) := resolve eq289 p4XZ -- subsumption resolution 289,57
  have eq292 : (sP1 a c sk3) ∨ c = sk3 ∨ (old sk1 sk2 sk3) := resolve eq291 rule_def_0_2 -- subsumption resolution 291,70
  have eq294 : (old sk1 sk2 sk3) ∨ b = sk2 ∨ (sP0 a c sk3) ∨ (old a c sk3) ∨ (sP1 a c sk3) := resolve eq258 new_imp -- resolution 258,77
  have eq296 : (sP1 a c sk3) ∨ b = sk2 ∨ (sP0 a c sk3) ∨ (old sk1 sk2 sk3) := resolve eq294 p4XZ -- subsumption resolution 294,57
  have eq806 : c = sk3 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk3 ∨ c = sk4 := resolve eq235 eq193 -- resolution 235,193
  have eq807 : c = sk3 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ a = sk0 := resolve eq235 eq142 -- resolution 235,142
  have eq808 : c = sk3 ∨ (old sk0 sk4 sk1) ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk4 := resolve eq806 rfl -- duplicate literal removal 806
  have eq810 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk2 ∨ a = sk0 := resolve eq807 eq132 -- subsumption resolution 807,132
  have eq820 : c = sk3 ∨ c = sk2 ∨ a = sk0 ∨ (new sk0 sk4 sk1) := resolve eq810 imp_new_0 -- resolution 810,66
  have eq827 : c = sk3 ∨ c = sk2 ∨ a = sk0 := resolve eq820 preserve_3 -- subsumption resolution 820,82
  have eq838 : (sP1 sk0 c sk4) ∨ (old sk0 c sk4) ∨ (sP0 sk0 c sk4) ∨ c = sk2 ∨ a = sk0 := Or.assoc3 (eq827.imp_left (fun h : c = sk3 ↦ superpose h eq116)) -- superposition 116,827, 827 into 116, unify on (0).2 in 827 and (0).2 in 116
  have eq893 : (sP1 sk0 c sk4) ∨ (sP0 sk0 c sk4) ∨ c = sk2 ∨ a = sk0 := resolve eq838 p4XZ -- subsumption resolution 838,57
  have eq894 : (sP1 sk0 c sk4) ∨ c = sk2 ∨ a = sk0 := resolve eq893 rule_def_0_0 -- subsumption resolution 893,68
  have eq895 : c = sk2 ∨ a = sk0 := resolve eq894 rule_def_1_0 -- subsumption resolution 894,72
  have eq911 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := Or.assoc3 (eq895.imp_left (fun h : c = sk2 ↦ superpose h eq115)) -- superposition 115,895, 895 into 115, unify on (0).2 in 895 and (0).3 in 115
  have eq959 : (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq911 eq91 -- subsumption resolution 911,91
  have eq960 : (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq959 p4XY -- subsumption resolution 959,56
  have eq961 : a = sk0 := resolve eq960 rule_def_0_0 -- subsumption resolution 960,68
  have eq964 : ¬(new a sk4 sk1) := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 82,961
  have eq966 : ∀ (X0 : G) , ¬(new a sk3 X0) ∨ sk4 = X0 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq97 -- backward demodulation 97,961
  have eq968 : (sP0 a sk3 sk4) ∨ (sP1 sk0 sk3 sk4) ∨ (old sk0 sk3 sk4) := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq116 -- backward demodulation 116,961
  have eq977 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq171 -- backward demodulation 171,961
  have eq978 : (old a sk1 sk2) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq172 -- backward demodulation 172,961
  have eq990 : (old a sk3 sk4) ∨ c = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq194 -- backward demodulation 194,961
  have eq1120 : (old a sk4 sk1) ∨ c = sk3 ∨ c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk4 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq808 -- backward demodulation 808,961
  have eq1125 : (sP1 a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (old sk0 sk3 sk4) := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq968 -- forward demodulation 968,961
  have eq1126 : (sP1 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP0 a sk3 sk4) := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1125 -- forward demodulation 1125,961
  have eq1238 : ¬(old a sk1 sk2) ∨ (old a sk4 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 := Eq.mp (by simp only [eq961, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1120 -- forward demodulation 1120,961
  have eq1250 (X0 X1 : G) : ¬(sP1 X0 X1 sk3) ∨ sk4 = (sF0 X0 X1 sk3) := resolve eq966 eq90 -- resolution 966,90
  have eq1269 : (sP0 a c sk3) ∨ b = sk2 ∨ sk4 = (sF0 a c sk3) ∨ (old sk1 sk2 sk3) := resolve eq1250 eq296 -- resolution 1250,296
  have eq1276 : ¬(old sk1 sk2 b) ∨ c = sk2 ∨ c = sk1 ∨ (new a c sk1) := resolve eq977 eq87 -- resolution 977,87
  have eq1870 : (old a sk4 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq1238 eq977 -- resolution 1238,977
  have eq1871 : (old a sk4 sk1) ∨ c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk1 := resolve eq1870 rfl -- duplicate literal removal 1870
  have eq1888 : c = sk3 ∨ c = sk2 ∨ c = sk4 ∨ c = sk1 ∨ (new a sk4 sk1) := resolve eq1871 imp_new_0 -- resolution 1871,66
  have eq1894 : c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq1888 eq964 -- subsumption resolution 1888,964
  have eq1896 : ¬(new a c sk1) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := eq1894.imp_left (fun h : c = sk4 ↦ superpose h eq964) -- superposition 964,1894, 1894 into 964, unify on (0).2 in 1894 and (0).2 in 964
  have eq1897 : (old a sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq1894.imp_left (fun h : c = sk4 ↦ superpose h eq990)) -- superposition 990,1894, 1894 into 990, unify on (0).2 in 1894 and (0).3 in 990
  have eq1920 : (old a sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1897 rfl -- duplicate literal removal 1897
  have eq1921 : b = sk3 ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1920 p4XY -- subsumption resolution 1920,56
  have eq1932 : (old sk1 sk2 b) ∨ c = sk2 ∨ c = b ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq1921.imp_left (fun h : b = sk3 ↦ superpose h eq226)) -- superposition 226,1921, 1921 into 226, unify on (0).2 in 1921 and (0).3 in 226
  have eq1990 : (old sk1 sk2 b) ∨ c = sk2 ∨ c = b ∨ c = sk3 ∨ c = sk1 := resolve eq1932 rfl -- duplicate literal removal 1932
  have eq1993 : (old sk1 sk2 b) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq1990 bc -- subsumption resolution 1990,54
  have eq2022 : b = sk2 ∨ sk4 = (sF0 a c sk3) ∨ (old sk1 sk2 sk3) ∨ c = b := resolve eq1269 rule_def_0_1 -- resolution 1269,69
  have eq2025 : (old sk1 sk2 sk3) ∨ sk4 = (sF0 a c sk3) ∨ b = sk2 := resolve eq2022 bc -- subsumption resolution 2022,54
  have eq2119 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk1 ∨ (new a c sk1) := resolve eq1993 eq1276 -- resolution 1993,1276
  have eq2140 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ (new a c sk1) := resolve eq2119 rfl -- duplicate literal removal 2119
  have eq2146 : c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq2140 eq1896 -- subsumption resolution 2140,1896
  have eq2156 : (old sk1 sk2 c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 := Or.assoc2 (eq2146.imp_left (fun h : c = sk3 ↦ superpose h eq152)) -- superposition 152,2146, 2146 into 152, unify on (0).2 in 2146 and (0).3 in 152
  have eq2160 : (old sk1 sk2 c) ∨ c = sk2 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq2146.imp_left (fun h : c = sk3 ↦ superpose h eq227)) -- superposition 227,2146, 2146 into 227, unify on (0).2 in 2146 and (0).3 in 227
  have eq2176 : (sP1 a c sk4) ∨ (old a c sk4) ∨ (sP0 a c sk4) ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq2146.imp_left (fun h : c = sk3 ↦ superpose h eq1126)) -- superposition 1126,2146, 2146 into 1126, unify on (0).2 in 2146 and (0).2 in 1126
  have eq2200 : (old sk1 sk2 c) ∨ c = sk2 ∨ b = sk2 ∨ c = sk1 := resolve eq2160 rfl -- duplicate literal removal 2160
  have eq2205 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq2156 p4XY -- subsumption resolution 2156,56
  have eq2206 : c = sk2 ∨ b = sk2 ∨ c = sk1 := resolve eq2200 p4XY -- subsumption resolution 2200,56
  have eq2207 : (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ c = sk2 ∨ c = sk1 := resolve eq2176 p4XZ -- subsumption resolution 2176,57
  have eq2213 : (sP1 sk1 c sk3) ∨ (old sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq2205.imp_left (fun h : c = sk2 ↦ superpose h eq117)) -- superposition 117,2205, 2205 into 117, unify on (0).2 in 2205 and (0).2 in 117
  have eq2269 : (sP1 sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 := resolve eq2213 p4XZ -- subsumption resolution 2213,57
  have eq2270 : (sP1 sk1 c sk3) ∨ a = sk1 ∨ c = sk1 := resolve eq2269 rule_def_0_0 -- subsumption resolution 2269,68
  have eq2271 : c = sk1 ∨ a = sk1 := resolve eq2270 rule_def_1_0 -- subsumption resolution 2270,72
  have eq2282 : (old c sk2 sk3) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq2271.imp_left (fun h : c = sk1 ↦ superpose h eq152)) -- superposition 152,2271, 2271 into 152, unify on (0).2 in 2271 and (0).1 in 152
  have eq2329 : a = c ∨ a = sk1 := resolve eq2282 p4YZ -- subsumption resolution 2282,58
  have eq2330 : a = sk1 := resolve eq2329 ac -- subsumption resolution 2329,53
  have eq2358 : (sP1 a c sk3) ∨ (old a sk2 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq292 -- backward demodulation 292,2330
  have eq2360 : (sP1 a c sk3) ∨ (old a sk2 sk3) ∨ b = sk2 ∨ (sP0 a c sk3) := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq296 -- backward demodulation 296,2330
  have eq2387 : ¬(new a sk4 a) := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq964 -- backward demodulation 964,2330
  have eq2389 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq977 -- backward demodulation 977,2330
  have eq2390 : a = c ∨ (old a sk1 sk2) ∨ b = sk1 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq978 -- backward demodulation 978,2330
  have eq2627 : (old a sk2 sk3) ∨ sk4 = (sF0 a c sk3) ∨ b = sk2 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2025 -- backward demodulation 2025,2330
  have eq2655 : a = c ∨ c = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2206 -- backward demodulation 2206,2330
  have eq2656 : a = c ∨ (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ c = sk2 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2207 -- backward demodulation 2207,2330
  have eq2694 : (old a sk1 sk2) ∨ c = sk2 := resolve eq2389 ac -- subsumption resolution 2389,53
  have eq2695 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2694 -- forward demodulation 2694,2330
  have eq2696 : (old a sk1 sk2) ∨ b = sk1 := resolve eq2390 ac -- subsumption resolution 2390,53
  have eq2697 : (old a a sk2) ∨ b = sk1 := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2696 -- forward demodulation 2696,2330
  have eq2698 : (old a a sk2) ∨ a = b := Eq.mp (by simp only [eq2330, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2697 -- forward demodulation 2697,2330
  have eq3015 : b = sk2 ∨ c = sk2 := resolve eq2655 ac -- subsumption resolution 2655,53
  have eq3016 : (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ c = sk2 := resolve eq2656 ac -- subsumption resolution 2656,53
  have eq3058 : (old a a b) ∨ c = b ∨ c = sk2 := Or.assoc2 (eq3015.imp_left (fun h : b = sk2 ↦ superpose h eq2695)) -- superposition 2695,3015, 3015 into 2695, unify on (0).2 in 3015 and (0).3 in 2695
  have eq3059 : (old a a b) ∨ c = sk2 := resolve eq3058 bc -- subsumption resolution 3058,54
  have eq3422 : (sP0 a c sk4) ∨ c = sk2 ∨ ¬(old a a b) ∨ a = (sF0 a c sk4) := resolve eq3016 eq225 -- resolution 3016,225
  have eq3427 : (sP0 a c sk4) ∨ c = sk2 ∨ a = (sF0 a c sk4) := resolve eq3422 eq3059 -- subsumption resolution 3422,3059
  have eq3664 : c = sk2 ∨ a = (sF0 a c sk4) ∨ c = b := resolve eq3427 rule_def_0_1 -- resolution 3427,69
  have eq3668 : a = (sF0 a c sk4) ∨ c = sk2 := resolve eq3664 bc -- subsumption resolution 3664,54
  have eq3676 : (new a sk4 a) ∨ ¬(sP1 a c sk4) ∨ c = sk2 := Or.assoc2 (eq3668.imp_left (fun h : a = (sF0 a c sk4) ↦ superpose h eq90)) -- superposition 90,3668, 3668 into 90, unify on (0).2 in 3668 and (0).3 in 90
  have eq3718 : ¬(sP1 a c sk4) ∨ c = sk2 := resolve eq3676 eq2387 -- subsumption resolution 3676,2387
  have eq3722 : c = sk2 ∨ (sP0 a c sk4) ∨ c = sk2 := resolve eq3718 eq3016 -- resolution 3718,3016
  have eq3727 : (sP0 a c sk4) ∨ c = sk2 := resolve eq3722 rfl -- duplicate literal removal 3722
  have eq3729 : c = sk2 ∨ c = b := resolve eq3727 rule_def_0_1 -- resolution 3727,69
  have eq3733 : c = sk2 := resolve eq3729 bc -- subsumption resolution 3729,54
  have eq3741 : (old a c sk3) ∨ (sP1 a c sk3) ∨ c = sk3 := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2358 -- backward demodulation 2358,3733
  have eq3743 : c = b ∨ (sP1 a c sk3) ∨ (old a sk2 sk3) ∨ (sP0 a c sk3) := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2360 -- backward demodulation 2360,3733
  have eq3771 : c = b ∨ (old a sk2 sk3) ∨ sk4 = (sF0 a c sk3) := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2627 -- backward demodulation 2627,3733
  have eq3796 : (old a a c) ∨ a = b := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2698 -- backward demodulation 2698,3733
  have eq3856 : (sP1 a c sk3) ∨ c = sk3 := resolve eq3741 p4XZ -- subsumption resolution 3741,57
  have eq3857 : (sP1 a c sk3) ∨ (old a sk2 sk3) ∨ (sP0 a c sk3) := resolve eq3743 bc -- subsumption resolution 3743,54
  have eq3858 : (old a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3857 -- forward demodulation 3857,3733
  have eq3859 : (sP1 a c sk3) ∨ (sP0 a c sk3) := resolve eq3858 p4XZ -- subsumption resolution 3858,57
  have eq3894 : (old a sk2 sk3) ∨ sk4 = (sF0 a c sk3) := resolve eq3771 bc -- subsumption resolution 3771,54
  have eq3895 : (old a c sk3) ∨ sk4 = (sF0 a c sk3) := Eq.mp (by simp only [eq3733, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3894 -- forward demodulation 3894,3733
  have eq3896 : sk4 = (sF0 a c sk3) := resolve eq3895 p4XZ -- subsumption resolution 3895,57
  have eq3938 : a = b := resolve eq3796 p4XY -- subsumption resolution 3796,56
  have eq3941 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq3938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 69,3938
  have eq3949 : ∀ (X0 X1 X2 : G) , (old a (sF0 X0 X1 X2) a) ∨ ¬(old b X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq3938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq102 -- backward demodulation 102,3938
  have eq4004 : ∀ (X0 X1 X2 : G) , ¬(old a X2 (sF0 X0 X1 X2)) ∨ (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq3938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3949 -- forward demodulation 3949,3938
  have eq4005 (X0 X1 X2 : G) : (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := resolve eq4004 rule_def_1_2 -- subsumption resolution 4004,74
  have eq4150 (X0 X1 X2 : G) : (new a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := resolve eq4005 imp_new_0 -- resolution 4005,66
  have eq4202 : (new a sk4 a) ∨ ¬(sP1 a c sk3) := superpose eq3896 eq4150 -- superposition 4150,3896, 3896 into 4150, unify on (0).2 in 3896 and (0).2 in 4150
  have eq4204 : ¬(sP1 a c sk3) := resolve eq4202 eq2387 -- subsumption resolution 4202,2387
  have eq4206 : c = sk3 := resolve eq4204 eq3856 -- resolution 4204,3856
  have eq4232 : (sP0 a c c) ∨ (sP1 a c sk3) := Eq.mp (by simp only [eq4206, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3859 -- backward demodulation 3859,4206
  have eq4312 : (sP1 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq4206, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4232 -- forward demodulation 4232,4206
  have eq4313 : (sP0 a c c) := resolve eq4312 eq91 -- subsumption resolution 4312,91
  have eq4380 : a = c := resolve eq4313 eq3941 -- resolution 4313,3941
  subsumption ac eq4380 -- subsumption resolution 4380,53

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ ¬ old X1 X1 X0 ∨ X1 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1, ¬ new X0 X1 X1 ∨ ¬ new X1 X1 X0 ∨ X1 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq114 : (sP1 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) := resolve new_imp preserve_0 -- resolution 78,81
  have eq115 : (sP1 sk1 sk1 sk0) ∨ (old sk1 sk1 sk0) ∨ (sP0 sk1 sk1 sk0) := resolve new_imp preserve_1 -- resolution 78,82
  have eq133 : (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ c = sk1 := resolve eq114 rule_def_1_1 -- resolution 114,74
  have eq134 : (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ a = sk0 := resolve eq114 rule_def_1_0 -- resolution 114,73
  have eq135 : (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq133 rule_def_0_2 -- subsumption resolution 133,71
  have eq136 : (old sk0 sk1 sk1) ∨ a = sk0 := resolve eq134 rule_def_0_0 -- subsumption resolution 134,69
  have eq138 : (old sk1 sk1 sk0) ∨ (sP0 sk1 sk1 sk0) ∨ c = sk1 := resolve eq115 rule_def_1_1 -- resolution 115,74
  have eq139 : (old sk1 sk1 sk0) ∨ (sP0 sk1 sk1 sk0) ∨ a = sk1 := resolve eq115 rule_def_1_0 -- resolution 115,73
  have eq140 : (old sk1 sk1 sk0) ∨ a = sk1 := resolve eq139 rule_def_0_0 -- subsumption resolution 139,69
  have eq165 : a = sk1 ∨ sk0 = sk1 ∨ ¬(old sk0 sk1 sk1) := resolve eq140 old_2 -- resolution 140,62
  have eq166 : ¬(old sk0 sk1 sk1) ∨ a = sk1 := resolve eq165 preserve_2 -- subsumption resolution 165,83
  have eq168 : a = sk1 ∨ a = sk0 := resolve eq166 eq136 -- resolution 166,136
  have eq169 : c = sk1 ∨ a = sk1 := resolve eq166 eq135 -- resolution 166,135
  have eq177 : (sP1 sk0 a a) ∨ (old sk0 a a) ∨ (sP0 sk0 a a) ∨ a = sk0 := Or.assoc3 (eq168.imp_left (fun h : a = sk1 ↦ superpose h eq114)) -- superposition 114,168, 168 into 114, unify on (0).2 in 168 and (0).2 in 114
  have eq184 : (sP1 sk0 a a) ∨ (old sk0 a a) ∨ a = sk0 := resolve eq177 rule_def_0_0 -- subsumption resolution 177,69
  have eq185 : (old sk0 a a) ∨ a = sk0 := resolve eq184 rule_def_1_0 -- subsumption resolution 184,73
  have eq199 : (old c c sk0) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq169.imp_left (fun h : c = sk1 ↦ superpose h eq140)) -- superposition 140,169, 169 into 140, unify on (0).2 in 169 and (0).1 in 140
  have eq206 : a = c ∨ a = sk1 := resolve eq199 p4YZ -- subsumption resolution 199,59
  have eq207 : a = sk1 := resolve eq206 ac -- subsumption resolution 206,54
  have eq210 : a ≠ sk0 := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 83,207
  have eq218 : (old sk0 a a) ∨ c = sk1 := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq135 -- backward demodulation 135,207
  have eq221 : (sP0 a a sk0) ∨ (old sk1 sk1 sk0) ∨ c = sk1 := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq138 -- backward demodulation 138,207
  have eq253 : a = c ∨ (old sk0 a a) := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq218 -- forward demodulation 218,207
  have eq254 : (old sk0 a a) := resolve eq253 ac -- subsumption resolution 253,54
  have eq256 : (old a a sk0) ∨ (sP0 a a sk0) ∨ c = sk1 := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq221 -- forward demodulation 221,207
  have eq257 : a = c ∨ (old a a sk0) ∨ (sP0 a a sk0) := Eq.mp (by simp only [eq207, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq256 -- forward demodulation 256,207
  have eq258 : (sP0 a a sk0) ∨ (old a a sk0) := resolve eq257 ac -- subsumption resolution 257,54
  have eq339 : (old a a sk0) ∨ c = sk0 := resolve eq258 rule_def_0_2 -- resolution 258,71
  have eq343 : c = sk0 ∨ a = sk0 ∨ ¬(old sk0 a a) := resolve eq339 old_2 -- resolution 339,62
  have eq350 : c = sk0 ∨ ¬(old sk0 a a) := resolve eq343 eq210 -- subsumption resolution 343,210
  have eq351 : c = sk0 := resolve eq350 eq254 -- subsumption resolution 350,254
  have eq360 : a = c ∨ (old sk0 a a) := Eq.mp (by simp only [eq351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq185 -- backward demodulation 185,351
  have eq405 : (old sk0 a a) := resolve eq360 ac -- subsumption resolution 360,54
  have eq406 : (old c a a) := Eq.mp (by simp only [eq351, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq405 -- forward demodulation 405,351
  subsumption p4YZ eq406 -- subsumption resolution 406,59

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X0 ∨ old X0 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X0 ∨ new X0 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq122 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 80,84
  have eq123 : (sP1 sk1 sk2 sk0) ∨ (old sk1 sk2 sk0) ∨ (sP0 sk1 sk2 sk0) := resolve new_imp preserve_1 -- resolution 80,85
  have eq135 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq122 rule_def_1_1 -- resolution 122,76
  have eq136 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq122 rule_def_1_0 -- resolution 122,75
  have eq137 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq136 rule_def_0_0 -- subsumption resolution 136,71
  have eq147 : (sP0 sk1 sk2 sk0) ∨ (old sk1 sk2 sk0) ∨ c = sk2 := resolve eq123 rule_def_1_1 -- resolution 123,76
  have eq148 : (old sk1 sk2 sk0) ∨ (sP0 sk1 sk2 sk0) ∨ a = sk1 := resolve eq123 rule_def_1_0 -- resolution 123,75
  have eq149 : (old sk1 sk2 sk0) ∨ a = sk1 := resolve eq148 rule_def_0_0 -- subsumption resolution 148,71
  have eq153 : ¬(old sk0 sk1 sk2) ∨ (old sk0 sk2 sk0) ∨ a = sk1 := resolve eq149 old_3 -- resolution 149,65
  have eq169 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq135 rule_def_0_2 -- resolution 135,73
  have eq186 : (old sk1 sk2 sk0) ∨ c = sk2 ∨ c = sk0 := resolve eq147 rule_def_0_2 -- resolution 147,73
  have eq195 : c = sk2 ∨ c = sk0 ∨ (old sk0 sk2 sk0) ∨ ¬(old sk0 sk1 sk2) := resolve eq186 old_3 -- resolution 186,65
  have eq221 : (old sk0 sk2 sk0) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq153 eq169 -- resolution 153,169
  have eq222 : (old sk0 sk2 sk0) ∨ a = sk1 ∨ a = sk0 := resolve eq153 eq137 -- resolution 153,137
  have eq232 : a = sk1 ∨ a = sk0 ∨ (new sk0 sk2 sk0) := resolve eq222 imp_new_0 -- resolution 222,69
  have eq233 : a = sk1 ∨ a = sk0 := resolve eq232 preserve_2 -- subsumption resolution 232,86
  have eq242 : (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ a = sk0 := Or.assoc3 (eq233.imp_left (fun h : a = sk1 ↦ superpose h eq122)) -- superposition 122,233, 233 into 122, unify on (0).2 in 233 and (0).2 in 122
  have eq258 : (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ a = sk0 := resolve eq242 rule_def_0_0 -- subsumption resolution 242,71
  have eq259 : (old sk0 a sk2) ∨ a = sk0 := resolve eq258 rule_def_1_0 -- subsumption resolution 258,75
  have eq474 : a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ (new sk0 sk2 sk0) := resolve eq221 imp_new_0 -- resolution 221,69
  have eq475 : c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq474 preserve_2 -- subsumption resolution 474,86
  have eq490 : (sP1 sk1 c sk0) ∨ (old sk1 c sk0) ∨ (sP0 sk1 c sk0) ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq475.imp_left (fun h : c = sk2 ↦ superpose h eq123)) -- superposition 123,475, 475 into 123, unify on (0).2 in 475 and (0).2 in 123
  have eq528 : (sP1 sk1 c sk0) ∨ (sP0 sk1 c sk0) ∨ c = sk1 ∨ a = sk1 := resolve eq490 p4XZ -- subsumption resolution 490,60
  have eq529 : (sP1 sk1 c sk0) ∨ c = sk1 ∨ a = sk1 := resolve eq528 rule_def_0_0 -- subsumption resolution 528,71
  have eq530 : c = sk1 ∨ a = sk1 := resolve eq529 rule_def_1_0 -- subsumption resolution 529,75
  have eq552 : (old c sk2 sk0) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq530.imp_left (fun h : c = sk1 ↦ superpose h eq149)) -- superposition 149,530, 530 into 149, unify on (0).2 in 530 and (0).1 in 149
  have eq570 : a = c ∨ a = sk1 := resolve eq552 p4YZ -- subsumption resolution 552,61
  have eq571 : a = sk1 := resolve eq570 ac -- subsumption resolution 570,56
  have eq573 : (new a sk2 sk0) := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 85,571
  have eq597 : (old sk0 a sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq169 -- backward demodulation 169,571
  have eq614 : ¬(old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 ∨ (old sk0 sk2 sk0) := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq195 -- backward demodulation 195,571
  have eq741 : a = c ∨ (old sk0 a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq597 -- forward demodulation 597,571
  have eq742 : (old sk0 a sk2) ∨ c = sk2 := resolve eq741 ac -- subsumption resolution 741,56
  have eq777 : (old sk0 sk2 sk0) ∨ c = sk0 ∨ c = sk2 := resolve eq614 eq742 -- subsumption resolution 614,742
  have eq908 : c = sk0 ∨ c = sk2 ∨ (new sk0 sk2 sk0) := resolve eq777 imp_new_0 -- resolution 777,69
  have eq909 : c = sk2 ∨ c = sk0 := resolve eq908 preserve_2 -- subsumption resolution 908,86
  have eq920 : (old sk0 a c) ∨ a = sk0 ∨ c = sk0 := Or.assoc2 (eq909.imp_left (fun h : c = sk2 ↦ superpose h eq259)) -- superposition 259,909, 909 into 259, unify on (0).2 in 909 and (0).3 in 259
  have eq933 : c = sk0 ∨ a = sk0 := resolve eq920 p4XY -- subsumption resolution 920,59
  have eq1067 : (old c a sk2) ∨ a = c ∨ a = sk0 := Or.assoc2 (eq933.imp_left (fun h : c = sk0 ↦ superpose h eq259)) -- superposition 259,933, 933 into 259, unify on (0).2 in 933 and (0).1 in 259
  have eq1090 : a = c ∨ a = sk0 := resolve eq1067 p4YZ -- subsumption resolution 1067,61
  have eq1091 : a = sk0 := resolve eq1090 ac -- subsumption resolution 1090,56
  have eq1092 : ¬(new a sk2 a) := Eq.mp (by simp only [eq1091, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 86,1091
  have eq1099 : (new a sk2 a) := Eq.mp (by simp only [eq1091, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq573 -- backward demodulation 573,1091
  subsumption eq1092 eq1099 -- subsumption resolution 1099,1092

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X4 ∨ ¬ new X1 X2 X3 ∨ new X0 X4 X1)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X2 X3 ∨ ¬ old X2 X3 X1 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X2 X3 ∨ ¬ new X2 X3 X1 ∨ X3 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq100 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4XZ -- resolution 80,63
  have eq105 (X0 : G) : ¬(new sk0 sk0 X0) ∨ sk1 = X0 := resolve prev_0 preserve_0 -- resolution 84,88
  have eq106 (X0 : G) : ¬(new sk0 sk2 X0) ∨ sk3 = X0 := resolve prev_0 preserve_1 -- resolution 84,89
  have eq127 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 83,88
  have eq128 : (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) := resolve new_imp preserve_1 -- resolution 83,89
  have eq129 : (sP1 sk2 sk3 sk1) ∨ (old sk2 sk3 sk1) ∨ (sP0 sk2 sk3 sk1) := resolve new_imp preserve_2 -- resolution 83,90
  have eq138 (X0 X1 : G) : ¬(new X0 sk2 sk3) ∨ ¬(new X0 sk1 X1) ∨ (new X0 X1 sk2) := resolve prev_1 preserve_2 -- resolution 85,90
  have eq153 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq127 rule_def_1_1 -- resolution 127,79
  have eq154 : (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ a = sk0 := resolve eq127 rule_def_1_0 -- resolution 127,78
  have eq155 : (old sk0 sk0 sk1) ∨ a = sk0 := resolve eq154 rule_def_0_0 -- subsumption resolution 154,74
  have eq164 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk2 := resolve eq128 rule_def_1_1 -- resolution 128,79
  have eq165 : (old sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ a = sk0 := resolve eq128 rule_def_1_0 -- resolution 128,78
  have eq166 : (old sk0 sk2 sk3) ∨ a = sk0 := resolve eq165 rule_def_0_0 -- subsumption resolution 165,74
  have eq174 : (sP0 sk2 sk3 sk1) ∨ (old sk2 sk3 sk1) ∨ c = sk3 := resolve eq129 rule_def_1_1 -- resolution 129,79
  have eq175 : (old sk2 sk3 sk1) ∨ (sP0 sk2 sk3 sk1) ∨ a = sk2 := resolve eq129 rule_def_1_0 -- resolution 129,78
  have eq176 : (old sk2 sk3 sk1) ∨ a = sk2 := resolve eq175 rule_def_0_0 -- subsumption resolution 175,74
  have eq179 (X0 : G) : ¬(old X0 sk2 sk3) ∨ sk3 = X0 ∨ a = sk2 ∨ ¬(old X0 X0 sk1) := resolve eq176 old_4 -- resolution 176,69
  have eq188 (X0 : G) : ¬(new sk0 sk1 X0) ∨ (new sk0 X0 sk2) := resolve eq138 preserve_1 -- resolution 138,89
  have eq200 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq153 rule_def_0_2 -- resolution 153,76
  have eq201 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ b = sk0 := resolve eq153 rule_def_0_1 -- resolution 153,75
  have eq221 : (old sk0 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq164 rule_def_0_2 -- resolution 164,76
  have eq253 : (old sk2 sk3 sk1) ∨ c = sk3 ∨ c = sk1 := resolve eq174 rule_def_0_2 -- resolution 174,76
  have eq263 (X0 : G) : ¬(old X0 sk2 sk3) ∨ c = sk1 ∨ sk3 = X0 ∨ c = sk3 ∨ ¬(old X0 X0 sk1) := resolve eq253 old_4 -- resolution 253,69
  have eq463 : sk0 = sk3 ∨ a = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk2 ∨ c = sk3 := resolve eq179 eq221 -- resolution 179,221
  have eq466 : ¬(old sk0 sk0 sk1) ∨ a = sk2 ∨ c = sk2 ∨ c = sk3 := resolve eq463 preserve_3 -- subsumption resolution 463,91
  have eq553 : c = sk3 ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq466 eq201 -- resolution 466,201
  have eq1092 : (sP1 sk2 c sk1) ∨ (old sk2 c sk1) ∨ (sP0 sk2 c sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := Or.assoc3 (eq553.imp_left (fun h : c = sk3 ↦ superpose h eq129)) -- superposition 129,553, 553 into 129, unify on (0).2 in 553 and (0).2 in 129
  have eq1146 : (sP1 sk2 c sk1) ∨ (sP0 sk2 c sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1092 p4XZ -- subsumption resolution 1092,63
  have eq1147 : (sP1 sk2 c sk1) ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1146 rule_def_0_0 -- subsumption resolution 1146,74
  have eq1148 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1147 rule_def_1_0 -- subsumption resolution 1147,78
  have eq1168 : (old c sk3 sk1) ∨ a = c ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := Or.assoc2 (eq1148.imp_left (fun h : c = sk2 ↦ superpose h eq176)) -- superposition 176,1148, 1148 into 176, unify on (0).2 in 1148 and (0).1 in 176
  have eq1191 : a = c ∨ a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1168 p4YZ -- subsumption resolution 1168,64
  have eq1192 : a = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1191 ac -- subsumption resolution 1191,59
  have eq1198 : (new sk0 a sk3) ∨ c = sk0 ∨ b = sk0 := eq1192.imp_left (fun h : a = sk2 ↦ superpose h preserve_1) -- superposition 89,1192, 1192 into 89, unify on (0).2 in 1192 and (0).2 in 89
  have eq1199 : (new a sk3 sk1) ∨ c = sk0 ∨ b = sk0 := eq1192.imp_left (fun h : a = sk2 ↦ superpose h preserve_2) -- superposition 90,1192, 1192 into 90, unify on (0).2 in 1192 and (0).1 in 90
  have eq1293 : c = sk1 ∨ sk0 = sk3 ∨ c = sk3 ∨ ¬(old sk0 sk0 sk1) ∨ a = sk0 := resolve eq263 eq166 -- resolution 263,166
  have eq1303 : c = sk1 ∨ c = sk3 ∨ ¬(old sk0 sk0 sk1) ∨ a = sk0 := resolve eq1293 preserve_3 -- subsumption resolution 1293,91
  have eq1304 : c = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq1303 eq155 -- subsumption resolution 1303,155
  have eq1311 : (sP1 sk0 sk2 c) ∨ (old sk0 sk2 c) ∨ (sP0 sk0 sk2 c) ∨ c = sk1 ∨ a = sk0 := Or.assoc3 (eq1304.imp_left (fun h : c = sk3 ↦ superpose h eq128)) -- superposition 128,1304, 1304 into 128, unify on (0).2 in 1304 and (0).3 in 128
  have eq1373 : (old sk0 sk2 c) ∨ (sP0 sk0 sk2 c) ∨ c = sk1 ∨ a = sk0 := resolve eq1311 eq100 -- subsumption resolution 1311,100
  have eq1374 : (sP0 sk0 sk2 c) ∨ c = sk1 ∨ a = sk0 := resolve eq1373 p4XY -- subsumption resolution 1373,62
  have eq1375 : c = sk1 ∨ a = sk0 := resolve eq1374 rule_def_0_0 -- subsumption resolution 1374,74
  have eq1394 : (sP1 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk0 := Or.assoc3 (eq1375.imp_left (fun h : c = sk1 ↦ superpose h eq127)) -- superposition 127,1375, 1375 into 127, unify on (0).2 in 1375 and (0).3 in 127
  have eq1462 : (old sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk0 := resolve eq1394 eq100 -- subsumption resolution 1394,100
  have eq1463 : (sP0 sk0 sk0 c) ∨ a = sk0 := resolve eq1462 p4XY -- subsumption resolution 1462,62
  have eq1464 : a = sk0 := resolve eq1463 rule_def_0_0 -- subsumption resolution 1463,74
  have eq1467 : a ≠ sk3 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 91,1464
  have eq1468 : ∀ (X0 : G) , ¬(new a a X0) ∨ sk1 = X0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq105 -- backward demodulation 105,1464
  have eq1469 : ∀ (X0 : G) , ¬(new a sk2 X0) ∨ sk3 = X0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq106 -- backward demodulation 106,1464
  have eq1487 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ (new sk0 X0 sk2) := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188 -- backward demodulation 188,1464
  have eq1490 : (old a a sk1) ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq200 -- backward demodulation 200,1464
  have eq1504 : (old a sk2 sk3) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq221 -- backward demodulation 221,1464
  have eq1758 : a = c ∨ a = sk2 ∨ b = sk0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1192 -- backward demodulation 1192,1464
  have eq1759 : a = c ∨ (new sk0 a sk3) ∨ b = sk0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1198 -- backward demodulation 1198,1464
  have eq1760 : a = c ∨ (new a sk3 sk1) ∨ b = sk0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1199 -- backward demodulation 1199,1464
  have eq1815 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ (new a X0 sk2) := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1487 -- forward demodulation 1487,1464
  have eq1820 : a = c ∨ (old a a sk1) ∨ c = sk1 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1490 -- forward demodulation 1490,1464
  have eq1821 : (old a a sk1) ∨ c = sk1 := resolve eq1820 ac -- subsumption resolution 1820,59
  have eq2238 : a = sk2 ∨ b = sk0 := resolve eq1758 ac -- subsumption resolution 1758,59
  have eq2239 : a = sk2 ∨ a = b := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2238 -- forward demodulation 2238,1464
  have eq2240 : (new sk0 a sk3) ∨ b = sk0 := resolve eq1759 ac -- subsumption resolution 1759,59
  have eq2241 : (new a a sk3) ∨ b = sk0 := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2240 -- forward demodulation 2240,1464
  have eq2242 : (new a a sk3) ∨ a = b := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2241 -- forward demodulation 2241,1464
  have eq2243 : (new a sk3 sk1) ∨ b = sk0 := resolve eq1760 ac -- subsumption resolution 1760,59
  have eq2244 : (new a sk3 sk1) ∨ a = b := Eq.mp (by simp only [eq1464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2243 -- forward demodulation 2243,1464
  have eq2405 : sk1 = sk3 ∨ a = b := resolve eq2242 eq1468 -- resolution 2242,1468
  have eq2469 : (new a sk1 sk1) ∨ a = b ∨ a = b := Or.assoc2 (eq2405.imp_left (fun h : sk1 = sk3 ↦ superpose h eq2244)) -- superposition 2244,2405, 2405 into 2244, unify on (0).2 in 2405 and (0).2 in 2244
  have eq2470 : (new a sk1 sk1) ∨ a = b := resolve eq2469 rfl -- duplicate literal removal 2469
  have eq2513 : (new a sk1 sk2) ∨ a = b := resolve eq2470 eq1815 -- resolution 2470,1815
  have eq2536 : (new a sk2 sk2) ∨ a = b := resolve eq2513 eq1815 -- resolution 2513,1815
  have eq2554 : sk2 = sk3 ∨ a = b := resolve eq2536 eq1469 -- resolution 2536,1469
  have eq2586 : a ≠ sk2 ∨ a = b := eq2554.imp_left (fun h : sk2 = sk3 ↦ superpose h eq1467) -- superposition 1467,2554, 2554 into 1467, unify on (0).2 in 2554 and (0).2 in 1467
  have eq2607 : a = b := resolve eq2586 eq2239 -- subsumption resolution 2586,2239
  have eq2609 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq2607, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 61,2607
  have eq2610 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq2607, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 75,2607
  have eq2802 : c = sk1 := resolve eq2609 eq1821 -- resolution 2609,1821
  have eq2807 : (sP0 sk2 sk3 c) ∨ (sP1 sk2 sk3 sk1) ∨ (old sk2 sk3 sk1) := Eq.mp (by simp only [eq2802, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq129 -- backward demodulation 129,2802
  have eq2811 : (old sk2 sk3 c) ∨ a = sk2 := Eq.mp (by simp only [eq2802, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq176 -- backward demodulation 176,2802
  have eq2916 : (sP1 sk2 sk3 c) ∨ (sP0 sk2 sk3 c) ∨ (old sk2 sk3 sk1) := Eq.mp (by simp only [eq2802, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2807 -- forward demodulation 2807,2802
  have eq2917 : (sP0 sk2 sk3 c) ∨ (old sk2 sk3 sk1) := resolve eq2916 eq100 -- subsumption resolution 2916,100
  have eq2918 : (old sk2 sk3 c) ∨ (sP0 sk2 sk3 c) := Eq.mp (by simp only [eq2802, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2917 -- forward demodulation 2917,2802
  have eq2919 : (sP0 sk2 sk3 c) := resolve eq2918 p4XY -- subsumption resolution 2918,62
  have eq2920 : a = sk2 := resolve eq2811 p4XY -- subsumption resolution 2811,62
  have eq2924 : a = c ∨ (old a sk2 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq2920, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1504 -- backward demodulation 1504,2920
  have eq2996 : (sP0 a sk3 c) := Eq.mp (by simp only [eq2920, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2919 -- backward demodulation 2919,2920
  have eq2998 : (old a sk2 sk3) ∨ c = sk3 := resolve eq2924 ac -- subsumption resolution 2924,59
  have eq2999 : (old a a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq2920, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2998 -- forward demodulation 2998,2920
  have eq3000 : c = sk3 := resolve eq2999 eq2609 -- subsumption resolution 2999,2609
  have eq3077 : (sP0 a c c) := Eq.mp (by simp only [eq3000, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2996 -- forward demodulation 2996,3000
  have eq3169 : a = c := resolve eq3077 eq2610 -- resolution 3077,2610
  subsumption ac eq3169 -- subsumption resolution 3169,59

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_5 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X2 ∨ X0 = X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X2 ∨ X0 = X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq103 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4XZ -- resolution 82,65
  have eq135 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 85,91
  have eq136 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 85,92
  have eq137 : (sP1 sk1 sk2 sk2) ∨ (old sk1 sk2 sk2) ∨ (sP0 sk1 sk2 sk2) := resolve new_imp preserve_2 -- resolution 85,93
  have eq166 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq135 rule_def_1_1 -- resolution 135,81
  have eq167 : (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ a = sk0 := resolve eq135 rule_def_1_0 -- resolution 135,80
  have eq168 : (old sk0 sk0 sk1) ∨ a = sk0 := resolve eq167 rule_def_0_0 -- subsumption resolution 167,76
  have eq170 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq136 rule_def_1_1 -- resolution 136,81
  have eq171 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq136 rule_def_1_0 -- resolution 136,80
  have eq172 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq171 rule_def_0_0 -- subsumption resolution 171,76
  have eq182 : (old sk1 sk2 sk2) ∨ (sP0 sk1 sk2 sk2) ∨ c = sk2 := resolve eq137 rule_def_1_1 -- resolution 137,81
  have eq183 : (old sk1 sk2 sk2) ∨ (sP0 sk1 sk2 sk2) ∨ a = sk1 := resolve eq137 rule_def_1_0 -- resolution 137,80
  have eq184 : (old sk1 sk2 sk2) ∨ c = sk2 := resolve eq182 rule_def_0_2 -- subsumption resolution 182,78
  have eq185 : (old sk1 sk2 sk2) ∨ a = sk1 := resolve eq183 rule_def_0_0 -- subsumption resolution 183,76
  have eq200 (X0 : G) : ¬(old X0 sk1 sk2) ∨ sk1 = X0 ∨ c = sk2 ∨ ¬(old X0 X0 sk1) := resolve eq184 old_5 -- resolution 184,72
  have eq234 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq166 rule_def_0_2 -- resolution 166,78
  have eq279 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq170 rule_def_0_2 -- resolution 170,78
  have eq487 : sk0 = sk1 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk2 := resolve eq200 eq279 -- resolution 200,279
  have eq488 : sk0 = sk1 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ a = sk0 := resolve eq200 eq172 -- resolution 200,172
  have eq489 : sk0 = sk1 ∨ c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk1 := resolve eq487 rfl -- duplicate literal removal 487
  have eq491 : c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ c = sk1 := resolve eq489 preserve_3 -- subsumption resolution 489,94
  have eq492 : c = sk2 ∨ ¬(old sk0 sk0 sk1) ∨ a = sk0 := resolve eq488 preserve_3 -- subsumption resolution 488,94
  have eq493 : c = sk2 ∨ a = sk0 := resolve eq492 eq168 -- subsumption resolution 492,168
  have eq500 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := Or.assoc3 (eq493.imp_left (fun h : c = sk2 ↦ superpose h eq136)) -- superposition 136,493, 493 into 136, unify on (0).2 in 493 and (0).3 in 136
  have eq529 : (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq500 eq103 -- subsumption resolution 500,103
  have eq530 : (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq529 p4XY -- subsumption resolution 529,64
  have eq531 : a = sk0 := resolve eq530 rule_def_0_0 -- subsumption resolution 530,76
  have eq534 : a ≠ sk1 := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 94,531
  have eq561 : (old a a sk1) ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq234 -- backward demodulation 234,531
  have eq662 : ¬(old a a sk1) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq491 -- backward demodulation 491,531
  have eq685 : a = c ∨ (old a a sk1) ∨ c = sk1 := Eq.mp (by simp only [eq531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq561 -- forward demodulation 561,531
  have eq686 : (old a a sk1) ∨ c = sk1 := resolve eq685 ac -- subsumption resolution 685,61
  have eq780 : c = sk2 ∨ c = sk1 := resolve eq662 eq686 -- subsumption resolution 662,686
  have eq802 : (old sk1 c c) ∨ a = sk1 ∨ c = sk1 := Or.assoc2 (eq780.imp_left (fun h : c = sk2 ↦ superpose h eq185)) -- superposition 185,780, 780 into 185, unify on (0).2 in 780 and (0).2 in 185
  have eq813 : a = sk1 ∨ c = sk1 := resolve eq802 p4XZ -- subsumption resolution 802,65
  have eq814 : c = sk1 := resolve eq813 eq534 -- subsumption resolution 813,534
  have eq823 : (old c sk2 sk2) ∨ a = sk1 := Eq.mp (by simp only [eq814, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq185 -- backward demodulation 185,814
  have eq953 : a = sk1 := resolve eq823 p4YZ -- subsumption resolution 823,66
  subsumption eq534 eq953 -- subsumption resolution 953,534

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_6_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X4 ∨ ¬ new X1 X2 X3 ∨ new X0 X4 X1)) (old_6 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X4 ∨ ¬ old X1 X2 X5 ∨ ¬ old X3 X4 X5 ∨ X1 = X3)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old a Z X2 ∨ ¬ old Z X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old Z (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X4 ∨ ¬ new X1 X2 X5 ∨ ¬ new X3 X4 X5 ∨ X1 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq100 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 78
  have eq101 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq100 rfl -- equality resolution 100
  have eq102 : (new a b c) := resolve eq101 rfl -- equality resolution 101
  have eq103 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 X3 b) ∨ ¬(old a X2 X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 82
  have eq104 (X2 X3 : G) : ¬(old a X2 X3) ∨ ¬(old X2 X3 b) ∨ (new a c X2) := resolve eq103 rfl -- equality resolution 103
  have eq107 (X0 X1 X2 : G) : (new a X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_2 imp_new_0 -- resolution 85,77
  have eq108 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4XZ -- resolution 85,68
  have eq113 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq102 -- resolution 89,102
  have eq128 (X0 X1 X2 : G) : ¬(old X0 (sF0 X1 X2 X0) b) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq104 rule_def_1_2 -- resolution 104,85
  have eq130 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq128 rule_def_1_3 -- subsumption resolution 128,86
  have eq143 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 88,95
  have eq144 : (sP1 sk0 sk3 sk4) ∨ (old sk0 sk3 sk4) ∨ (sP0 sk0 sk3 sk4) := resolve new_imp preserve_1 -- resolution 88,96
  have eq145 : (sP1 sk1 sk2 sk5) ∨ (old sk1 sk2 sk5) ∨ (sP0 sk1 sk2 sk5) := resolve new_imp preserve_2 -- resolution 88,97
  have eq146 : (sP1 sk3 sk4 sk5) ∨ (old sk3 sk4 sk5) ∨ (sP0 sk3 sk4 sk5) := resolve new_imp preserve_3 -- resolution 88,98
  have eq155 (X0 X1 : G) : ¬(new X0 sk5 X1) ∨ (new X0 X1 sk1) ∨ ¬(new X0 sk1 sk2) := resolve prev_1 preserve_2 -- resolution 90,97
  have eq156 (X0 X1 : G) : ¬(new X0 sk5 X1) ∨ (new X0 X1 sk3) ∨ ¬(new X0 sk3 sk4) := resolve prev_1 preserve_3 -- resolution 90,98
  have eq174 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq143 rule_def_1_1 -- resolution 143,84
  have eq175 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq143 rule_def_1_0 -- resolution 143,83
  have eq176 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq175 rule_def_0_0 -- subsumption resolution 175,79
  have eq178 : (sP0 sk0 sk3 sk4) ∨ (old sk0 sk3 sk4) ∨ c = sk3 := resolve eq144 rule_def_1_1 -- resolution 144,84
  have eq179 : (old sk0 sk3 sk4) ∨ (sP0 sk0 sk3 sk4) ∨ a = sk0 := resolve eq144 rule_def_1_0 -- resolution 144,83
  have eq180 : (old sk0 sk3 sk4) ∨ a = sk0 := resolve eq179 rule_def_0_0 -- subsumption resolution 179,79
  have eq187 : (sP0 sk1 sk2 sk5) ∨ (old sk1 sk2 sk5) ∨ (new a c sk5) := resolve eq145 eq130 -- resolution 145,130
  have eq188 : (sP0 sk1 sk2 sk5) ∨ (old sk1 sk2 sk5) ∨ c = sk2 := resolve eq145 rule_def_1_1 -- resolution 145,84
  have eq189 : (old sk1 sk2 sk5) ∨ (sP0 sk1 sk2 sk5) ∨ a = sk1 := resolve eq145 rule_def_1_0 -- resolution 145,83
  have eq190 : (old sk1 sk2 sk5) ∨ a = sk1 := resolve eq189 rule_def_0_0 -- subsumption resolution 189,79
  have eq197 : (sP0 sk3 sk4 sk5) ∨ (old sk3 sk4 sk5) ∨ (new a c sk5) := resolve eq146 eq130 -- resolution 146,130
  have eq198 : (sP0 sk3 sk4 sk5) ∨ (old sk3 sk4 sk5) ∨ c = sk4 := resolve eq146 rule_def_1_1 -- resolution 146,84
  have eq199 : (old sk3 sk4 sk5) ∨ (sP0 sk3 sk4 sk5) ∨ a = sk3 := resolve eq146 rule_def_1_0 -- resolution 146,83
  have eq200 : (old sk3 sk4 sk5) ∨ a = sk3 := resolve eq199 rule_def_0_0 -- subsumption resolution 199,79
  have eq201 (X0 X1 X2 : G) : ¬(old X2 sk1 sk2) ∨ sk1 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk1 ∨ ¬(old X2 X0 X1) := resolve eq190 old_6 -- resolution 190,76
  have eq209 (X0 X1 X2 : G) : ¬(old X2 sk3 sk4) ∨ sk3 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk3 ∨ ¬(old X2 X0 X1) := resolve eq200 old_6 -- resolution 200,76
  have eq217 (X0 X1 : G) : (new a (sF0 X0 X1 sk5) sk1) ∨ ¬(new a sk1 sk2) ∨ ¬(sP1 X0 X1 sk5) := resolve eq155 eq107 -- resolution 155,107
  have eq218 (X0 X1 : G) : (new a (sF0 X0 X1 sk5) sk3) ∨ ¬(new a sk3 sk4) ∨ ¬(sP1 X0 X1 sk5) := resolve eq156 eq107 -- resolution 156,107
  have eq235 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq174 rule_def_0_2 -- resolution 174,81
  have eq236 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq174 rule_def_0_1 -- resolution 174,80
  have eq254 : (old sk0 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq178 rule_def_0_2 -- resolution 178,81
  have eq255 : (old sk0 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq178 rule_def_0_1 -- resolution 178,80
  have eq287 : (old sk1 sk2 sk5) ∨ c = sk2 ∨ b = sk2 := resolve eq188 rule_def_0_1 -- resolution 188,80
  have eq315 : (old sk3 sk4 sk5) ∨ c = sk4 ∨ c = sk5 := resolve eq198 rule_def_0_2 -- resolution 198,81
  have eq338 : (new a c sk5) ∨ (old sk1 sk2 sk5) ∨ c = sk5 := resolve eq187 rule_def_0_2 -- resolution 187,81
  have eq341 : (new a c sk5) ∨ (old sk3 sk4 sk5) ∨ c = sk5 := resolve eq197 rule_def_0_2 -- resolution 197,81
  have eq403 (X0 X1 X2 : G) : ¬(new a (sF0 X0 X1 sk5) X2) ∨ ¬(sP1 X0 X1 sk5) ∨ sk1 = X2 ∨ ¬(new a sk1 sk2) := resolve eq217 prev_0 -- resolution 217,89
  have eq406 : (old sk1 sk2 sk5) ∨ c = sk5 ∨ (sP0 a c sk5) ∨ (old a c sk5) ∨ (sP1 a c sk5) := resolve eq338 new_imp -- resolution 338,88
  have eq410 : (old sk1 sk2 sk5) ∨ c = sk5 ∨ (sP0 a c sk5) ∨ (sP1 a c sk5) := resolve eq406 p4XZ -- subsumption resolution 406,68
  have eq411 : (sP1 a c sk5) ∨ c = sk5 ∨ (old sk1 sk2 sk5) := resolve eq410 rule_def_0_2 -- subsumption resolution 410,81
  have eq430 : (old sk3 sk4 sk5) ∨ c = sk5 ∨ (sP0 a c sk5) ∨ (old a c sk5) ∨ (sP1 a c sk5) := resolve eq341 new_imp -- resolution 341,88
  have eq434 : (old sk3 sk4 sk5) ∨ c = sk5 ∨ (sP0 a c sk5) ∨ (sP1 a c sk5) := resolve eq430 p4XZ -- subsumption resolution 430,68
  have eq435 : (sP1 a c sk5) ∨ c = sk5 ∨ (old sk3 sk4 sk5) := resolve eq434 rule_def_0_2 -- subsumption resolution 434,81
  have eq709 (X0 X1 : G) : sk1 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk1 ∨ ¬(old sk0 X0 X1) ∨ c = sk1 ∨ b = sk1 := resolve eq201 eq236 -- resolution 201,236
  have eq711 (X0 X1 : G) : ¬(old sk0 X0 X1) ∨ ¬(old X0 X1 sk5) ∨ a = sk1 ∨ sk1 = X0 ∨ a = sk0 := resolve eq201 eq176 -- resolution 201,176
  have eq724 (X0 X1 : G) : sk3 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk3 ∨ ¬(old sk0 X0 X1) ∨ c = sk3 ∨ b = sk3 := resolve eq209 eq255 -- resolution 209,255
  have eq726 (X0 X1 : G) : ¬(old sk0 X0 X1) ∨ ¬(old X0 X1 sk5) ∨ a = sk3 ∨ sk3 = X0 ∨ a = sk0 := resolve eq209 eq180 -- resolution 209,180
  have eq761 (X0 X1 : G) : ¬(sP1 X0 X1 sk5) ∨ sk1 = sk3 ∨ ¬(new a sk1 sk2) ∨ ¬(new a sk3 sk4) ∨ ¬(sP1 X0 X1 sk5) := resolve eq403 eq218 -- resolution 403,218
  have eq763 (X0 X1 : G) : ¬(sP1 X0 X1 sk5) ∨ sk1 = sk3 ∨ ¬(new a sk1 sk2) ∨ ¬(new a sk3 sk4) := resolve eq761 rfl -- duplicate literal removal 761
  have eq765 (X0 X1 : G) : ¬(sP1 X0 X1 sk5) ∨ ¬(new a sk1 sk2) ∨ ¬(new a sk3 sk4) := resolve eq763 preserve_4 -- subsumption resolution 763,99
  have eq766 : ¬(new a sk3 sk4) ∨ ¬(new a sk1 sk2) ∨ c = sk5 ∨ (old sk3 sk4 sk5) := resolve eq765 eq435 -- resolution 765,435
  have eq767 : ¬(new a sk3 sk4) ∨ ¬(new a sk1 sk2) ∨ c = sk5 ∨ (old sk1 sk2 sk5) := resolve eq765 eq411 -- resolution 765,411
  have eq769 : ¬(new a sk3 sk4) ∨ ¬(new a sk1 sk2) ∨ (old sk3 sk4 sk5) ∨ (sP0 sk3 sk4 sk5) := resolve eq765 eq146 -- resolution 765,146
  have eq1265 : ¬(old sk3 sk4 sk5) ∨ a = sk1 ∨ sk1 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq711 eq180 -- resolution 711,180
  have eq1267 : ¬(old sk3 sk4 sk5) ∨ a = sk1 ∨ sk1 = sk3 ∨ a = sk0 := resolve eq1265 rfl -- duplicate literal removal 1265
  have eq1272 : ¬(old sk3 sk4 sk5) ∨ a = sk1 ∨ a = sk0 := resolve eq1267 preserve_4 -- subsumption resolution 1267,99
  have eq1275 : c = sk5 ∨ a = sk0 ∨ c = sk4 ∨ a = sk1 := resolve eq1272 eq315 -- resolution 1272,315
  have eq1280 : ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ sk1 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq726 eq176 -- resolution 726,176
  have eq1287 : ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ sk1 = sk3 ∨ a = sk0 := resolve eq1280 rfl -- duplicate literal removal 1280
  have eq1291 : ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ a = sk0 := resolve eq1287 preserve_4 -- subsumption resolution 1287,99
  have eq1362 : a = sk3 ∨ a = sk0 ∨ c = sk2 ∨ b = sk2 := resolve eq1291 eq287 -- resolution 1291,287
  have eq1493 : (sP1 sk1 sk2 c) ∨ (old sk1 sk2 c) ∨ (sP0 sk1 sk2 c) ∨ a = sk0 ∨ c = sk4 ∨ a = sk1 := Or.assoc3 (eq1275.imp_left (fun h : c = sk5 ↦ superpose h eq145)) -- superposition 145,1275, 1275 into 145, unify on (0).2 in 1275 and (0).3 in 145
  have eq1581 : (old sk1 sk2 c) ∨ (sP0 sk1 sk2 c) ∨ a = sk0 ∨ c = sk4 ∨ a = sk1 := resolve eq1493 eq108 -- subsumption resolution 1493,108
  have eq1582 : (sP0 sk1 sk2 c) ∨ a = sk0 ∨ c = sk4 ∨ a = sk1 := resolve eq1581 p4XY -- subsumption resolution 1581,67
  have eq1583 : c = sk4 ∨ a = sk0 ∨ a = sk1 := resolve eq1582 rule_def_0_0 -- subsumption resolution 1582,79
  have eq1595 : (sP1 sk0 sk3 c) ∨ (old sk0 sk3 c) ∨ (sP0 sk0 sk3 c) ∨ a = sk0 ∨ a = sk1 := Or.assoc3 (eq1583.imp_left (fun h : c = sk4 ↦ superpose h eq144)) -- superposition 144,1583, 1583 into 144, unify on (0).2 in 1583 and (0).3 in 144
  have eq1648 : (old sk0 sk3 c) ∨ (sP0 sk0 sk3 c) ∨ a = sk0 ∨ a = sk1 := resolve eq1595 eq108 -- subsumption resolution 1595,108
  have eq1649 : (sP0 sk0 sk3 c) ∨ a = sk0 ∨ a = sk1 := resolve eq1648 p4XY -- subsumption resolution 1648,67
  have eq1650 : a = sk1 ∨ a = sk0 := resolve eq1649 rule_def_0_0 -- subsumption resolution 1649,79
  have eq1652 : (new a sk2 sk5) ∨ a = sk0 := eq1650.imp_left (fun h : a = sk1 ↦ superpose h preserve_2) -- superposition 97,1650, 1650 into 97, unify on (0).2 in 1650 and (0).1 in 97
  have eq1827 : a ≠ sk1 ∨ a = sk0 ∨ c = sk2 ∨ b = sk2 := eq1362.imp_left (fun h : a = sk3 ↦ superpose h preserve_4) -- superposition 99,1362, 1362 into 99, unify on (0).2 in 1362 and (0).2 in 99
  have eq1888 : b = sk2 ∨ c = sk2 ∨ a = sk0 := resolve eq1827 eq1650 -- subsumption resolution 1827,1650
  have eq1953 : (new a b sk5) ∨ a = sk0 ∨ c = sk2 ∨ a = sk0 := Or.assoc2 (eq1888.imp_left (fun h : b = sk2 ↦ superpose h eq1652)) -- superposition 1652,1888, 1888 into 1652, unify on (0).2 in 1888 and (0).2 in 1652
  have eq1967 : (new a b sk5) ∨ a = sk0 ∨ c = sk2 := resolve eq1953 rfl -- duplicate literal removal 1953
  have eq2053 : c = sk5 ∨ c = sk2 ∨ a = sk0 := resolve eq1967 eq113 -- resolution 1967,113
  have eq2089 : (old sk3 sk4 c) ∨ a = sk3 ∨ c = sk2 ∨ a = sk0 := Or.assoc2 (eq2053.imp_left (fun h : c = sk5 ↦ superpose h eq200)) -- superposition 200,2053, 2053 into 200, unify on (0).2 in 2053 and (0).3 in 200
  have eq2182 : a = sk3 ∨ c = sk2 ∨ a = sk0 := resolve eq2089 p4XY -- subsumption resolution 2089,67
  have eq2196 : a ≠ sk1 ∨ c = sk2 ∨ a = sk0 := eq2182.imp_left (fun h : a = sk3 ↦ superpose h preserve_4) -- superposition 99,2182, 2182 into 99, unify on (0).2 in 2182 and (0).2 in 99
  have eq2257 : c = sk2 ∨ a = sk0 := resolve eq2196 eq1650 -- subsumption resolution 2196,1650
  have eq2270 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := Or.assoc3 (eq2257.imp_left (fun h : c = sk2 ↦ superpose h eq143)) -- superposition 143,2257, 2257 into 143, unify on (0).2 in 2257 and (0).3 in 143
  have eq2330 : (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq2270 eq108 -- subsumption resolution 2270,108
  have eq2331 : (sP0 sk0 sk1 c) ∨ a = sk0 := resolve eq2330 p4XY -- subsumption resolution 2330,67
  have eq2332 : a = sk0 := resolve eq2331 rule_def_0_0 -- subsumption resolution 2331,79
  have eq2333 : (new a sk1 sk2) := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_0 -- backward demodulation 95,2332
  have eq2334 : (new a sk3 sk4) := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 96,2332
  have eq2359 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq235 -- backward demodulation 235,2332
  have eq2360 : (old a sk1 sk2) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq236 -- backward demodulation 236,2332
  have eq2371 : (old a sk3 sk4) ∨ c = sk3 ∨ c = sk4 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq254 -- backward demodulation 254,2332
  have eq2372 : (old a sk3 sk4) ∨ c = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq255 -- backward demodulation 255,2332
  have eq2485 : ∀ (X0 X1 : G) , ¬(old a X0 X1) ∨ sk1 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq709 -- backward demodulation 709,2332
  have eq2487 : ∀ (X0 X1 : G) , ¬(old a X0 X1) ∨ sk3 = X0 ∨ ¬(old X0 X1 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq2332, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq724 -- backward demodulation 724,2332
  have eq3036 : ¬(new a sk1 sk2) ∨ (old sk3 sk4 sk5) ∨ (sP0 sk3 sk4 sk5) := resolve eq2334 eq769 -- resolution 2334,769
  have eq3038 : ¬(new a sk1 sk2) ∨ c = sk5 ∨ (old sk1 sk2 sk5) := resolve eq2334 eq767 -- resolution 2334,767
  have eq3039 : ¬(new a sk1 sk2) ∨ c = sk5 ∨ (old sk3 sk4 sk5) := resolve eq2334 eq766 -- resolution 2334,766
  have eq3046 : (sP0 sk3 sk4 sk5) ∨ (old sk3 sk4 sk5) := resolve eq3036 eq2333 -- subsumption resolution 3036,2333
  have eq3048 : (old sk1 sk2 sk5) ∨ c = sk5 := resolve eq3038 eq2333 -- subsumption resolution 3038,2333
  have eq3049 : (old sk3 sk4 sk5) ∨ c = sk5 := resolve eq3039 eq2333 -- subsumption resolution 3039,2333
  have eq3101 : (old sk3 sk4 sk5) ∨ b = sk4 := resolve eq3046 rule_def_0_1 -- resolution 3046,80
  have eq3701 : sk1 = sk3 ∨ ¬(old sk3 sk4 sk5) ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 := resolve eq2485 eq2372 -- resolution 2485,2372
  have eq3709 : ¬(old sk3 sk4 sk5) ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 := resolve eq3701 preserve_4 -- subsumption resolution 3701,99
  have eq3735 : sk1 = sk3 ∨ ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq2487 eq2360 -- resolution 2487,2360
  have eq3746 : ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq3735 preserve_4 -- subsumption resolution 3735,99
  have eq4944 : c = sk5 ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 ∨ a = sk1 := resolve eq3709 eq3049 -- resolution 3709,3049
  have eq5079 : (sP1 sk1 sk2 c) ∨ (old sk1 sk2 c) ∨ (sP0 sk1 sk2 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 ∨ a = sk1 := Or.assoc3 (eq4944.imp_left (fun h : c = sk5 ↦ superpose h eq145)) -- superposition 145,4944, 4944 into 145, unify on (0).2 in 4944 and (0).3 in 145
  have eq5271 : (old sk1 sk2 c) ∨ (sP0 sk1 sk2 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 ∨ a = sk1 := resolve eq5079 eq108 -- subsumption resolution 5079,108
  have eq5272 : (sP0 sk1 sk2 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ b = sk3 ∨ a = sk1 := resolve eq5271 p4XY -- subsumption resolution 5271,67
  have eq5273 : b = sk3 ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq5272 rule_def_0_0 -- subsumption resolution 5272,79
  have eq5333 : (old a b sk4) ∨ c = b ∨ c = sk4 ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5273.imp_left (fun h : b = sk3 ↦ superpose h eq2371)) -- superposition 2371,5273, 5273 into 2371, unify on (0).2 in 5273 and (0).2 in 2371
  have eq5389 : c = b ∨ c = sk4 ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq5333 p3 -- subsumption resolution 5333,66
  have eq5390 : c = sk4 ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq5389 bc -- subsumption resolution 5389,65
  have eq5491 : (old sk3 c sk5) ∨ c = b ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := Or.assoc2 (eq5390.imp_left (fun h : c = sk4 ↦ superpose h eq3101)) -- superposition 3101,5390, 5390 into 3101, unify on (0).2 in 5390 and (0).2 in 3101
  have eq5531 : c = b ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq5491 p4XZ -- subsumption resolution 5491,68
  have eq5532 : c = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5531 bc -- subsumption resolution 5531,65
  have eq5544 : (old c sk4 sk5) ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 := Or.assoc2 (eq5532.imp_left (fun h : c = sk3 ↦ superpose h eq200)) -- superposition 200,5532, 5532 into 200, unify on (0).2 in 5532 and (0).1 in 200
  have eq5642 : a = c ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5544 p4YZ -- subsumption resolution 5544,69
  have eq5643 : b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5642 ac -- subsumption resolution 5642,64
  have eq5695 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5643.imp_left (fun h : b = sk1 ↦ superpose h eq2359)) -- superposition 2359,5643, 5643 into 2359, unify on (0).2 in 5643 and (0).2 in 2359
  have eq5744 : c = b ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5695 p3 -- subsumption resolution 5695,66
  have eq5745 : c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq5744 bc -- subsumption resolution 5744,65
  have eq5757 : (sP1 sk1 c sk5) ∨ (old sk1 c sk5) ∨ (sP0 sk1 c sk5) ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq5745.imp_left (fun h : c = sk2 ↦ superpose h eq145)) -- superposition 145,5745, 5745 into 145, unify on (0).2 in 5745 and (0).2 in 145
  have eq5860 : (sP1 sk1 c sk5) ∨ (sP0 sk1 c sk5) ∨ c = sk1 ∨ a = sk1 := resolve eq5757 p4XZ -- subsumption resolution 5757,68
  have eq5861 : (sP1 sk1 c sk5) ∨ c = sk1 ∨ a = sk1 := resolve eq5860 rule_def_0_0 -- subsumption resolution 5860,79
  have eq5862 : c = sk1 ∨ a = sk1 := resolve eq5861 rule_def_1_0 -- subsumption resolution 5861,83
  have eq5872 : (old c sk2 sk5) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq5862.imp_left (fun h : c = sk1 ↦ superpose h eq190)) -- superposition 190,5862, 5862 into 190, unify on (0).2 in 5862 and (0).1 in 190
  have eq5954 : a = c ∨ a = sk1 := resolve eq5872 p4YZ -- subsumption resolution 5872,69
  have eq5955 : a = sk1 := resolve eq5954 ac -- subsumption resolution 5954,64
  have eq5957 : a ≠ sk3 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_4 -- backward demodulation 99,5955
  have eq6101 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2359 -- backward demodulation 2359,5955
  have eq6278 : (old a sk2 sk5) ∨ c = sk5 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3048 -- backward demodulation 3048,5955
  have eq6326 : a = c ∨ ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3746 -- backward demodulation 3746,5955
  have eq6849 : (old a sk1 sk2) ∨ c = sk2 := resolve eq6101 ac -- subsumption resolution 6101,64
  have eq6850 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6849 -- forward demodulation 6849,5955
  have eq7052 : ¬(old sk1 sk2 sk5) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 := resolve eq6326 ac -- subsumption resolution 6326,64
  have eq7053 : ¬(old sk1 sk2 sk5) ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 := resolve eq7052 eq5957 -- subsumption resolution 7052,5957
  have eq7054 : ¬(old a sk2 sk5) ∨ c = sk3 ∨ b = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7053 -- forward demodulation 7053,5955
  have eq7055 : ¬(old a sk2 sk5) ∨ a = b ∨ c = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq5955, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7054 -- forward demodulation 7054,5955
  have eq7696 : c = sk5 ∨ c = sk3 ∨ b = sk3 ∨ a = b := resolve eq7055 eq6278 -- resolution 7055,6278
  have eq7703 : (old sk3 sk4 c) ∨ a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ a = b := Or.assoc2 (eq7696.imp_left (fun h : c = sk5 ↦ superpose h eq200)) -- superposition 200,7696, 7696 into 200, unify on (0).2 in 7696 and (0).3 in 200
  have eq7817 : a = sk3 ∨ c = sk3 ∨ b = sk3 ∨ a = b := resolve eq7703 p4XY -- subsumption resolution 7703,67
  have eq7818 : b = sk3 ∨ c = sk3 ∨ a = b := resolve eq7817 eq5957 -- subsumption resolution 7817,5957
  have eq7868 : (old a b sk4) ∨ c = b ∨ c = sk4 ∨ c = sk3 ∨ a = b := Or.assoc3 (eq7818.imp_left (fun h : b = sk3 ↦ superpose h eq2371)) -- superposition 2371,7818, 7818 into 2371, unify on (0).2 in 7818 and (0).2 in 2371
  have eq7918 : c = b ∨ c = sk4 ∨ c = sk3 ∨ a = b := resolve eq7868 p3 -- subsumption resolution 7868,66
  have eq7919 : c = sk4 ∨ c = sk3 ∨ a = b := resolve eq7918 bc -- subsumption resolution 7918,65
  have eq7942 : (old sk3 c sk5) ∨ a = sk3 ∨ c = sk3 ∨ a = b := Or.assoc2 (eq7919.imp_left (fun h : c = sk4 ↦ superpose h eq200)) -- superposition 200,7919, 7919 into 200, unify on (0).2 in 7919 and (0).2 in 200
  have eq8025 : a = sk3 ∨ c = sk3 ∨ a = b := resolve eq7942 p4XZ -- subsumption resolution 7942,68
  have eq8026 : c = sk3 ∨ a = b := resolve eq8025 eq5957 -- subsumption resolution 8025,5957
  have eq8044 : (old c sk4 sk5) ∨ a = c ∨ a = b := Or.assoc2 (eq8026.imp_left (fun h : c = sk3 ↦ superpose h eq200)) -- superposition 200,8026, 8026 into 200, unify on (0).2 in 8026 and (0).1 in 200
  have eq8116 : a = c ∨ a = b := resolve eq8044 p4YZ -- subsumption resolution 8044,69
  have eq8117 : a = b := resolve eq8116 ac -- subsumption resolution 8116,64
  have eq8119 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq8117, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 66,8117
  have eq8559 : c = sk2 := resolve eq8119 eq6850 -- resolution 8119,6850
  have eq8609 : (old a c sk5) ∨ c = sk5 := Eq.mp (by simp only [eq8559, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6278 -- backward demodulation 6278,8559
  have eq8748 : c = sk5 := resolve eq8609 p4XZ -- subsumption resolution 8609,68
  have eq8757 : (old sk3 sk4 c) ∨ a = sk3 := Eq.mp (by simp only [eq8748, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq200 -- backward demodulation 200,8748
  have eq8984 : a = sk3 := resolve eq8757 p4XY -- subsumption resolution 8757,67
  subsumption eq5957 eq8984 -- subsumption resolution 8984,5957

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq119 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 82,86
  have eq135 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq119 rule_def_1_0 -- resolution 119,77
  have eq137 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq135 preserve_1 -- subsumption resolution 135,87
  have eq148 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq137 rule_def_0_0 -- resolution 137,73
  have eq149 : (old sk0 sk1 sk2) := resolve eq148 preserve_1 -- subsumption resolution 148,87
  have eq158 : memold sk0 := resolve eq149 old_mem1 -- resolution 149,83
  subsumption preserve_3 eq158 -- subsumption resolution 158,89

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq119 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 82,86
  have eq134 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq119 rule_def_1_1 -- resolution 119,78
  have eq137 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq134 preserve_4 -- subsumption resolution 134,90
  have eq147 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq137 rule_def_0_1 -- resolution 137,74
  have eq149 : (old sk0 sk1 sk2) := resolve eq147 preserve_2 -- subsumption resolution 147,88
  have eq157 : memold sk1 := resolve eq149 old_mem2 -- resolution 149,84
  subsumption preserve_3 eq157 -- subsumption resolution 157,89

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old a Z (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq100 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X2 := resolve rule_def_1_2 old_mem2 -- resolution 79,84
  have eq119 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 82,86
  have eq133 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk2 := resolve eq119 eq100 -- resolution 119,100
  have eq136 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq133 preserve_3 -- subsumption resolution 133,89
  have eq138 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq136 rule_def_0_2 -- resolution 136,75
  have eq141 : (old sk0 sk1 sk2) := resolve eq138 preserve_4 -- subsumption resolution 138,90
  have eq153 : memold sk2 := resolve eq141 old_mem3 -- resolution 141,85
  subsumption preserve_3 eq153 -- subsumption resolution 153,89

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X4 ∨ ¬ R X1 X2 X3 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1, ¬ R X0 X1 X1 ∨ ¬ R X1 X1 X0 ∨ X1 = X0)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X0 ∨ R X0 X2 X0)
  rule_4 : (∀ X0 X1 X2 X3, ¬ R X0 X0 X1 ∨ ¬ R X0 X2 X3 ∨ ¬ R X2 X3 X1 ∨ X3 = X0)
  rule_5 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X2 ∨ X0 = X1)
  rule_6 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X4 ∨ ¬ R X1 X2 X5 ∨ ¬ R X3 X4 X5 ∨ X1 = X3)
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
  let sP1 (X Y Z) := ∃ sF0, a = X ∧ c = Y ∧ ps.R a Z sF0 ∧ ps.R Z sF0 b
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3

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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 bc p3 p4XY p4XZ ps.rule_0 ps.rule_6 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_3 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 ac p4YZ ps.rule_2 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 ac p4XY p4XZ p4YZ ps.rule_3 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 ac p3 p4XY p4XZ p4YZ prev_0 prev_1 ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sF0 sP1 ac p4XY p4XZ p4YZ ps.rule_5 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_6 := rule_6_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ prev_0 prev_1 ps.rule_6 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    rule_6 := prev_6
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_0 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_2 rule_def_1_2 new_imp ps.mem_2 ps.mem_3
  }, by simp only [new_new, imp_iff_not_or, imp_new_0, implies_true, and_self]⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X0 X3 X4 ∨ ¬ ps.compl X1 X2 X3 ∨ ps.compl X0 X4 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X0 X3) (max (Nat.pair X1 X2) (max (Nat.pair X0 X4) 0)))
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

theorem PartialSolution.toMagma_equation503 :
    letI := ps.toMagma
    Equation503 ℕ := by
  simp only [Equation503, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun X0 (ps.complFun X1 X0)) (ps.complFun X1 (ps.complFun X0 (ps.complFun X1 X0)))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter359 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation503_not_implies_Equation359 : ∃ (G : Type) (_ : Magma G), Equation503 G ∧ ¬Equation359 G := by
  use ℕ, PartialSolution.counter359.toMagma, PartialSolution.counter359.toMagma_equation503
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter359.of_R 1 1 2] | rw [PartialSolution.counter359.of_R 2 1 3])
  all_goals simp [PartialSolution.counter359]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3862 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (2, 1, 3), (3, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation503_not_implies_Equation3862 : ∃ (G : Type) (_ : Magma G), Equation503 G ∧ ¬Equation3862 G := by
  use ℕ, PartialSolution.counter3862.toMagma, PartialSolution.counter3862.toMagma_equation503
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3862.of_R 1 1 2] | rw [PartialSolution.counter3862.of_R 1 2 3] | rw [PartialSolution.counter3862.of_R 2 1 3] | rw [PartialSolution.counter3862.of_R 3 1 3])
  all_goals simp [PartialSolution.counter3862]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter4065 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 3), (3, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation503_not_implies_Equation4065 : ∃ (G : Type) (_ : Magma G), Equation503 G ∧ ¬Equation4065 G := by
  use ℕ, PartialSolution.counter4065.toMagma, PartialSolution.counter4065.toMagma_equation503
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter4065.of_R 1 1 2] | rw [PartialSolution.counter4065.of_R 2 1 3] | rw [PartialSolution.counter4065.of_R 3 1 3])
  all_goals simp [PartialSolution.counter4065]

end Eq503
