import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq707

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old X2 a b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) a b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq72 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X3 a b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 59
  have eq73 (X2 X3 : G) : ¬(old X3 a b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq72 rfl -- equality resolution 72
  have eq74 (X0 X1 X2 X3 : G) : ¬(old X3 a (sF0 X0 X1 X2)) ∨ X2 = X3 ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_2 old_2 -- resolution 62,52
  have eq77 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 62,49
  have eq78 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ (sF0 X0 X1 X2) = X3 ∨ ¬(old X3 a b) := resolve rule_def_1_3 old_2 -- resolution 63,52
  have eq83 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq73 rule_def_1_3 -- resolution 73,63
  have eq91 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 65,66
  have eq92 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 65,67
  have eq98 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq91 rule_def_1_1 -- resolution 91,61
  have eq99 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq91 rule_def_1_0 -- resolution 91,60
  have eq100 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq99 rule_def_0_0 -- subsumption resolution 99,56
  have eq104 (X0 : G) : ¬(old sk0 sk1 X0) ∨ sk2 = X0 ∨ a = sk0 := resolve eq100 old_0 -- resolution 100,50
  have eq106 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ c = sk1 := resolve eq92 rule_def_1_1 -- resolution 92,61
  have eq107 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ a = sk0 := resolve eq92 rule_def_1_0 -- resolution 92,60
  have eq108 : (old sk0 sk1 sk3) ∨ a = sk0 := resolve eq107 rule_def_0_0 -- subsumption resolution 107,56
  have eq118 (X0 : G) : (sF0 sk0 sk1 sk2) = X0 ∨ ¬(old X0 a b) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq78 eq91 -- resolution 78,91
  have eq121 : sk2 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq104 eq108 -- resolution 104,108
  have eq122 : sk2 = sk3 ∨ a = sk0 := resolve eq121 rfl -- duplicate literal removal 121
  have eq124 : a = sk0 := resolve eq122 preserve_2 -- subsumption resolution 122,68
  have eq127 : (sP0 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq91 -- backward demodulation 91,124
  have eq128 : (sP0 a sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq92 -- backward demodulation 92,124
  have eq129 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq98 -- backward demodulation 98,124
  have eq131 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq106 -- backward demodulation 106,124
  have eq135 : ∀ (X0 : G) , (sP0 a sk1 sk2) ∨ (sF0 sk0 sk1 sk2) = X0 ∨ ¬(old X0 a b) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq118 -- backward demodulation 118,124
  have eq137 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq127 -- forward demodulation 127,124
  have eq138 : (sP1 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq137 -- forward demodulation 137,124
  have eq139 : (sP1 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq128 -- forward demodulation 128,124
  have eq140 : (sP1 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a sk1 sk3) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq139 -- forward demodulation 139,124
  have eq141 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq129 -- forward demodulation 129,124
  have eq142 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq131 -- forward demodulation 131,124
  have eq147 : ∀ (X0 : G) , (sF0 a sk1 sk2) = X0 ∨ (sP0 a sk1 sk2) ∨ ¬(old X0 a b) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq135 -- forward demodulation 135,124
  have eq148 : ∀ (X0 : G) , ¬(old X0 a b) ∨ (sF0 a sk1 sk2) = X0 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq124, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq147 -- forward demodulation 147,124
  have eq153 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq141 rule_def_0_2 -- resolution 141,58
  have eq163 (X0 : G) : ¬(old a sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq153 old_0 -- resolution 153,50
  have eq177 : (old a sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq142 rule_def_0_2 -- resolution 142,58
  have eq178 : (old a sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq142 rule_def_0_1 -- resolution 142,57
  have eq190 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq83 rule_def_1_2 -- resolution 83,62
  have eq191 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq190 rfl -- duplicate literal removal 190
  have eq193 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (new a c sk3) := resolve eq191 eq140 -- resolution 191,140
  have eq215 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sF0 X0 X1 X2) = (sF0 a sk1 sk2) := resolve eq148 rule_def_1_3 -- resolution 148,63
  have eq223 : (new a c sk3) ∨ (old a sk1 sk3) ∨ c = sk3 := resolve eq193 rule_def_0_2 -- resolution 193,58
  have eq228 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP0 a c sk3) ∨ (old a c sk3) ∨ (sP1 a c sk3) := resolve eq223 new_imp -- resolution 223,65
  have eq229 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) := resolve eq228 p4XZ -- subsumption resolution 228,48
  have eq230 : (sP1 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) := resolve eq229 rule_def_0_2 -- subsumption resolution 229,58
  have eq247 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq163 eq178 -- resolution 163,178
  have eq250 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq247 rfl -- duplicate literal removal 247
  have eq253 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq250 preserve_2 -- subsumption resolution 250,68
  have eq256 : (sP1 a sk1 c) ∨ (old a sk1 c) ∨ (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq253.imp_left (fun h : c = sk2 ↦ superpose h eq138)) -- superposition 138,253, 253 into 138, unify on (0).2 in 253 and (0).3 in 138
  have eq265 : (old a sk1 c) ∨ (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq256 eq77 -- subsumption resolution 256,77
  have eq266 : (sP0 a sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq265 p4XY -- subsumption resolution 265,47
  have eq267 : b = sk1 ∨ c = sk1 := resolve eq266 rule_def_0_1 -- subsumption resolution 266,57
  have eq280 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq267.imp_left (fun h : b = sk1 ↦ superpose h eq153)) -- superposition 153,267, 267 into 153, unify on (0).2 in 267 and (0).2 in 153
  have eq283 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq267.imp_left (fun h : b = sk1 ↦ superpose h eq177)) -- superposition 177,267, 267 into 177, unify on (0).2 in 267 and (0).2 in 177
  have eq293 : c = b ∨ c = sk2 ∨ c = sk1 := resolve eq280 p3 -- subsumption resolution 280,46
  have eq294 : c = sk2 ∨ c = sk1 := resolve eq293 bc -- subsumption resolution 293,45
  have eq295 : c = b ∨ c = sk3 ∨ c = sk1 := resolve eq283 p3 -- subsumption resolution 283,46
  have eq296 : c = sk3 ∨ c = sk1 := resolve eq295 bc -- subsumption resolution 295,45
  have eq317 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sF0 a sk1 sk2) = (sF0 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) := resolve eq215 eq230 -- resolution 215,230
  have eq320 : c ≠ sk2 ∨ c = sk1 := eq296.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 68,296, 296 into 68, unify on (0).2 in 296 and (0).2 in 68
  have eq331 : c = sk1 := resolve eq320 eq294 -- subsumption resolution 320,294
  have eq334 : (sP0 a c sk2) ∨ (sP1 a sk1 sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq138 -- backward demodulation 138,331
  have eq335 : (sP0 a c sk3) ∨ (sP1 a sk1 sk3) ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq140 -- backward demodulation 140,331
  have eq357 : (old a c sk3) ∨ (sP1 a c sk3) ∨ c = sk3 := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq230 -- backward demodulation 230,331
  have eq365 : (sP0 a c sk2) ∨ (old a sk1 sk2) ∨ (sF0 a sk1 sk2) = (sF0 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq317 -- backward demodulation 317,331
  have eq366 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq334 -- forward demodulation 334,331
  have eq367 : (old a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq366 -- forward demodulation 366,331
  have eq368 : (sP1 a c sk2) ∨ (sP0 a c sk2) := resolve eq367 p4XZ -- subsumption resolution 367,48
  have eq369 : (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq335 -- forward demodulation 335,331
  have eq370 : (old a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq369 -- forward demodulation 369,331
  have eq371 : (sP1 a c sk3) ∨ (sP0 a c sk3) := resolve eq370 p4XZ -- subsumption resolution 370,48
  have eq404 : (sP1 a c sk3) ∨ c = sk3 := resolve eq357 p4XZ -- subsumption resolution 357,48
  have eq416 : (old a c sk2) ∨ (sP0 a c sk2) ∨ (sF0 a sk1 sk2) = (sF0 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq365 -- forward demodulation 365,331
  have eq417 : (sP0 a c sk2) ∨ (sF0 a sk1 sk2) = (sF0 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) := resolve eq416 p4XZ -- subsumption resolution 416,48
  have eq418 : (sF0 a c sk2) = (sF0 a c sk3) ∨ (sP0 a c sk2) ∨ c = sk3 ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq417 -- forward demodulation 417,331
  have eq419 : (old a c sk3) ∨ (sF0 a c sk2) = (sF0 a c sk3) ∨ (sP0 a c sk2) ∨ c = sk3 := Eq.mp (by simp only [eq331, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq418 -- forward demodulation 418,331
  have eq420 : (sP0 a c sk2) ∨ (sF0 a c sk2) = (sF0 a c sk3) ∨ c = sk3 := resolve eq419 p4XZ -- subsumption resolution 419,48
  have eq472 : (sF0 a c sk2) = (sF0 a c sk3) ∨ c = sk3 ∨ c = b := resolve eq420 rule_def_0_1 -- resolution 420,57
  have eq474 : (sF0 a c sk2) = (sF0 a c sk3) ∨ c = sk3 := resolve eq472 bc -- subsumption resolution 472,45
  have eq479 : (old sk3 a (sF0 a c sk2)) ∨ ¬(sP1 a c sk3) ∨ c = sk3 := Or.assoc2 (eq474.imp_left (fun h : (sF0 a c sk2) = (sF0 a c sk3) ↦ superpose h rule_def_1_2)) -- superposition 62,474, 474 into 62, unify on (0).2 in 474 and (0).3 in 62
  have eq494 : (old sk3 a (sF0 a c sk2)) ∨ c = sk3 := resolve eq479 eq404 -- subsumption resolution 479,404
  have eq538 : c = sk3 ∨ sk2 = sk3 ∨ ¬(sP1 a c sk2) := resolve eq494 eq74 -- resolution 494,74
  have eq544 : ¬(sP1 a c sk2) ∨ c = sk3 := resolve eq538 preserve_2 -- subsumption resolution 538,68
  have eq546 : (sP0 a c sk2) ∨ c = sk3 := resolve eq544 eq368 -- resolution 544,368
  have eq564 : c = sk3 ∨ c = b := resolve eq546 rule_def_0_1 -- resolution 546,57
  have eq566 : c = sk3 := resolve eq564 bc -- subsumption resolution 564,45
  have eq569 : (sP0 a c c) ∨ (sP1 a c sk3) := Eq.mp (by simp only [eq566, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq371 -- backward demodulation 371,566
  have eq594 : (sP1 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq566, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq569 -- forward demodulation 569,566
  have eq595 : (sP0 a c c) := resolve eq594 eq77 -- subsumption resolution 594,77
  have eq612 : c = b := resolve eq595 rule_def_0_1 -- resolution 595,57
  subsumption bc eq612 -- subsumption resolution 612,45

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X4 ∨ ¬ old X2 X1 X3 ∨ old X1 X4 X0)) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X2 X1 X0 ∨ old X1 X2 X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old X2 a b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) a b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X3 X4 ∨ ¬ new X2 X1 X3 ∨ new X1 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq74 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 58
  have eq75 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq74 rfl -- equality resolution 74
  have eq76 : (new a b c) := resolve eq75 rfl -- equality resolution 75
  have eq77 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X3 a b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 62
  have eq78 (X2 X3 : G) : ¬(old X3 a b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq77 rfl -- equality resolution 77
  have eq82 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 65,52
  have eq86 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq76 -- resolution 69,76
  have eq90 (X0 X1 X2 : G) : ¬(old (sF0 X1 X2 X0) a a) ∨ (old a X0 (sF0 X1 X2 X0)) ∨ ¬(sP1 X1 X2 X0) := resolve old_3 rule_def_1_2 -- resolution 56,65
  have eq93 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq78 rule_def_1_3 -- resolution 78,66
  have eq99 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 68,70
  have eq100 : (sP1 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) := resolve new_imp preserve_1 -- resolution 68,71
  have eq101 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) := resolve new_imp preserve_2 -- resolution 68,72
  have eq112 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq99 rule_def_1_1 -- resolution 99,64
  have eq115 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 := resolve eq100 rule_def_1_1 -- resolution 100,64
  have eq116 : (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ a = sk1 := resolve eq100 rule_def_1_0 -- resolution 100,63
  have eq117 : (old sk1 sk3 sk4) ∨ a = sk1 := resolve eq116 rule_def_0_0 -- subsumption resolution 116,59
  have eq123 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq101 rule_def_1_1 -- resolution 101,64
  have eq124 : (old sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ a = sk2 := resolve eq101 rule_def_1_0 -- resolution 101,63
  have eq125 : (old sk2 sk1 sk3) ∨ a = sk2 := resolve eq124 rule_def_0_0 -- subsumption resolution 124,59
  have eq133 (X0 X1 : G) : ¬(old sk1 sk3 X0) ∨ (old sk1 X0 X1) ∨ a = sk2 ∨ ¬(old X1 sk1 sk2) := resolve eq125 old_1 -- resolution 125,54
  have eq160 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq93 rule_def_1_2 -- resolution 93,65
  have eq161 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq160 rfl -- duplicate literal removal 160
  have eq163 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (new a c sk4) := resolve eq161 eq100 -- resolution 161,100
  have eq172 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq112 rule_def_0_2 -- resolution 112,61
  have eq173 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq112 rule_def_0_1 -- resolution 112,60
  have eq179 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 := resolve eq172 old_2 -- resolution 172,55
  have eq182 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq115 rule_def_0_2 -- resolution 115,61
  have eq183 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq115 rule_def_0_1 -- resolution 115,60
  have eq192 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq123 rule_def_0_2 -- resolution 123,61
  have eq193 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq123 rule_def_0_1 -- resolution 123,60
  have eq217 (X0 X1 : G) : ¬(old sk1 sk3 X0) ∨ c = sk3 ∨ (old sk1 X0 X1) ∨ c = sk1 ∨ ¬(old X1 sk1 sk2) := resolve eq192 old_1 -- resolution 192,54
  have eq227 (X0 X1 : G) : ¬(old sk1 sk3 X0) ∨ b = sk1 ∨ (old sk1 X0 X1) ∨ c = sk1 ∨ ¬(old X1 sk1 sk2) := resolve eq193 old_1 -- resolution 193,54
  have eq259 : (new a c sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk4 := resolve eq163 rule_def_0_2 -- resolution 163,61
  have eq260 : (new a c sk4) ∨ (old sk1 sk3 sk4) ∨ b = sk3 := resolve eq163 rule_def_0_1 -- resolution 163,60
  have eq264 : (old sk1 sk3 sk4) ∨ c = sk4 ∨ (sP0 a c sk4) ∨ (old a c sk4) ∨ (sP1 a c sk4) := resolve eq259 new_imp -- resolution 259,68
  have eq266 : (old sk1 sk3 sk4) ∨ c = sk4 ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) := resolve eq264 p4XZ -- subsumption resolution 264,51
  have eq267 : (sP1 a c sk4) ∨ c = sk4 ∨ (old sk1 sk3 sk4) := resolve eq266 rule_def_0_2 -- subsumption resolution 266,61
  have eq268 : (old sk1 sk3 sk4) ∨ b = sk3 ∨ (sP0 a c sk4) ∨ (old a c sk4) ∨ (sP1 a c sk4) := resolve eq260 new_imp -- resolution 260,68
  have eq270 : (sP1 a c sk4) ∨ b = sk3 ∨ (sP0 a c sk4) ∨ (old sk1 sk3 sk4) := resolve eq268 p4XZ -- subsumption resolution 268,51
  have eq297 (X0 : G) : ¬(old X0 sk1 sk2) ∨ a = sk2 ∨ (old sk1 sk4 X0) ∨ a = sk1 := resolve eq133 eq117 -- resolution 133,117
  have eq403 : (old sk1 sk4 sk0) ∨ a = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq297 eq172 -- resolution 297,172
  have eq473 (X0 : G) : c = sk3 ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ ¬(old X0 sk1 sk2) ∨ c = sk3 ∨ c = sk4 := resolve eq217 eq182 -- resolution 217,182
  have eq475 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 := resolve eq473 rfl -- duplicate literal removal 473
  have eq482 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ b = sk1 ∨ a = sk1 := resolve eq227 eq117 -- resolution 227,117
  have eq679 : a = sk2 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk4 sk0) := resolve eq403 imp_new_0 -- resolution 403,57
  have eq680 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq679 preserve_3 -- subsumption resolution 679,73
  have eq692 : (old c sk1 sk3) ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = sk2 := Or.assoc2 (eq680.imp_left (fun h : c = sk2 ↦ superpose h eq125)) -- superposition 125,680, 680 into 125, unify on (0).2 in 680 and (0).1 in 125
  have eq735 : a = c ∨ a = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq692 p4YZ -- subsumption resolution 692,52
  have eq736 : a = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq735 ac -- subsumption resolution 735,47
  have eq829 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq475 eq172 -- resolution 475,172
  have eq838 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ c = sk3 ∨ c = sk4 ∨ c = sk2 := resolve eq829 rfl -- duplicate literal removal 829
  have eq919 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq482 eq173 -- resolution 482,173
  have eq931 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ b = sk1 ∨ a = sk1 := resolve eq919 rfl -- duplicate literal removal 919
  have eq978 : c = sk1 ∨ b = sk1 ∨ a = sk1 ∨ (new sk1 sk4 sk0) := resolve eq931 imp_new_0 -- resolution 931,57
  have eq980 : b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq978 preserve_3 -- subsumption resolution 978,73
  have eq991 : (new sk2 b sk3) ∨ c = sk1 ∨ a = sk1 := eq980.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 72,980, 980 into 72, unify on (0).2 in 980 and (0).2 in 72
  have eq1132 : (new a b sk3) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq736.imp_left (fun h : a = sk2 ↦ superpose h eq991)) -- superposition 991,736, 736 into 991, unify on (0).2 in 736 and (0).1 in 991
  have eq1140 : (new a b sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq1132 rfl -- duplicate literal removal 1132
  have eq1165 : c = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq1140 eq86 -- resolution 1140,86
  have eq1174 : (sP1 sk1 c sk4) ∨ (old sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq1165.imp_left (fun h : c = sk3 ↦ superpose h eq100)) -- superposition 100,1165, 1165 into 100, unify on (0).2 in 1165 and (0).2 in 100
  have eq1223 : (sP1 sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ a = sk1 ∨ c = sk1 := resolve eq1174 p4XZ -- subsumption resolution 1174,51
  have eq1224 : (sP1 sk1 c sk4) ∨ a = sk1 ∨ c = sk1 := resolve eq1223 rule_def_0_0 -- subsumption resolution 1223,59
  have eq1225 : c = sk1 ∨ a = sk1 := resolve eq1224 rule_def_1_0 -- subsumption resolution 1224,63
  have eq1239 : (old c sk3 sk4) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq1225.imp_left (fun h : c = sk1 ↦ superpose h eq117)) -- superposition 117,1225, 1225 into 117, unify on (0).2 in 1225 and (0).1 in 117
  have eq1286 : a = c ∨ a = sk1 := resolve eq1239 p4YZ -- subsumption resolution 1239,52
  have eq1287 : a = sk1 := resolve eq1286 ac -- subsumption resolution 1286,47
  have eq1291 : ¬(new a sk4 sk0) := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 73,1287
  have eq1307 : (old sk2 a sk3) ∨ a = sk2 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq125 -- backward demodulation 125,1287
  have eq1321 : (old sk0 a sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq172 -- backward demodulation 172,1287
  have eq1325 : ∀ (X0 : G) , a = c ∨ ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq179 -- backward demodulation 179,1287
  have eq1328 : (old a sk3 sk4) ∨ c = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq183 -- backward demodulation 183,1287
  have eq1333 : (old sk2 a sk3) ∨ c = sk1 ∨ c = sk3 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq192 -- backward demodulation 192,1287
  have eq1334 : (old sk2 a sk3) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq193 -- backward demodulation 193,1287
  have eq1376 : (sP1 a c sk4) ∨ (old a sk3 sk4) ∨ c = sk4 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq267 -- backward demodulation 267,1287
  have eq1378 : (sP1 a c sk4) ∨ (old a sk3 sk4) ∨ b = sk3 ∨ (sP0 a c sk4) := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq270 -- backward demodulation 270,1287
  have eq1514 : a = c ∨ (old sk1 sk4 sk0) ∨ c = sk3 ∨ c = sk4 ∨ c = sk2 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq838 -- backward demodulation 838,1287
  have eq1664 : a = c ∨ (old sk0 a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1321 -- forward demodulation 1321,1287
  have eq1665 : (old sk0 a sk2) ∨ c = sk2 := resolve eq1664 ac -- subsumption resolution 1664,47
  have eq1676 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 := resolve eq1325 ac -- subsumption resolution 1325,47
  have eq1677 : ∀ (X0 : G) , ¬(old X0 a sk2) ∨ c = sk2 ∨ sk0 = X0 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1676 -- forward demodulation 1676,1287
  have eq1695 : a = c ∨ (old sk2 a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1333 -- forward demodulation 1333,1287
  have eq1696 : (old sk2 a sk3) ∨ c = sk3 := resolve eq1695 ac -- subsumption resolution 1695,47
  have eq1697 : a = c ∨ (old sk2 a sk3) ∨ b = sk1 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1334 -- forward demodulation 1334,1287
  have eq1698 : (old sk2 a sk3) ∨ b = sk1 := resolve eq1697 ac -- subsumption resolution 1697,47
  have eq1699 : (old sk2 a sk3) ∨ a = b := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1698 -- forward demodulation 1698,1287
  have eq1831 : (old sk1 sk4 sk0) ∨ c = sk3 ∨ c = sk4 ∨ c = sk2 := resolve eq1514 ac -- subsumption resolution 1514,47
  have eq1832 : (old a sk4 sk0) ∨ c = sk3 ∨ c = sk4 ∨ c = sk2 := Eq.mp (by simp only [eq1287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1831 -- forward demodulation 1831,1287
  have eq2391 : c = sk3 ∨ c = sk4 ∨ c = sk2 ∨ (new a sk4 sk0) := resolve eq1832 imp_new_0 -- resolution 1832,57
  have eq2392 : c = sk4 ∨ c = sk3 ∨ c = sk2 := resolve eq2391 eq1291 -- subsumption resolution 2391,1291
  have eq2397 : ¬(new a c sk0) ∨ c = sk3 ∨ c = sk2 := eq2392.imp_left (fun h : c = sk4 ↦ superpose h eq1291) -- superposition 1291,2392, 2392 into 1291, unify on (0).2 in 2392 and (0).2 in 1291
  have eq2398 : (old a sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk2 := Or.assoc3 (eq2392.imp_left (fun h : c = sk4 ↦ superpose h eq1328)) -- superposition 1328,2392, 2392 into 1328, unify on (0).2 in 2392 and (0).3 in 1328
  have eq2417 : (old a sk3 c) ∨ c = sk3 ∨ b = sk3 ∨ c = sk2 := resolve eq2398 rfl -- duplicate literal removal 2398
  have eq2418 : b = sk3 ∨ c = sk3 ∨ c = sk2 := resolve eq2417 p4XY -- subsumption resolution 2417,50
  have eq2441 : (old sk2 a b) ∨ c = b ∨ c = sk3 ∨ c = sk2 := Or.assoc2 (eq2418.imp_left (fun h : b = sk3 ↦ superpose h eq1696)) -- superposition 1696,2418, 2418 into 1696, unify on (0).2 in 2418 and (0).3 in 1696
  have eq2455 : (old sk2 a b) ∨ c = sk3 ∨ c = sk2 := resolve eq2441 bc -- subsumption resolution 2441,48
  have eq2742 (X0 : G) : ¬(old X0 a sk2) ∨ c = sk2 ∨ (new a c X0) ∨ c = sk3 := resolve eq2455 eq78 -- resolution 2455,78
  have eq4836 : c = sk2 ∨ (new a c sk0) ∨ c = sk3 ∨ c = sk2 := resolve eq2742 eq1665 -- resolution 2742,1665
  have eq4839 : c = sk2 ∨ (new a c sk0) ∨ c = sk3 := resolve eq4836 rfl -- duplicate literal removal 4836
  have eq4841 : c = sk3 ∨ c = sk2 := resolve eq4839 eq2397 -- subsumption resolution 4839,2397
  have eq4851 : (old sk2 a c) ∨ a = sk2 ∨ c = sk2 := Or.assoc2 (eq4841.imp_left (fun h : c = sk3 ↦ superpose h eq1307)) -- superposition 1307,4841, 4841 into 1307, unify on (0).2 in 4841 and (0).3 in 1307
  have eq4867 : c = sk2 ∨ a = sk2 := resolve eq4851 p4XY -- subsumption resolution 4851,50
  have eq4885 : (old c a sk3) ∨ a = c ∨ a = sk2 := Or.assoc2 (eq4867.imp_left (fun h : c = sk2 ↦ superpose h eq1307)) -- superposition 1307,4867, 4867 into 1307, unify on (0).2 in 4867 and (0).1 in 1307
  have eq4936 : a = c ∨ a = sk2 := resolve eq4885 p4YZ -- subsumption resolution 4885,52
  have eq4937 : a = sk2 := resolve eq4936 ac -- subsumption resolution 4936,47
  have eq4957 : ∀ (X0 : G) , a = c ∨ ¬(old X0 a sk2) ∨ sk0 = X0 := Eq.mp (by simp only [eq4937, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1677 -- backward demodulation 1677,4937
  have eq4964 : (old a a sk3) ∨ a = b := Eq.mp (by simp only [eq4937, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1699 -- backward demodulation 1699,4937
  have eq5045 : a = c ∨ c = sk3 := Eq.mp (by simp only [eq4937, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4841 -- backward demodulation 4841,4937
  have eq5066 (X0 : G) : ¬(old X0 a sk2) ∨ sk0 = X0 := resolve eq4957 ac -- subsumption resolution 4957,47
  have eq5067 : ∀ (X0 : G) , ¬(old X0 a a) ∨ sk0 = X0 := Eq.mp (by simp only [eq4937, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5066 -- forward demodulation 5066,4937
  have eq5118 : c = sk3 := resolve eq5045 ac -- subsumption resolution 5045,47
  have eq5124 : (old a c sk4) ∨ (sP1 a c sk4) ∨ c = sk4 := Eq.mp (by simp only [eq5118, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1376 -- backward demodulation 1376,5118
  have eq5126 : c = b ∨ (sP1 a c sk4) ∨ (old a sk3 sk4) ∨ (sP0 a c sk4) := Eq.mp (by simp only [eq5118, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1378 -- backward demodulation 1378,5118
  have eq5190 : (old a a c) ∨ a = b := Eq.mp (by simp only [eq5118, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4964 -- backward demodulation 4964,5118
  have eq5199 : (sP1 a c sk4) ∨ c = sk4 := resolve eq5124 p4XZ -- subsumption resolution 5124,51
  have eq5200 : (sP1 a c sk4) ∨ (old a sk3 sk4) ∨ (sP0 a c sk4) := resolve eq5126 bc -- subsumption resolution 5126,48
  have eq5201 : (old a c sk4) ∨ (sP1 a c sk4) ∨ (sP0 a c sk4) := Eq.mp (by simp only [eq5118, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5200 -- forward demodulation 5200,5118
  have eq5202 : (sP1 a c sk4) ∨ (sP0 a c sk4) := resolve eq5201 p4XZ -- subsumption resolution 5201,51
  have eq5259 : a = b := resolve eq5190 p4XY -- subsumption resolution 5190,50
  have eq5262 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq5259, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 60,5259
  have eq5263 : ∀ (X0 X1 X2 : G) , (old (sF0 X0 X1 X2) a a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq5259, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_3 -- backward demodulation 66,5259
  have eq5313 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (old a X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve eq5263 eq90 -- resolution 5263,90
  have eq5320 (X0 X1 X2 : G) : (old a X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve eq5313 rfl -- duplicate literal removal 5313
  have eq5341 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ sk0 = (sF0 X0 X1 X2) := resolve eq5067 eq5263 -- resolution 5067,5263
  have eq5374 (X0 X1 X2 : G) : (new a X2 (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve eq5320 imp_new_0 -- resolution 5320,57
  have eq5390 : sk0 = (sF0 a c sk4) ∨ c = sk4 := resolve eq5341 eq5199 -- resolution 5341,5199
  have eq5417 : (new a sk4 sk0) ∨ ¬(sP1 a c sk4) ∨ c = sk4 := Or.assoc2 (eq5390.imp_left (fun h : sk0 = (sF0 a c sk4) ↦ superpose h eq5374)) -- superposition 5374,5390, 5390 into 5374, unify on (0).2 in 5390 and (0).3 in 5374
  have eq5418 : ¬(sP1 a c sk4) ∨ c = sk4 := resolve eq5417 eq1291 -- subsumption resolution 5417,1291
  have eq5419 : c = sk4 := resolve eq5418 eq5199 -- subsumption resolution 5418,5199
  have eq5428 : (sP0 a c c) ∨ (sP1 a c sk4) := Eq.mp (by simp only [eq5419, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5202 -- backward demodulation 5202,5419
  have eq5441 : (sP1 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq5419, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5428 -- forward demodulation 5428,5419
  have eq5442 : (sP0 a c c) := resolve eq5441 eq82 -- subsumption resolution 5441,82
  have eq5448 : a = c := resolve eq5442 eq5262 -- resolution 5442,5262
  subsumption ac eq5448 -- subsumption resolution 5448,47

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X0 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq99 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 69,72
  have eq100 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 69,73
  have eq115 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq99 rule_def_1_1 -- resolution 99,65
  have eq116 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq99 rule_def_1_0 -- resolution 99,64
  have eq117 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq116 rule_def_0_0 -- subsumption resolution 116,60
  have eq120 (X0 : G) : ¬(old X0 sk1 sk2) ∨ sk0 = X0 ∨ a = sk0 := resolve eq117 old_2 -- resolution 117,56
  have eq123 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 := resolve eq100 rule_def_1_1 -- resolution 100,65
  have eq124 : (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ a = sk3 := resolve eq100 rule_def_1_0 -- resolution 100,64
  have eq125 : (old sk3 sk1 sk2) ∨ a = sk3 := resolve eq124 rule_def_0_0 -- subsumption resolution 124,60
  have eq128 (X0 : G) : ¬(old X0 sk1 sk2) ∨ sk3 = X0 ∨ a = sk3 := resolve eq125 old_2 -- resolution 125,56
  have eq166 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq115 rule_def_0_2 -- resolution 115,62
  have eq174 : c = sk1 ∨ c = sk2 ∨ sk0 = sk3 ∨ a = sk3 := resolve eq166 eq128 -- resolution 166,128
  have eq181 : a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq174 preserve_2 -- subsumption resolution 174,74
  have eq186 : a ≠ sk0 ∨ c = sk2 ∨ c = sk1 := eq181.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 74,181, 181 into 74, unify on (0).2 in 181 and (0).2 in 74
  have eq191 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq123 rule_def_0_2 -- resolution 123,62
  have eq227 : c = sk1 ∨ c = sk2 ∨ sk0 = sk3 ∨ a = sk0 := resolve eq191 eq120 -- resolution 191,120
  have eq238 : c = sk1 ∨ c = sk2 ∨ a = sk0 := resolve eq227 preserve_2 -- subsumption resolution 227,74
  have eq239 : c = sk2 ∨ c = sk1 := resolve eq238 eq186 -- subsumption resolution 238,186
  have eq248 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 := Or.assoc2 (eq239.imp_left (fun h : c = sk2 ↦ superpose h eq117)) -- superposition 117,239, 239 into 117, unify on (0).2 in 239 and (0).3 in 117
  have eq251 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 := Or.assoc2 (eq239.imp_left (fun h : c = sk2 ↦ superpose h eq125)) -- superposition 125,239, 239 into 125, unify on (0).2 in 239 and (0).3 in 125
  have eq263 : c = sk1 ∨ a = sk0 := resolve eq248 p4XY -- subsumption resolution 248,51
  have eq264 : a = sk3 ∨ c = sk1 := resolve eq251 p4XY -- subsumption resolution 251,51
  have eq272 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 := Or.assoc3 (eq263.imp_left (fun h : c = sk1 ↦ superpose h eq99)) -- superposition 99,263, 263 into 99, unify on (0).2 in 263 and (0).2 in 99
  have eq289 : (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 := resolve eq272 p4XZ -- subsumption resolution 272,52
  have eq290 : (sP1 sk0 c sk2) ∨ a = sk0 := resolve eq289 rule_def_0_0 -- subsumption resolution 289,60
  have eq291 : a = sk0 := resolve eq290 rule_def_1_0 -- subsumption resolution 290,64
  have eq293 : a ≠ sk3 := Eq.mp (by simp only [eq291, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 74,291
  have eq348 : a ≠ a ∨ c = sk1 := eq264.imp_left (fun h : a = sk3 ↦ superpose h eq293) -- superposition 293,264, 264 into 293, unify on (0).2 in 264 and (0).2 in 293
  have eq349 : c = sk1 := resolve eq348 rfl -- trivial inequality removal 348
  have eq357 : (old sk3 c sk2) ∨ a = sk3 := Eq.mp (by simp only [eq349, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq125 -- backward demodulation 125,349
  have eq387 : a = sk3 := resolve eq357 p4XZ -- subsumption resolution 357,52
  subsumption eq293 eq387 -- subsumption resolution 387,293

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1 X2, ¬ old X0 X1 X1 ∨ ¬ old X2 X1 X0 ∨ old X1 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X1 X1 ∨ ¬ new X2 X1 X0 ∨ new X1 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq86 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 68,55
  have eq106 : (sP1 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) := resolve new_imp preserve_0 -- resolution 71,75
  have eq107 : (sP1 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ (sP0 sk2 sk1 sk0) := resolve new_imp preserve_1 -- resolution 71,76
  have eq126 : (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ c = sk1 := resolve eq106 rule_def_1_1 -- resolution 106,67
  have eq127 : (old sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ a = sk0 := resolve eq106 rule_def_1_0 -- resolution 106,66
  have eq128 : (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq126 rule_def_0_2 -- subsumption resolution 126,64
  have eq129 : (old sk0 sk1 sk1) ∨ a = sk0 := resolve eq127 rule_def_0_0 -- subsumption resolution 127,62
  have eq135 : (sP0 sk2 sk1 sk0) ∨ (old sk2 sk1 sk0) ∨ c = sk1 := resolve eq107 rule_def_1_1 -- resolution 107,67
  have eq178 : (old sk2 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq135 rule_def_0_2 -- resolution 135,64
  have eq188 : c = sk1 ∨ c = sk0 ∨ (old sk1 sk2 sk0) ∨ ¬(old sk0 sk1 sk1) := resolve eq178 old_3 -- resolution 178,59
  have eq192 : (old sk1 sk2 sk0) ∨ c = sk0 ∨ c = sk1 := resolve eq188 eq128 -- subsumption resolution 188,128
  have eq210 : c = sk0 ∨ c = sk1 ∨ (new sk1 sk2 sk0) := resolve eq192 imp_new_0 -- resolution 192,60
  have eq211 : c = sk1 ∨ c = sk0 := resolve eq210 preserve_2 -- subsumption resolution 210,77
  have eq225 : (old sk0 c c) ∨ a = sk0 ∨ c = sk0 := Or.assoc2 (eq211.imp_left (fun h : c = sk1 ↦ superpose h eq129)) -- superposition 129,211, 211 into 129, unify on (0).2 in 211 and (0).2 in 129
  have eq235 : c = sk0 ∨ a = sk0 := resolve eq225 p4XZ -- subsumption resolution 225,54
  have eq248 : (old c sk1 sk1) ∨ a = c ∨ a = sk0 := Or.assoc2 (eq235.imp_left (fun h : c = sk0 ↦ superpose h eq129)) -- superposition 129,235, 235 into 129, unify on (0).2 in 235 and (0).1 in 129
  have eq260 : a = c ∨ a = sk0 := resolve eq248 p4YZ -- subsumption resolution 248,55
  have eq261 : a = sk0 := resolve eq260 ac -- subsumption resolution 260,50
  have eq269 : (sP0 a sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) := Eq.mp (by simp only [eq261, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq106 -- backward demodulation 106,261
  have eq307 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq261, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq211 -- backward demodulation 211,261
  have eq322 : (sP1 a sk1 sk1) ∨ (sP0 a sk1 sk1) ∨ (old sk0 sk1 sk1) := Eq.mp (by simp only [eq261, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq269 -- forward demodulation 269,261
  have eq323 : (old a sk1 sk1) ∨ (sP1 a sk1 sk1) ∨ (sP0 a sk1 sk1) := Eq.mp (by simp only [eq261, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq322 -- forward demodulation 322,261
  have eq359 : c = sk1 := resolve eq307 ac -- subsumption resolution 307,50
  have eq374 : (sP0 a c c) ∨ (old a sk1 sk1) ∨ (sP1 a sk1 sk1) := Eq.mp (by simp only [eq359, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq323 -- backward demodulation 323,359
  have eq397 : (old a c c) ∨ (sP0 a c c) ∨ (sP1 a sk1 sk1) := Eq.mp (by simp only [eq359, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq374 -- forward demodulation 374,359
  have eq398 : (sP0 a c c) ∨ (sP1 a sk1 sk1) := resolve eq397 p4XZ -- subsumption resolution 397,54
  have eq399 : (sP1 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq359, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq398 -- forward demodulation 398,359
  have eq400 : (sP0 a c c) := resolve eq399 eq86 -- subsumption resolution 399,86
  have eq462 : c = b := resolve eq400 rule_def_0_1 -- resolution 400,63
  subsumption bc eq462 -- subsumption resolution 462,51

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq105 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq118 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq105 rule_def_1_0 -- resolution 105,68
  have eq120 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq118 preserve_1 -- subsumption resolution 118,78
  have eq134 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq120 rule_def_0_0 -- resolution 120,64
  have eq135 : (old sk0 sk1 sk2) := resolve eq134 preserve_1 -- subsumption resolution 134,78
  have eq149 : memold sk0 := resolve eq135 old_mem1 -- resolution 135,74
  subsumption preserve_3 eq149 -- subsumption resolution 149,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq105 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq117 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq105 rule_def_1_1 -- resolution 105,69
  have eq120 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq117 preserve_4 -- subsumption resolution 117,81
  have eq130 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq120 rule_def_0_1 -- resolution 120,65
  have eq132 : (old sk0 sk1 sk2) := resolve eq130 preserve_2 -- subsumption resolution 130,79
  have eq142 : memold sk1 := resolve eq132 old_mem2 -- resolution 132,75
  subsumption preserve_3 eq142 -- subsumption resolution 142,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq92 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X2 := resolve rule_def_1_2 old_mem1 -- resolution 70,74
  have eq105 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq115 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk2 := resolve eq105 eq92 -- resolution 105,92
  have eq119 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq115 preserve_3 -- subsumption resolution 115,80
  have eq120 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq119 rule_def_0_2 -- resolution 119,66
  have eq123 : (old sk0 sk1 sk2) := resolve eq120 preserve_4 -- subsumption resolution 120,81
  have eq133 : memold sk2 := resolve eq123 old_mem3 -- resolution 123,76
  subsumption preserve_3 eq133 -- subsumption resolution 133,80

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X3 X4 ∨ ¬ R X2 X1 X3 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X0 = X3)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X1 X1 ∨ ¬ R X2 X1 X0 ∨ R X1 X2 X0)
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
  let sP1 (X Y Z) := ∃ sF0, a = X ∧ c = Y ∧ ps.R Z a sF0 ∧ ps.R sF0 a b
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_2 ps.rule_3 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 p4XY p4XZ ps.rule_2 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p4XZ p4YZ ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_0 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_2 rule_def_1_2 new_imp ps.mem_1 ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X3 X4 ∨ ¬ ps.compl X2 X1 X3 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X3) (max (Nat.pair X2 X1) (max (Nat.pair X1 X4) 0)))
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

theorem PartialSolution.toMagma_equation707 :
    letI := ps.toMagma
    Equation707 ℕ := by
  simp only [Equation707, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun (ps.complFun X0 X1) X1) (ps.complFun X1 (ps.complFun (ps.complFun X0 X1) X1))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1223 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (1, 3, 2), (1, 4, 3), (2, 1, 3), (2, 3, 1), (3, 1, 4), (3, 4, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3, 4}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation707_not_implies_Equation1223 : ∃ (G : Type) (_ : Magma G), Equation707 G ∧ ¬Equation1223 G := by
  use ℕ, PartialSolution.counter1223.toMagma, PartialSolution.counter1223.toMagma_equation707
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter1223.of_R 1 1 2] | rw [PartialSolution.counter1223.of_R 1 2 1] | rw [PartialSolution.counter1223.of_R 1 3 2] | rw [PartialSolution.counter1223.of_R 1 4 3] | rw [PartialSolution.counter1223.of_R 2 1 3] | rw [PartialSolution.counter1223.of_R 2 3 1] | rw [PartialSolution.counter1223.of_R 3 1 4] | rw [PartialSolution.counter1223.of_R 3 4 1])
  all_goals simp [PartialSolution.counter1223]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1316 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation707_not_implies_Equation1316 : ∃ (G : Type) (_ : Magma G), Equation707 G ∧ ¬Equation1316 G := by
  use ℕ, PartialSolution.counter1316.toMagma, PartialSolution.counter1316.toMagma_equation707
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter1316.of_R 1 1 1] | rw [PartialSolution.counter1316.of_R 1 2 1])
  all_goals simp [PartialSolution.counter1316]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2238 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3), (2, 3, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation707_not_implies_Equation2238 : ∃ (G : Type) (_ : Magma G), Equation707 G ∧ ¬Equation2238 G := by
  use ℕ, PartialSolution.counter2238.toMagma, PartialSolution.counter2238.toMagma_equation707
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2238.of_R 1 1 2] | rw [PartialSolution.counter2238.of_R 1 2 1] | rw [PartialSolution.counter2238.of_R 2 1 3] | rw [PartialSolution.counter2238.of_R 2 3 1])
  all_goals simp [PartialSolution.counter2238]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2847 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3), (2, 3, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation707_not_implies_Equation2847 : ∃ (G : Type) (_ : Magma G), Equation707 G ∧ ¬Equation2847 G := by
  use ℕ, PartialSolution.counter2847.toMagma, PartialSolution.counter2847.toMagma_equation707
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2847.of_R 1 1 2] | rw [PartialSolution.counter2847.of_R 1 2 1] | rw [PartialSolution.counter2847.of_R 2 1 3] | rw [PartialSolution.counter2847.of_R 2 3 1])
  all_goals simp [PartialSolution.counter2847]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2940 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation707_not_implies_Equation2940 : ∃ (G : Type) (_ : Magma G), Equation707 G ∧ ¬Equation2940 G := by
  use ℕ, PartialSolution.counter2940.toMagma, PartialSolution.counter2940.toMagma_equation707
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter2940.of_R 1 1 1] | rw [PartialSolution.counter2940.of_R 1 2 1])
  all_goals simp [PartialSolution.counter2940]

end Eq707