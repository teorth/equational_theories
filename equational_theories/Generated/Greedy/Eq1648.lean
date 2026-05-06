import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq1648

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq68 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 59,60
  have eq69 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 59,61
  have eq76 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk2 b a) := resolve eq68 rule_def_1_2 -- resolution 68,57
  have eq77 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq68 rule_def_1_1 -- resolution 68,56
  have eq78 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq68 rule_def_1_0 -- resolution 68,55
  have eq79 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq78 rule_def_0_0 -- subsumption resolution 78,51
  have eq83 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk3 b a) := resolve eq69 rule_def_1_2 -- resolution 69,57
  have eq84 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ c = sk1 := resolve eq69 rule_def_1_1 -- resolution 69,56
  have eq85 : (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ a = sk0 := resolve eq69 rule_def_1_0 -- resolution 69,55
  have eq86 : (old sk0 sk1 sk3) ∨ a = sk0 := resolve eq85 rule_def_0_0 -- subsumption resolution 85,51
  have eq89 (X0 : G) : ¬(old sk0 sk1 X0) ∨ sk2 = X0 ∨ a = sk0 := resolve eq79 old_0 -- resolution 79,46
  have eq97 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq77 rule_def_0_2 -- resolution 77,53
  have eq98 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq77 rule_def_0_1 -- resolution 77,52
  have eq101 : sk2 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq89 eq86 -- resolution 89,86
  have eq102 : sk2 = sk3 ∨ a = sk0 := resolve eq101 rfl -- duplicate literal removal 101
  have eq104 : a = sk0 := resolve eq102 preserve_2 -- subsumption resolution 102,62
  have eq109 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq76 -- backward demodulation 76,104
  have eq112 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (old sk3 b a) := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq83 -- backward demodulation 83,104
  have eq113 : (sP0 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq84 -- backward demodulation 84,104
  have eq115 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq97 -- backward demodulation 97,104
  have eq116 : (old a sk1 sk2) ∨ c = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq98 -- backward demodulation 98,104
  have eq121 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq109 -- forward demodulation 109,104
  have eq123 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (old sk3 b a) := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq112 -- forward demodulation 112,104
  have eq124 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq104, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq113 -- forward demodulation 113,104
  have eq129 (X0 : G) : ¬(old a sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq115 old_0 -- resolution 115,46
  have eq144 : (old a sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq124 rule_def_0_2 -- resolution 124,53
  have eq145 : (old a sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq124 rule_def_0_1 -- resolution 124,52
  have eq152 : (old sk2 b a) ∨ (old a sk1 sk2) ∨ b = sk1 := resolve eq121 rule_def_0_1 -- resolution 121,52
  have eq158 : (old sk3 b a) ∨ (old a sk1 sk3) ∨ c = sk3 := resolve eq123 rule_def_0_2 -- resolution 123,53
  have eq159 : (old sk3 b a) ∨ (old a sk1 sk3) ∨ b = sk1 := resolve eq123 rule_def_0_1 -- resolution 123,52
  have eq168 (X0 : G) : (old a sk1 sk2) ∨ b = sk1 ∨ sk2 = X0 ∨ ¬(old X0 b a) := resolve eq152 old_2 -- resolution 152,48
  have eq207 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq129 eq145 -- resolution 129,145
  have eq210 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq207 rfl -- duplicate literal removal 207
  have eq213 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq210 preserve_2 -- subsumption resolution 210,62
  have eq216 : (old a sk1 c) ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq213.imp_left (fun h : c = sk2 ↦ superpose h eq116)) -- superposition 116,213, 213 into 116, unify on (0).2 in 213 and (0).3 in 116
  have eq227 : (old a sk1 c) ∨ c = sk1 ∨ b = sk1 := resolve eq216 rfl -- duplicate literal removal 216
  have eq228 : b = sk1 ∨ c = sk1 := resolve eq227 p4XY -- subsumption resolution 227,43
  have eq237 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq228.imp_left (fun h : b = sk1 ↦ superpose h eq115)) -- superposition 115,228, 228 into 115, unify on (0).2 in 228 and (0).2 in 115
  have eq246 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq228.imp_left (fun h : b = sk1 ↦ superpose h eq144)) -- superposition 144,228, 228 into 144, unify on (0).2 in 228 and (0).2 in 144
  have eq248 : c = b ∨ c = sk2 ∨ c = sk1 := resolve eq237 p3 -- subsumption resolution 237,42
  have eq249 : c = sk2 ∨ c = sk1 := resolve eq248 bc -- subsumption resolution 248,41
  have eq258 : c = b ∨ c = sk3 ∨ c = sk1 := resolve eq246 p3 -- subsumption resolution 246,42
  have eq259 : c = sk3 ∨ c = sk1 := resolve eq258 bc -- subsumption resolution 258,41
  have eq287 : c ≠ sk2 ∨ c = sk1 := eq259.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 62,259, 259 into 62, unify on (0).2 in 259 and (0).2 in 62
  have eq298 : c = sk1 := resolve eq287 eq249 -- subsumption resolution 287,249
  have eq307 : (old a c sk3) ∨ (old sk3 b a) ∨ c = sk3 := Eq.mp (by simp only [eq298, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq158 -- backward demodulation 158,298
  have eq308 : c = b ∨ (old sk3 b a) ∨ (old a sk1 sk3) := Eq.mp (by simp only [eq298, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq159 -- backward demodulation 159,298
  have eq316 : ∀ (X0 : G) , c = b ∨ (old a sk1 sk2) ∨ sk2 = X0 ∨ ¬(old X0 b a) := Eq.mp (by simp only [eq298, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq168 -- backward demodulation 168,298
  have eq347 : (old sk3 b a) ∨ c = sk3 := resolve eq307 p4XZ -- subsumption resolution 307,44
  have eq348 : (old sk3 b a) ∨ (old a sk1 sk3) := resolve eq308 bc -- subsumption resolution 308,41
  have eq349 : (old a c sk3) ∨ (old sk3 b a) := Eq.mp (by simp only [eq298, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq348 -- forward demodulation 348,298
  have eq350 : (old sk3 b a) := resolve eq349 p4XZ -- subsumption resolution 349,44
  have eq358 (X0 : G) : (old a sk1 sk2) ∨ sk2 = X0 ∨ ¬(old X0 b a) := resolve eq316 bc -- subsumption resolution 316,41
  have eq359 : ∀ (X0 : G) , (old a c sk2) ∨ sk2 = X0 ∨ ¬(old X0 b a) := Eq.mp (by simp only [eq298, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq358 -- forward demodulation 358,298
  have eq360 (X0 : G) : ¬(old X0 b a) ∨ sk2 = X0 := resolve eq359 p4XZ -- subsumption resolution 359,44
  have eq424 : sk2 = sk3 ∨ c = sk3 := resolve eq360 eq347 -- resolution 360,347
  have eq426 : c = sk3 := resolve eq424 preserve_2 -- subsumption resolution 424,62
  have eq432 : (old c b a) := Eq.mp (by simp only [eq426, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq350 -- backward demodulation 350,426
  subsumption p4YZ eq432 -- subsumption resolution 432,45

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X2 X1 X3 ∨ old X2 X3 X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ ¬ old Z b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X2 X3 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq66 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 52
  have eq67 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq66 rfl -- equality resolution 66
  have eq68 : (new a b c) := resolve eq67 rfl -- equality resolution 67
  have eq69 (X0 X2 : G) : (new X0 c X2) ∨ ¬(old X2 b a) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 56
  have eq70 (X2 : G) : ¬(old X2 b a) ∨ (new a c X2) := resolve eq69 rfl -- equality resolution 69
  have eq73 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq68 -- resolution 62,68
  have eq75 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 61,63
  have eq76 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) := resolve new_imp preserve_1 -- resolution 61,64
  have eq85 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 b a) := resolve eq75 rule_def_1_2 -- resolution 75,59
  have eq86 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq75 rule_def_1_1 -- resolution 75,58
  have eq93 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq76 rule_def_1_1 -- resolution 76,58
  have eq94 : (old sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ a = sk2 := resolve eq76 rule_def_1_0 -- resolution 76,57
  have eq95 : (old sk2 sk1 sk3) ∨ a = sk2 := resolve eq94 rule_def_0_0 -- subsumption resolution 94,53
  have eq100 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk2 sk3 X0) ∨ a = sk2 := resolve eq95 old_1 -- resolution 95,49
  have eq106 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq86 rule_def_0_2 -- resolution 86,55
  have eq107 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq86 rule_def_0_1 -- resolution 86,54
  have eq112 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq93 rule_def_0_1 -- resolution 93,54
  have eq116 : (old sk2 b a) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq85 rule_def_0_2 -- resolution 85,55
  have eq144 (X0 : G) : ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 sk3 X0) ∨ c = sk1 := resolve eq112 old_1 -- resolution 112,49
  have eq149 : (old sk2 sk3 sk0) ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := resolve eq100 eq106 -- resolution 100,106
  have eq354 : a = sk2 ∨ c = sk1 ∨ c = sk2 ∨ (new sk2 sk3 sk0) := resolve eq149 imp_new_0 -- resolution 149,51
  have eq355 : c = sk2 ∨ c = sk1 ∨ a = sk2 := resolve eq354 preserve_2 -- subsumption resolution 354,65
  have eq367 : (old c sk1 sk3) ∨ a = c ∨ c = sk1 ∨ a = sk2 := Or.assoc2 (eq355.imp_left (fun h : c = sk2 ↦ superpose h eq95)) -- superposition 95,355, 355 into 95, unify on (0).2 in 355 and (0).1 in 95
  have eq399 : a = c ∨ c = sk1 ∨ a = sk2 := resolve eq367 p4YZ -- subsumption resolution 367,47
  have eq400 : a = sk2 ∨ c = sk1 := resolve eq399 ac -- subsumption resolution 399,42
  have eq403 : (new a sk1 sk3) ∨ c = sk1 := eq400.imp_left (fun h : a = sk2 ↦ superpose h preserve_1) -- superposition 64,400, 400 into 64, unify on (0).2 in 400 and (0).1 in 64
  have eq404 : ¬(new a sk3 sk0) ∨ c = sk1 := eq400.imp_left (fun h : a = sk2 ↦ superpose h preserve_2) -- superposition 65,400, 400 into 65, unify on (0).2 in 400 and (0).1 in 65
  have eq414 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c ∨ c = sk1 := Or.assoc3 (eq400.imp_left (fun h : a = sk2 ↦ superpose h eq106)) -- superposition 106,400, 400 into 106, unify on (0).2 in 400 and (0).3 in 106
  have eq436 : (old sk0 sk1 a) ∨ c = sk1 ∨ a = c := resolve eq414 rfl -- duplicate literal removal 414
  have eq442 : (old sk0 sk1 a) ∨ c = sk1 := resolve eq436 ac -- subsumption resolution 436,42
  have eq463 : b = sk1 ∨ (old sk2 sk3 sk0) ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq144 eq107 -- resolution 144,107
  have eq474 : (old sk2 sk3 sk0) ∨ b = sk1 ∨ c = sk1 := resolve eq463 rfl -- duplicate literal removal 463
  have eq502 : b = sk1 ∨ c = sk1 ∨ (new sk2 sk3 sk0) := resolve eq474 imp_new_0 -- resolution 474,51
  have eq510 : b = sk1 ∨ c = sk1 := resolve eq502 preserve_2 -- subsumption resolution 502,65
  have eq553 : (new a b sk3) ∨ c = b ∨ c = sk1 := Or.assoc2 (eq510.imp_left (fun h : b = sk1 ↦ superpose h eq403)) -- superposition 403,510, 510 into 403, unify on (0).2 in 510 and (0).2 in 403
  have eq554 : (old sk0 b a) ∨ c = b ∨ c = sk1 := Or.assoc2 (eq510.imp_left (fun h : b = sk1 ↦ superpose h eq442)) -- superposition 442,510, 510 into 442, unify on (0).2 in 510 and (0).2 in 442
  have eq567 : (new a b sk3) ∨ c = sk1 := resolve eq553 bc -- subsumption resolution 553,43
  have eq568 : (old sk0 b a) ∨ c = sk1 := resolve eq554 bc -- subsumption resolution 554,43
  have eq615 : c = sk3 ∨ c = sk1 := resolve eq567 eq73 -- resolution 567,73
  have eq642 : ¬(new a c sk0) ∨ c = sk1 ∨ c = sk1 := Or.assoc2 (eq615.imp_left (fun h : c = sk3 ↦ superpose h eq404)) -- superposition 404,615, 615 into 404, unify on (0).2 in 615 and (0).2 in 404
  have eq649 : ¬(new a c sk0) ∨ c = sk1 := resolve eq642 rfl -- duplicate literal removal 642
  have eq665 : c = sk1 ∨ (new a c sk0) := resolve eq568 eq70 -- resolution 568,70
  have eq670 : c = sk1 := resolve eq665 eq649 -- subsumption resolution 665,649
  have eq682 : (old sk2 c sk3) ∨ a = sk2 := Eq.mp (by simp only [eq670, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq95 -- backward demodulation 95,670
  have eq693 : (old sk0 c sk2) ∨ (old sk2 b a) ∨ c = sk2 := Eq.mp (by simp only [eq670, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq116 -- backward demodulation 116,670
  have eq760 : a = sk2 := resolve eq682 p4XZ -- subsumption resolution 682,46
  have eq773 : (old sk2 b a) ∨ c = sk2 := resolve eq693 p4XZ -- subsumption resolution 693,46
  have eq774 : (old a b a) ∨ c = sk2 := Eq.mp (by simp only [eq760, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq773 -- forward demodulation 773,760
  have eq775 : c = sk2 := resolve eq774 p3 -- subsumption resolution 774,44
  have eq776 : a = c := Eq.mp (by simp only [eq760, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq775 -- forward demodulation 775,760
  subsumption ac eq776 -- subsumption resolution 776,42

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X3 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq82 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 63,66
  have eq83 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 63,67
  have eq92 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq82 rule_def_1_1 -- resolution 82,60
  have eq93 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq82 rule_def_1_0 -- resolution 82,59
  have eq94 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq93 rule_def_0_0 -- subsumption resolution 93,55
  have eq99 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 := resolve eq83 rule_def_1_1 -- resolution 83,60
  have eq100 : (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ a = sk3 := resolve eq83 rule_def_1_0 -- resolution 83,59
  have eq101 : (old sk3 sk1 sk2) ∨ a = sk3 := resolve eq100 rule_def_0_0 -- subsumption resolution 100,55
  have eq103 (X0 : G) : ¬(old X0 sk1 sk2) ∨ sk0 = X0 ∨ a = sk0 := resolve eq94 old_2 -- resolution 94,52
  have eq107 (X0 : G) : ¬(old X0 sk1 sk2) ∨ sk3 = X0 ∨ a = sk3 := resolve eq101 old_2 -- resolution 101,52
  have eq114 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq92 rule_def_0_2 -- resolution 92,57
  have eq123 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq99 rule_def_0_2 -- resolution 99,57
  have eq147 : c = sk1 ∨ c = sk2 ∨ sk0 = sk3 ∨ a = sk3 := resolve eq114 eq107 -- resolution 114,107
  have eq153 : a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq147 preserve_2 -- subsumption resolution 147,68
  have eq163 : a ≠ sk0 ∨ c = sk2 ∨ c = sk1 := eq153.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 68,153, 153 into 68, unify on (0).2 in 153 and (0).2 in 68
  have eq174 : c = sk1 ∨ c = sk2 ∨ sk0 = sk3 ∨ a = sk0 := resolve eq123 eq103 -- resolution 123,103
  have eq182 : c = sk1 ∨ c = sk2 ∨ a = sk0 := resolve eq174 preserve_2 -- subsumption resolution 174,68
  have eq183 : c = sk2 ∨ c = sk1 := resolve eq182 eq163 -- subsumption resolution 182,163
  have eq190 : (old sk0 sk1 c) ∨ a = sk0 ∨ c = sk1 := Or.assoc2 (eq183.imp_left (fun h : c = sk2 ↦ superpose h eq94)) -- superposition 94,183, 183 into 94, unify on (0).2 in 183 and (0).3 in 94
  have eq193 : (old sk3 sk1 c) ∨ a = sk3 ∨ c = sk1 := Or.assoc2 (eq183.imp_left (fun h : c = sk2 ↦ superpose h eq101)) -- superposition 101,183, 183 into 101, unify on (0).2 in 183 and (0).3 in 101
  have eq205 : c = sk1 ∨ a = sk0 := resolve eq190 p4XY -- subsumption resolution 190,47
  have eq206 : a = sk3 ∨ c = sk1 := resolve eq193 p4XY -- subsumption resolution 193,47
  have eq226 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 := Or.assoc3 (eq205.imp_left (fun h : c = sk1 ↦ superpose h eq82)) -- superposition 82,205, 205 into 82, unify on (0).2 in 205 and (0).2 in 82
  have eq241 : (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 := resolve eq226 p4XZ -- subsumption resolution 226,48
  have eq242 : (sP1 sk0 c sk2) ∨ a = sk0 := resolve eq241 rule_def_0_0 -- subsumption resolution 241,55
  have eq243 : a = sk0 := resolve eq242 rule_def_1_0 -- subsumption resolution 242,59
  have eq245 : a ≠ sk3 := Eq.mp (by simp only [eq243, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 68,243
  have eq286 : a ≠ a ∨ c = sk1 := eq206.imp_left (fun h : a = sk3 ↦ superpose h eq245) -- superposition 245,206, 206 into 245, unify on (0).2 in 206 and (0).2 in 245
  have eq287 : c = sk1 := resolve eq286 rfl -- trivial inequality removal 286
  have eq297 : (old sk3 c sk2) ∨ a = sk3 := Eq.mp (by simp only [eq287, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq101 -- backward demodulation 101,287
  have eq317 : a = sk3 := resolve eq297 p4XZ -- subsumption resolution 297,48
  subsumption eq245 eq317 -- subsumption resolution 317,245

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq81 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 67,71
  have eq93 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq81 rule_def_1_0 -- resolution 81,63
  have eq94 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq93 preserve_1 -- subsumption resolution 93,72
  have eq97 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq94 rule_def_0_0 -- resolution 94,59
  have eq98 : (old sk0 sk1 sk2) := resolve eq97 preserve_1 -- subsumption resolution 97,72
  have eq106 : memold sk0 := resolve eq98 old_mem1 -- resolution 98,68
  subsumption preserve_3 eq106 -- subsumption resolution 106,74

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq81 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 67,71
  have eq92 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq81 rule_def_1_1 -- resolution 81,64
  have eq94 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq92 preserve_4 -- subsumption resolution 92,75
  have eq96 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq94 rule_def_0_1 -- resolution 94,60
  have eq98 : (old sk0 sk1 sk2) := resolve eq96 preserve_2 -- subsumption resolution 96,73
  have eq107 : memold sk1 := resolve eq98 old_mem2 -- resolution 98,69
  subsumption preserve_3 eq107 -- subsumption resolution 107,74

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (memold : G → Prop) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq81 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 67,71
  have eq91 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk2 b a) := resolve eq81 rule_def_1_2 -- resolution 81,65
  have eq92 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq81 rule_def_1_1 -- resolution 81,64
  have eq93 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq81 rule_def_1_0 -- resolution 81,63
  have eq94 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq93 rule_def_0_0 -- subsumption resolution 93,59
  have eq101 : a = sk0 ∨ memold sk2 := resolve eq94 old_mem3 -- resolution 94,70
  have eq102 : a = sk0 := resolve eq101 preserve_3 -- subsumption resolution 101,74
  have eq105 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq102, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq91 -- backward demodulation 91,102
  have eq106 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq102, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq92 -- backward demodulation 92,102
  have eq110 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq102, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq105 -- forward demodulation 105,102
  have eq111 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq102, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq106 -- forward demodulation 106,102
  have eq116 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq111 rule_def_0_2 -- resolution 111,61
  have eq119 : (old a sk1 sk2) ∨ c = sk1 := resolve eq116 preserve_4 -- subsumption resolution 116,75
  have eq120 : (old a sk1 sk2) ∨ (old sk2 b a) ∨ c = sk2 := resolve eq110 rule_def_0_2 -- resolution 110,61
  have eq123 : (old a sk1 sk2) ∨ (old sk2 b a) := resolve eq120 preserve_4 -- subsumption resolution 120,75
  have eq130 : c = sk1 ∨ memold sk2 := resolve eq119 old_mem3 -- resolution 119,70
  have eq131 : c = sk1 := resolve eq130 preserve_3 -- subsumption resolution 130,74
  have eq135 : (old a c sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq131, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq123 -- backward demodulation 123,131
  have eq141 : (old sk2 b a) := resolve eq135 p4XZ -- subsumption resolution 135,52
  have eq151 : memold sk2 := resolve eq141 old_mem1 -- resolution 141,68
  subsumption preserve_3 eq151 -- subsumption resolution 151,74

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X2 X1 X3 ∨ R X2 X3 X0)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X3 = X0)
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
  let sP1 (X Y Z) := a = X ∧ c = Y ∧ ps.R Z b a
  have hsP1 (X Y Z) (h : sP1 X Y Z) : a = X ∧ c = Y ∧ ps.R Z b a := h
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sP1 bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sP1 ac bc p3 p4XZ p4YZ prev_0 ps.rule_1 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sP1 p4XY p4XZ ps.rule_2 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_0 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sP1 (· ∈ ps.finsupp) p4XZ rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp ps.mem_1 ps.mem_3
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

theorem PartialSolution.compl_rule1 (X0 X1 X2 X3 : ℕ) :
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X2 X1 X3 ∨ ps.compl X2 X3 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X2 X1) (max (Nat.pair X2 X3) 0))
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

theorem PartialSolution.toMagma_equation1648 :
    letI := ps.toMagma
    Equation1648 ℕ := by
  simp only [Equation1648, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun (ps.complFun X0 X1) X1)


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3253 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (1, 3, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation1648_not_implies_Equation3253 : ∃ (G : Type) (_ : Magma G), Equation1648 G ∧ ¬Equation3253 G := by
  use ℕ, PartialSolution.counter3253.toMagma, PartialSolution.counter3253.toMagma_equation1648
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3253.of_R 1 1 2] | rw [PartialSolution.counter3253.of_R 1 2 3] | rw [PartialSolution.counter3253.of_R 1 3 3])
  all_goals simp [PartialSolution.counter3253]

end Eq1648
