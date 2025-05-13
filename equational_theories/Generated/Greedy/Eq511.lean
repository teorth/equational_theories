import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq511

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_12 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X2 ∨ ¬ old X4 X0 X1 ∨ ¬ old X5 X0 X3 ∨ X4 = X5)) (old_15 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X0 ∨ ¬ old X0 X2 X3 ∨ ¬ old X3 X0 X1 ∨ ¬ old X4 X0 X2 ∨ X0 = X4)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old a X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (imp_new_4 : ∀ X Y Z X3, b ≠ X ∨ c ≠ Y ∨ ¬ old a X3 a ∨ ¬ old b X3 a ∨ ¬ old Z b X3 ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a (sF4 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq162 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old a X3 b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 131
  have eq163 (X2 X3 : G) : ¬(old a X3 b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq162 rfl -- equality resolution 162
  have eq167 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 b X3) ∨ ¬(old b X3 a) ∨ ¬(old a X3 a) ∨ b ≠ X0 := resolve imp_new_4 rfl -- equality resolution 142
  have eq168 (X2 X3 : G) : ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ (new b c X2) ∨ ¬(old a X3 a) := resolve eq167 rfl -- equality resolution 167
  have eq175 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 134,109
  have eq179 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 145,118
  have eq189 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 147,109
  have eq198 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq163 rule_def_1_3 -- resolution 163,135
  have eq208 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 140,118
  have eq284 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(old a (sF3 X1 X2 X3) a) ∨ ¬(sP3 X1 X2 X3) := resolve eq168 rule_def_3_3 -- resolution 168,146
  have eq285 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP3 X1 X2 X3) := resolve eq284 rule_def_3_2 -- subsumption resolution 284,145
  have eq288 (X0 X1 X2 X3 X4 X5 : G) : ¬(old a (sF0 X3 X4 X1) X5) ∨ ¬(old X0 a X2) ∨ X0 = X1 ∨ ¬(old a X2 X5) ∨ ¬(sP1 X3 X4 X1) := resolve old_12 rule_def_1_2 -- resolution 122,134
  have eq289 (X0 X1 X2 X3 X4 X5 : G) : ¬(old b (sF3 X3 X4 X1) X5) ∨ ¬(old X0 b X2) ∨ X0 = X1 ∨ ¬(old b X2 X5) ∨ ¬(sP3 X3 X4 X1) := resolve old_12 rule_def_3_4 -- resolution 122,147
  have eq309 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq179 rule_def_3_3 -- resolution 179,146
  have eq310 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq309 rfl -- duplicate literal removal 309
  have eq312 (X0 X1 X2 X3 X4 : G) : ¬(old a (sF0 X3 X4 X0) X1) ∨ ¬(old X1 a X2) ∨ a = X0 ∨ ¬(old a X2 a) ∨ ¬(sP1 X3 X4 X0) := resolve old_15 rule_def_1_2 -- resolution 125,134
  have eq354 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 155,156
  have eq355 : (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 155,157
  have eq392 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq198 rule_def_1_2 -- resolution 198,134
  have eq393 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq392 rfl -- duplicate literal removal 392
  have eq396 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP3 X1 X2 X0) ∨ ¬(sP3 X1 X2 X0) := resolve eq285 rule_def_3_4 -- resolution 285,147
  have eq397 (X0 X1 X2 : G) : ¬(sP3 X1 X2 X0) ∨ (new b c X0) := resolve eq396 rfl -- duplicate literal removal 396
  have eq398 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq208 rule_def_2_4 -- resolution 208,141
  have eq401 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq398 rfl -- duplicate literal removal 398
  have eq451 (X0 X1 X2 X3 X4 : G) : ¬(old X0 a X1) ∨ X0 = X2 ∨ ¬(old a X1 b) ∨ ¬(sP1 X3 X4 X2) ∨ ¬(sP1 X3 X4 X2) := resolve eq288 rule_def_1_3 -- resolution 288,135
  have eq452 (X0 X1 X2 X3 X4 : G) : ¬(sP1 X3 X4 X2) ∨ X0 = X2 ∨ ¬(old a X1 b) ∨ ¬(old X0 a X1) := resolve eq451 rfl -- duplicate literal removal 451
  have eq455 (X0 X1 X2 X3 X4 : G) : ¬(old X0 b X1) ∨ X0 = X2 ∨ ¬(old b X1 a) ∨ ¬(sP3 X3 X4 X2) ∨ ¬(sP3 X3 X4 X2) := resolve eq289 rule_def_3_3 -- resolution 289,146
  have eq456 (X0 X1 X2 X3 X4 : G) : ¬(sP3 X3 X4 X2) ∨ X0 = X2 ∨ ¬(old b X1 a) ∨ ¬(old X0 b X1) := resolve eq455 rfl -- duplicate literal removal 455
  have eq465 (X0 X1 X2 X3 : G) : ¬(old b a X0) ∨ a = X1 ∨ ¬(old a X0 a) ∨ ¬(sP1 X2 X3 X1) ∨ ¬(sP1 X2 X3 X1) := resolve eq312 rule_def_1_3 -- resolution 312,135
  have eq466 (X0 X1 X2 X3 : G) : ¬(sP1 X2 X3 X1) ∨ a = X1 ∨ ¬(old a X0 a) ∨ ¬(old b a X0) := resolve eq465 rfl -- duplicate literal removal 465
  have eq472 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq354 rule_def_4_0 -- resolution 354,149
  have eq473 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq354 rule_def_4_1 -- resolution 354,150
  have eq474 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk2 := resolve eq354 rule_def_4_2 -- resolution 354,151
  have eq481 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq472 rule_def_0_0 -- subsumption resolution 472,128
  have eq482 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq481 rule_def_1_0 -- subsumption resolution 481,132
  have eq483 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq473 rule_def_1_1 -- subsumption resolution 473,133
  have eq484 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq483 rule_def_3_1 -- subsumption resolution 483,144
  have eq487 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq482 rule_def_3_0 -- resolution 482,143
  have eq492 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq482 eq310 -- resolution 482,310
  have eq496 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq487 rule_def_2_0 -- subsumption resolution 487,137
  have eq498 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq492 eq401 -- subsumption resolution 492,401
  have eq500 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ a = sk0 := resolve eq355 rule_def_4_0 -- resolution 355,149
  have eq501 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ c = sk1 := resolve eq355 rule_def_4_1 -- resolution 355,150
  have eq502 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ a = sk3 := resolve eq355 rule_def_4_2 -- resolution 355,151
  have eq509 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ a = sk0 := resolve eq500 rule_def_0_0 -- subsumption resolution 500,128
  have eq510 : (sP3 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ a = sk0 := resolve eq509 rule_def_1_0 -- subsumption resolution 509,132
  have eq511 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ c = sk1 := resolve eq501 rule_def_1_1 -- subsumption resolution 501,133
  have eq512 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq511 rule_def_3_1 -- subsumption resolution 511,144
  have eq515 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk0 ∨ sk2 = X0 ∨ a = sk0 := resolve eq496 old_0 -- resolution 496,110
  have eq530 (X0 : G) : ¬(old sk0 sk1 X0) ∨ a = b ∨ sk2 = X0 ∨ a = sk0 := resolve eq498 old_0 -- resolution 498,110
  have eq631 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b := resolve eq484 eq401 -- resolution 484,401
  have eq633 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq484 rule_def_2_2 -- resolution 484,139
  have eq634 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq484 rule_def_2_1 -- resolution 484,138
  have eq636 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq633 rule_def_0_2 -- subsumption resolution 633,130
  have eq732 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq631 rule_def_0_1 -- resolution 631,129
  have eq760 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq634 rule_def_0_1 -- resolution 634,129
  have eq813 : (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk0 := resolve eq510 rule_def_3_0 -- resolution 510,143
  have eq818 : (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ a = sk0 ∨ a = b := resolve eq510 eq310 -- resolution 510,310
  have eq822 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ b = sk0 := resolve eq813 rule_def_2_0 -- subsumption resolution 813,137
  have eq824 : (old sk0 sk1 sk3) ∨ a = sk0 ∨ a = b := resolve eq818 eq401 -- subsumption resolution 818,401
  have eq829 : a = sk0 ∨ b = sk0 ∨ b = sk0 ∨ sk2 = sk3 ∨ a = sk0 := resolve eq822 eq515 -- resolution 822,515
  have eq845 : a = sk0 ∨ b = sk0 ∨ sk2 = sk3 := resolve eq829 rfl -- duplicate literal removal 829
  have eq849 : b = sk0 ∨ a = sk0 := resolve eq845 preserve_2 -- subsumption resolution 845,158
  have eq869 : a ≠ b ∨ a = sk0 := resolve eq849 trans_resol -- equality factoring 849
  have eq912 : a = sk0 ∨ a = b ∨ a = b ∨ sk2 = sk3 ∨ a = sk0 := resolve eq824 eq530 -- resolution 824,530
  have eq934 : a = sk0 ∨ a = b ∨ sk2 = sk3 := resolve eq912 rfl -- duplicate literal removal 912
  have eq937 : a = sk0 ∨ a = b := resolve eq934 preserve_2 -- subsumption resolution 934,158
  have eq938 : a = sk0 := resolve eq937 eq869 -- subsumption resolution 937,869
  have eq941 : (sP3 a sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq354 -- backward demodulation 354,938
  have eq942 : (sP3 a sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq355 -- backward demodulation 355,938
  have eq943 : (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq474 -- backward demodulation 474,938
  have eq961 : (sP3 a sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq502 -- backward demodulation 502,938
  have eq968 : (sP2 a sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq512 -- backward demodulation 512,938
  have eq980 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq636 -- backward demodulation 636,938
  have eq997 : (old a sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq732 -- backward demodulation 732,938
  have eq1012 : (old a sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq760 -- backward demodulation 760,938
  have eq1052 : (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq941 -- forward demodulation 941,938
  have eq1053 : (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1052 -- forward demodulation 1052,938
  have eq1054 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1053 -- forward demodulation 1053,938
  have eq1055 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1054 -- forward demodulation 1054,938
  have eq1056 : (sP4 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1055 -- forward demodulation 1055,938
  have eq1057 : (sP4 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq942 -- forward demodulation 942,938
  have eq1058 : (sP2 a sk1 sk3) ∨ (sP4 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1057 -- forward demodulation 1057,938
  have eq1059 : (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (sP4 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1058 -- forward demodulation 1058,938
  have eq1060 : (sP0 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (sP4 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1059 -- forward demodulation 1059,938
  have eq1061 : (sP4 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP3 a sk1 sk3) := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1060 -- forward demodulation 1060,938
  have eq1062 : (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq943 -- forward demodulation 943,938
  have eq1063 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1062 -- forward demodulation 1062,938
  have eq1064 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1063 -- forward demodulation 1063,938
  have eq1065 : (sP3 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1064 -- forward demodulation 1064,938
  have eq1092 : (sP2 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq961 -- forward demodulation 961,938
  have eq1093 : (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1092 -- forward demodulation 1092,938
  have eq1094 : (sP0 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (sP3 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1093 -- forward demodulation 1093,938
  have eq1095 : (sP3 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1094 -- forward demodulation 1094,938
  have eq1117 : (sP0 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq968 -- forward demodulation 968,938
  have eq1118 : (sP2 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 := Eq.mp (by simp only [eq938, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1117 -- forward demodulation 1117,938
  have eq1263 : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq1118 rule_def_2_2 -- resolution 1118,139
  have eq1266 : (old a sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq1263 rule_def_0_2 -- subsumption resolution 1263,130
  have eq1268 (X0 : G) : ¬(old a sk1 X0) ∨ c = sk3 ∨ sk3 = X0 ∨ c = sk1 := resolve eq1266 old_0 -- resolution 1266,110
  have eq1295 : c = sk3 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1268 eq1012 -- resolution 1268,1012
  have eq1296 : c = sk3 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1268 eq997 -- resolution 1268,997
  have eq1301 : c = sk3 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1296 rfl -- duplicate literal removal 1296
  have eq1302 : c = sk3 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1295 rfl -- duplicate literal removal 1295
  have eq1303 : c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1302 preserve_2 -- subsumption resolution 1302,158
  have eq1304 : c = sk3 ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1301 preserve_2 -- subsumption resolution 1301,158
  have eq1307 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := Or.assoc6 (eq1303.imp_left (fun h : c = sk3 ↦ superpose h eq1061)) -- superposition 1061,1303, 1303 into 1061, unify on (0).2 in 1303 and (0).3 in 1061
  have eq1310 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1307 eq175 -- subsumption resolution 1307,175
  have eq1311 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1310 p4XY -- subsumption resolution 1310,107
  have eq1312 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1311 eq189 -- subsumption resolution 1311,189
  have eq1313 : (sP4 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1312 rule_def_0_1 -- subsumption resolution 1312,129
  have eq1314 : (sP4 a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1313 rule_def_2_1 -- subsumption resolution 1313,138
  have eq1315 : b = sk1 ∨ a = sk1 ∨ c = sk1 := resolve eq1314 rule_def_4_1 -- subsumption resolution 1314,150
  have eq1321 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq1315.imp_left (fun h : b = sk1 ↦ superpose h eq980)) -- superposition 980,1315, 1315 into 980, unify on (0).2 in 1315 and (0).2 in 980
  have eq1330 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq1315.imp_left (fun h : b = sk1 ↦ superpose h eq1266)) -- superposition 1266,1315, 1315 into 1266, unify on (0).2 in 1315 and (0).2 in 1266
  have eq1335 : c = b ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq1321 p3 -- subsumption resolution 1321,106
  have eq1336 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq1335 bc -- subsumption resolution 1335,105
  have eq1345 : c = b ∨ c = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq1330 p3 -- subsumption resolution 1330,106
  have eq1346 : c = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq1345 bc -- subsumption resolution 1345,105
  have eq1370 : c ≠ sk2 ∨ a = sk1 ∨ c = sk1 := eq1346.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 158,1346, 1346 into 158, unify on (0).2 in 1346 and (0).2 in 158
  have eq1375 : c = sk1 ∨ a = sk1 := resolve eq1370 eq1336 -- subsumption resolution 1370,1336
  have eq1411 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := Or.assoc6 (eq1304.imp_left (fun h : c = sk3 ↦ superpose h eq1061)) -- superposition 1061,1304, 1304 into 1061, unify on (0).2 in 1304 and (0).3 in 1061
  have eq1417 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1411 eq175 -- subsumption resolution 1411,175
  have eq1418 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1417 p4XY -- subsumption resolution 1417,107
  have eq1419 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1418 eq189 -- subsumption resolution 1418,189
  have eq1420 : (sP4 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1419 rule_def_0_1 -- subsumption resolution 1419,129
  have eq1421 : (sP4 a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1420 rule_def_2_0 -- subsumption resolution 1420,137
  have eq1422 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq1421 rule_def_4_1 -- subsumption resolution 1421,150
  have eq1439 : c = b ∨ a = b ∨ a = b ∨ c = sk1 := Or.assoc2 (eq1422.imp_left (fun h : b = sk1 ↦ superpose h eq1375)) -- superposition 1375,1422, 1422 into 1375, unify on (0).2 in 1422 and (0).2 in 1375
  have eq1441 : c = b ∨ a = b ∨ c = sk1 := resolve eq1439 rfl -- duplicate literal removal 1439
  have eq1462 : c = sk1 ∨ a = b := resolve eq1441 bc -- subsumption resolution 1441,105
  have eq1469 : (sP4 a c sk2) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ (sP2 a c sk2) ∨ (old a c sk2) ∨ (sP3 a c sk2) ∨ a = b := Or.assoc6 (eq1462.imp_left (fun h : c = sk1 ↦ superpose h eq1056)) -- superposition 1056,1462, 1462 into 1056, unify on (0).2 in 1462 and (0).2 in 1056
  have eq1470 : (sP4 a c sk3) ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) ∨ (sP2 a c sk3) ∨ (old a c sk3) ∨ (sP3 a c sk3) ∨ a = b := Or.assoc6 (eq1462.imp_left (fun h : c = sk1 ↦ superpose h eq1061)) -- superposition 1061,1462, 1462 into 1061, unify on (0).2 in 1462 and (0).2 in 1061
  have eq1472 : (sP4 a c sk2) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ (sP2 a c sk2) ∨ (sP3 a c sk2) ∨ a = b := resolve eq1469 p4XZ -- subsumption resolution 1469,108
  have eq1473 : (sP4 a c sk2) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ (sP3 a c sk2) ∨ a = b := resolve eq1472 rule_def_2_0 -- subsumption resolution 1472,137
  have eq1474 : (sP4 a c sk2) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ a = b := resolve eq1473 rule_def_3_0 -- subsumption resolution 1473,143
  have eq1475 : (sP4 a c sk3) ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) ∨ (sP2 a c sk3) ∨ (sP3 a c sk3) ∨ a = b := resolve eq1470 p4XZ -- subsumption resolution 1470,108
  have eq1476 : (sP4 a c sk3) ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) ∨ (sP3 a c sk3) ∨ a = b := resolve eq1475 rule_def_2_0 -- subsumption resolution 1475,137
  have eq1477 : (sP4 a c sk3) ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) ∨ a = b := resolve eq1476 rule_def_3_0 -- subsumption resolution 1476,143
  have eq1582 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b := resolve eq1065 rule_def_3_0 -- resolution 1065,143
  have eq1597 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b := resolve eq1582 rule_def_2_0 -- subsumption resolution 1582,137
  have eq1620 : (sP0 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ a = sk3 ∨ a = b := resolve eq1095 rule_def_3_0 -- resolution 1095,143
  have eq1638 : (sP1 a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ a = sk3 ∨ a = b := resolve eq1620 rule_def_2_0 -- subsumption resolution 1620,137
  have eq1966 (X0 X1 : G) : ¬(old a X1 b) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b ∨ sk2 = X0 ∨ (sP0 a sk1 sk2) ∨ ¬(old X0 a X1) := resolve eq1597 eq452 -- resolution 1597,452
  have eq1967 (X0 : G) : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b ∨ a = sk2 ∨ ¬(old a X0 a) ∨ ¬(old b a X0) := resolve eq1597 eq466 -- resolution 1597,466
  have eq1977 (X0 : G) : ¬(old b a X0) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b ∨ ¬(old a X0 a) ∨ (sP0 a sk1 sk2) := resolve eq1967 rfl -- duplicate literal removal 1967
  have eq1983 (X0 X1 : G) : ¬(old a X1 b) ∨ (old a sk1 sk3) ∨ a = sk3 ∨ a = b ∨ sk3 = X0 ∨ (sP0 a sk1 sk3) ∨ ¬(old X0 a X1) := resolve eq1638 eq452 -- resolution 1638,452
  have eq1984 (X0 : G) : (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ a = sk3 ∨ a = b ∨ a = sk3 ∨ ¬(old a X0 a) ∨ ¬(old b a X0) := resolve eq1638 eq466 -- resolution 1638,466
  have eq1998 (X0 : G) : ¬(old b a X0) ∨ (old a sk1 sk3) ∨ a = sk3 ∨ a = b ∨ ¬(old a X0 a) ∨ (sP0 a sk1 sk3) := resolve eq1984 rfl -- duplicate literal removal 1984
  have eq2756 (X0 X1 X2 : G) : (old a sk1 sk2) ∨ a = sk2 ∨ a = b ∨ ¬(old a (sF4 X0 X1 X2) a) ∨ (sP0 a sk1 sk2) ∨ ¬(sP4 X0 X1 X2) := resolve eq1977 rule_def_4_4 -- resolution 1977,153
  have eq2758 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = sk2 ∨ a = b ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := resolve eq2756 rule_def_4_3 -- subsumption resolution 2756,152
  have eq2765 : a = sk2 ∨ a = b ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a c sk3) ∨ (sP1 a c sk3) ∨ a = b := resolve eq2758 eq1477 -- resolution 2758,1477
  have eq2766 : (sP1 a c sk3) ∨ a = b ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a c sk3) ∨ a = sk2 := resolve eq2765 rfl -- duplicate literal removal 2765
  have eq2773 (X0 X1 X2 : G) : (old a sk1 sk3) ∨ a = sk3 ∨ a = b ∨ ¬(old a (sF4 X0 X1 X2) a) ∨ (sP0 a sk1 sk3) ∨ ¬(sP4 X0 X1 X2) := resolve eq1998 rule_def_4_4 -- resolution 1998,153
  have eq2775 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ a = sk3 ∨ a = b ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) := resolve eq2773 rule_def_4_3 -- subsumption resolution 2773,152
  have eq2781 : a = sk3 ∨ a = b ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ a = b := resolve eq2775 eq1474 -- resolution 2775,1474
  have eq2784 : (sP1 a c sk2) ∨ a = b ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a c sk2) ∨ a = sk3 := resolve eq2781 rfl -- duplicate literal removal 2781
  have eq2957 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ a = sk2 ∨ a = b ∨ sk2 = X0 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ ¬(sP1 X1 X2 X3) := resolve eq1966 rule_def_1_3 -- resolution 1966,135
  have eq2958 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ a = sk3 ∨ a = b ∨ sk3 = X0 ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ ¬(sP1 X1 X2 X3) := resolve eq1983 rule_def_1_3 -- resolution 1983,135
  have eq4213 (X0 X1 X2 : G) : a = sk2 ∨ a = b ∨ sk2 = X0 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq2957 rule_def_1_2 -- resolution 2957,134
  have eq4214 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ a = b ∨ sk2 = X0 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 := resolve eq4213 rfl -- duplicate literal removal 4213
  have eq4237 : a = b ∨ sk2 = sk3 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ a = b ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a c sk3) ∨ a = sk2 := resolve eq4214 eq2766 -- resolution 4214,2766
  have eq4272 : a = b ∨ sk2 = sk3 ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk2 ∨ (sP0 a c sk3) := resolve eq4237 rfl -- duplicate literal removal 4237
  have eq4293 : (sP0 a sk1 sk2) ∨ a = b ∨ (old a sk1 sk2) ∨ a = sk2 ∨ (sP0 a c sk3) := resolve eq4272 preserve_2 -- subsumption resolution 4272,158
  have eq4297 (X0 X1 X2 : G) : a = sk3 ∨ a = b ∨ sk3 = X0 ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq2958 rule_def_1_2 -- resolution 2958,134
  have eq4298 (X0 X1 X2 : G) : a = sk3 ∨ a = b ∨ sk3 = X0 ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ ¬(sP1 X1 X2 X0) := resolve eq4297 rfl -- duplicate literal removal 4297
  have eq4302 : (sP0 a c sk2) ∨ a = b ∨ (old a c sk2) ∨ a = sk2 ∨ (sP0 a c sk3) ∨ a = b := Or.assoc5 (eq1462.imp_left (fun h : c = sk1 ↦ superpose h eq4293)) -- superposition 4293,1462, 1462 into 4293, unify on (0).2 in 1462 and (0).2 in 4293
  have eq4310 : (sP0 a c sk2) ∨ a = b ∨ (old a c sk2) ∨ a = sk2 ∨ (sP0 a c sk3) := resolve eq4302 rfl -- duplicate literal removal 4302
  have eq4311 : (sP0 a c sk3) ∨ a = b ∨ a = sk2 ∨ (sP0 a c sk2) := resolve eq4310 p4XZ -- subsumption resolution 4310,108
  have eq4353 : a = b ∨ a = sk2 ∨ (sP0 a c sk2) ∨ c = b := resolve eq4311 rule_def_0_1 -- resolution 4311,129
  have eq4362 : (sP0 a c sk2) ∨ a = sk2 ∨ a = b := resolve eq4353 bc -- subsumption resolution 4353,105
  have eq4407 : a = sk2 ∨ a = b ∨ c = b := resolve eq4362 rule_def_0_1 -- resolution 4362,129
  have eq4412 : a = sk2 ∨ a = b := resolve eq4407 bc -- subsumption resolution 4407,105
  have eq4541 : (sP1 a c a) ∨ a = b ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a c a) ∨ a = sk3 ∨ a = b := Or.assoc6 (eq4412.imp_left (fun h : a = sk2 ↦ superpose h eq2784)) -- superposition 2784,4412, 4412 into 2784, unify on (0).2 in 4412 and (0).3 in 2784
  have eq4547 : (sP1 a c a) ∨ a = b ∨ (sP0 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a c a) ∨ a = sk3 := resolve eq4541 rfl -- duplicate literal removal 4541
  have eq4586 : (sP0 a sk1 sk3) ∨ a = b ∨ (old a sk1 sk3) ∨ (sP0 a c a) ∨ a = sk3 := resolve eq4547 eq4298 -- subsumption resolution 4547,4298
  have eq4897 : (sP0 a c sk3) ∨ a = b ∨ (old a c sk3) ∨ (sP0 a c a) ∨ a = sk3 ∨ a = b := Or.assoc5 (eq1462.imp_left (fun h : c = sk1 ↦ superpose h eq4586)) -- superposition 4586,1462, 1462 into 4586, unify on (0).2 in 1462 and (0).2 in 4586
  have eq4909 : (sP0 a c sk3) ∨ a = b ∨ (old a c sk3) ∨ (sP0 a c a) ∨ a = sk3 := resolve eq4897 rfl -- duplicate literal removal 4897
  have eq4910 : (sP0 a c sk3) ∨ a = b ∨ (sP0 a c a) ∨ a = sk3 := resolve eq4909 p4XZ -- subsumption resolution 4909,108
  have eq4954 : a = b ∨ (sP0 a c a) ∨ a = sk3 ∨ c = b := resolve eq4910 rule_def_0_1 -- resolution 4910,129
  have eq4963 : (sP0 a c a) ∨ a = b ∨ a = sk3 := resolve eq4954 bc -- subsumption resolution 4954,105
  have eq5007 : a = b ∨ a = sk3 ∨ a = c := resolve eq4963 rule_def_0_2 -- resolution 4963,130
  have eq5010 : a = sk3 ∨ a = b := resolve eq5007 ac -- subsumption resolution 5007,104
  have eq5017 : a ≠ sk2 ∨ a = b := eq5010.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 158,5010, 5010 into 158, unify on (0).2 in 5010 and (0).2 in 158
  have eq5115 : a = b := resolve eq5017 eq4412 -- subsumption resolution 5017,4412
  have eq5117 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 106,5115
  have eq5118 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 129,5115
  have eq5119 : ∀ (X0 X1 X2 : G) , (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_3 -- backward demodulation 135,5115
  have eq5124 : ∀ (X0 X1 X2 : G) , (old X2 a (sF3 X0 X1 X2)) ∨ ¬(sP3 X0 X1 X2) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_3_4 -- backward demodulation 147,5115
  have eq5125 : ∀ (X0 X1 X2 : G) , (old a a (sF4 X0 X1 X2)) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_4 -- backward demodulation 153,5115
  have eq5209 : ∀ (X0 X1 X2 : G) , ¬(sP3 X1 X2 X0) ∨ (new a c X0) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq397 -- backward demodulation 397,5115
  have eq5213 : ∀ (X0 X1 X2 X3 X4 : G) , ¬(sP1 X3 X4 X2) ∨ ¬(old a X1 a) ∨ X0 = X2 ∨ ¬(old X0 a X1) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq452 -- backward demodulation 452,5115
  have eq5216 : ∀ (X0 X1 X2 X3 X4 : G) , ¬(old X0 a X1) ∨ ¬(sP3 X3 X4 X2) ∨ X0 = X2 ∨ ¬(old b X1 a) := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq456 -- backward demodulation 456,5115
  have eq5654 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq5125 eq5117 -- subsumption resolution 5125,5117
  have eq5705 : ∀ (X0 X1 X2 X3 X4 : G) , ¬(sP3 X3 X4 X2) ∨ ¬(old X0 a X1) ∨ ¬(old a X1 a) ∨ X0 = X2 := Eq.mp (by simp only [eq5115, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5216 -- forward demodulation 5216,5115
  have eq5820 : (sP3 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) := resolve eq5654 eq1056 -- resolution 5654,1056
  have eq5821 : (sP3 a sk1 sk3) ∨ (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a sk1 sk3) := resolve eq5654 eq1061 -- resolution 5654,1061
  have eq6155 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) := resolve eq5820 eq5209 -- resolution 5820,5209
  have eq6168 : (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) := resolve eq6155 eq393 -- subsumption resolution 6155,393
  have eq6175 : (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) ∨ c = sk2 := resolve eq6168 rule_def_2_2 -- resolution 6168,139
  have eq6179 : (new a c sk2) ∨ (old a sk1 sk2) ∨ c = sk2 := resolve eq6175 rule_def_0_2 -- subsumption resolution 6175,130
  have eq6190 : (sP1 a sk1 sk3) ∨ (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (new a c sk3) := resolve eq5821 eq5209 -- resolution 5821,5209
  have eq6204 : (sP2 a sk1 sk3) ∨ (old a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (new a c sk3) := resolve eq6190 eq393 -- subsumption resolution 6190,393
  have eq6210 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (old a c sk2) ∨ (sP4 a c sk2) := resolve eq6179 new_imp -- resolution 6179,155
  have eq6211 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP4 a c sk2) := resolve eq6210 p4XZ -- subsumption resolution 6210,108
  have eq6212 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) := resolve eq6211 eq5654 -- subsumption resolution 6211,5654
  have eq6213 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) := resolve eq6212 rule_def_0_2 -- subsumption resolution 6212,130
  have eq6214 : (sP3 a c sk2) ∨ c = sk2 ∨ (old a sk1 sk2) ∨ (sP1 a c sk2) := resolve eq6213 rule_def_2_2 -- subsumption resolution 6213,139
  have eq6230 (X0 X1 : G) : c = sk2 ∨ (old a sk1 sk2) ∨ (sP1 a c sk2) ∨ ¬(old X0 a X1) ∨ ¬(old a X1 a) ∨ sk2 = X0 := resolve eq6214 eq5705 -- resolution 6214,5705
  have eq6242 (X0 X1 : G) : ¬(old a X1 a) ∨ (old a sk1 sk2) ∨ ¬(old X0 a X1) ∨ c = sk2 ∨ sk2 = X0 := resolve eq6230 eq5213 -- subsumption resolution 6230,5213
  have eq6248 : (old a sk1 sk3) ∨ (sP0 a sk1 sk3) ∨ (new a c sk3) ∨ c = sk3 := resolve eq6204 rule_def_2_2 -- resolution 6204,139
  have eq6253 : (new a c sk3) ∨ (old a sk1 sk3) ∨ c = sk3 := resolve eq6248 rule_def_0_2 -- subsumption resolution 6248,130
  have eq6254 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP3 a c sk3) ∨ (sP2 a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ (old a c sk3) ∨ (sP4 a c sk3) := resolve eq6253 new_imp -- resolution 6253,155
  have eq6255 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP3 a c sk3) ∨ (sP2 a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) ∨ (sP4 a c sk3) := resolve eq6254 p4XZ -- subsumption resolution 6254,108
  have eq6256 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP3 a c sk3) ∨ (sP2 a c sk3) ∨ (sP1 a c sk3) ∨ (sP0 a c sk3) := resolve eq6255 eq5654 -- subsumption resolution 6255,5654
  have eq6257 : (old a sk1 sk3) ∨ c = sk3 ∨ (sP3 a c sk3) ∨ (sP2 a c sk3) ∨ (sP1 a c sk3) := resolve eq6256 rule_def_0_2 -- subsumption resolution 6256,130
  have eq6258 : (sP3 a c sk3) ∨ c = sk3 ∨ (old a sk1 sk3) ∨ (sP1 a c sk3) := resolve eq6257 rule_def_2_2 -- subsumption resolution 6257,139
  have eq6298 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (old a sk1 sk2) ∨ c = sk2 ∨ sk2 = X0 ∨ ¬(sP1 X1 X2 X3) := resolve eq6242 eq5119 -- resolution 6242,5119
  have eq6299 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF3 X1 X2 X3)) ∨ (old a sk1 sk2) ∨ c = sk2 ∨ sk2 = X0 ∨ ¬(sP3 X1 X2 X3) := resolve eq6242 rule_def_3_2 -- resolution 6242,145
  have eq6506 (X0 X1 X2 : G) : (old a sk1 sk2) ∨ c = sk2 ∨ sk2 = X0 ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq6298 rule_def_1_2 -- resolution 6298,134
  have eq6507 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ (old a sk1 sk2) := resolve eq6506 rfl -- duplicate literal removal 6506
  have eq6513 (X0 X1 X2 : G) : (old a sk1 sk2) ∨ c = sk2 ∨ sk2 = X0 ∨ ¬(sP3 X1 X2 X0) ∨ ¬(sP3 X1 X2 X0) := resolve eq6299 eq5124 -- resolution 6299,5124
  have eq6514 (X0 X1 X2 : G) : ¬(sP3 X1 X2 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ (old a sk1 sk2) := resolve eq6513 rfl -- duplicate literal removal 6513
  have eq6531 : c = sk2 ∨ sk2 = sk3 ∨ (old a sk1 sk2) ∨ c = sk3 ∨ (old a sk1 sk3) ∨ (sP1 a c sk3) := resolve eq6514 eq6258 -- resolution 6514,6258
  have eq6545 : (sP1 a c sk3) ∨ (old a sk1 sk2) ∨ c = sk3 ∨ (old a sk1 sk3) ∨ c = sk2 := resolve eq6531 preserve_2 -- subsumption resolution 6531,158
  have eq6560 : (old a sk1 sk2) ∨ c = sk3 ∨ (old a sk1 sk3) ∨ c = sk2 ∨ c = sk2 ∨ sk2 = sk3 ∨ (old a sk1 sk2) := resolve eq6545 eq6507 -- resolution 6545,6507
  have eq6561 : (old a sk1 sk2) ∨ c = sk3 ∨ (old a sk1 sk3) ∨ c = sk2 ∨ sk2 = sk3 := resolve eq6560 rfl -- duplicate literal removal 6560
  have eq6562 : (old a sk1 sk3) ∨ c = sk3 ∨ (old a sk1 sk2) ∨ c = sk2 := resolve eq6561 preserve_2 -- subsumption resolution 6561,158
  have eq6585 : (old a c sk3) ∨ c = sk3 ∨ (old a c sk2) ∨ c = sk2 ∨ a = sk1 := Or.assoc4 (eq1375.imp_left (fun h : c = sk1 ↦ superpose h eq6562)) -- superposition 6562,1375, 1375 into 6562, unify on (0).2 in 1375 and (0).2 in 6562
  have eq6591 : c = sk3 ∨ (old a c sk2) ∨ c = sk2 ∨ a = sk1 := resolve eq6585 p4XZ -- subsumption resolution 6585,108
  have eq6592 : c = sk3 ∨ c = sk2 ∨ a = sk1 := resolve eq6591 p4XZ -- subsumption resolution 6591,108
  have eq6598 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk2 ∨ a = sk1 := Or.assoc6 (eq6592.imp_left (fun h : c = sk3 ↦ superpose h eq1061)) -- superposition 1061,6592, 6592 into 1061, unify on (0).2 in 6592 and (0).3 in 1061
  have eq6634 : (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk2 ∨ a = sk1 := resolve eq6598 eq5654 -- subsumption resolution 6598,5654
  have eq6635 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk2 ∨ a = sk1 := resolve eq6634 eq175 -- subsumption resolution 6634,175
  have eq6636 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk2 ∨ a = sk1 := resolve eq6635 p4XY -- subsumption resolution 6635,107
  have eq6637 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk2 ∨ a = sk1 := resolve eq6636 eq189 -- subsumption resolution 6636,189
  have eq6638 : (sP2 a sk1 c) ∨ c = sk2 ∨ a = sk1 := resolve eq6637 eq5118 -- subsumption resolution 6637,5118
  have eq6639 : c = sk2 ∨ a = sk1 := resolve eq6638 rule_def_2_1 -- subsumption resolution 6638,138
  have eq6644 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ a = sk1 := Or.assoc6 (eq6639.imp_left (fun h : c = sk2 ↦ superpose h eq1056)) -- superposition 1056,6639, 6639 into 1056, unify on (0).2 in 6639 and (0).3 in 1056
  have eq6680 : (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ a = sk1 := resolve eq6644 eq5654 -- subsumption resolution 6644,5654
  have eq6681 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ a = sk1 := resolve eq6680 eq175 -- subsumption resolution 6680,175
  have eq6682 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (sP3 a sk1 c) ∨ a = sk1 := resolve eq6681 p4XY -- subsumption resolution 6681,107
  have eq6683 : (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ a = sk1 := resolve eq6682 eq189 -- subsumption resolution 6682,189
  have eq6684 : (sP2 a sk1 c) ∨ a = sk1 := resolve eq6683 eq5118 -- subsumption resolution 6683,5118
  have eq6685 : a = sk1 := resolve eq6684 rule_def_2_1 -- subsumption resolution 6684,138
  have eq6688 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq6685, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq980 -- backward demodulation 980,6685
  have eq6713 : a = c ∨ (old a sk1 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq6685, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1266 -- backward demodulation 1266,6685
  have eq7010 : (old a sk1 sk2) ∨ c = sk2 := resolve eq6688 ac -- subsumption resolution 6688,104
  have eq7011 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq6685, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7010 -- forward demodulation 7010,6685
  have eq7012 : c = sk2 := resolve eq7011 eq5117 -- subsumption resolution 7011,5117
  have eq7013 : c ≠ sk3 := Eq.mp (by simp only [eq7012, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 158,7012
  have eq7062 : (old a sk1 sk3) ∨ c = sk3 := resolve eq6713 ac -- subsumption resolution 6713,104
  have eq7063 : (old a sk1 sk3) := resolve eq7062 eq7013 -- subsumption resolution 7062,7013
  have eq7064 : (old a a sk3) := Eq.mp (by simp only [eq6685, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7063 -- forward demodulation 7063,6685
  subsumption eq5117 eq7064 -- subsumption resolution 7064,5117

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X1 X3 X4 ∨ old X1 X4 X0)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_10 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X0 ∨ ¬ old X2 X0 X3 ∨ ¬ old X3 X0 X1 ∨ old X0 X0 X2)) (old_11 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X3 X0 X1 ∨ ¬ old X4 X0 X2 ∨ old X0 X3 X4)) (old_14 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X0 ∨ ¬ old X1 X0 X3 ∨ old X0 X2 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old a X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (imp_new_4 : ∀ X Y Z X3, b ≠ X ∨ c ≠ Y ∨ ¬ old a X3 a ∨ ¬ old b X3 a ∨ ¬ old Z b X3 ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a (sF4 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X1 X3 X4 ∨ new X1 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq167 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old a X3 b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 134
  have eq168 (X2 X3 : G) : ¬(old a X3 b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq167 rfl -- equality resolution 167
  have eq172 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 b X3) ∨ ¬(old b X3 a) ∨ ¬(old a X3 a) ∨ b ≠ X0 := resolve imp_new_4 rfl -- equality resolution 145
  have eq173 (X2 X3 : G) : ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ (new b c X2) ∨ ¬(old a X3 a) := resolve eq172 rfl -- equality resolution 172
  have eq180 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 137,112
  have eq184 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 148,121
  have eq194 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 150,112
  have eq202 (X0 : G) : ¬(new sk1 sk2 X0) ∨ sk3 = X0 := resolve prev_0 preserve_1 -- resolution 159,161
  have eq203 (X0 : G) : ¬(new sk1 sk3 X0) ∨ sk4 = X0 := resolve prev_0 preserve_2 -- resolution 159,162
  have eq208 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq168 rule_def_1_3 -- resolution 168,138
  have eq221 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 143,121
  have eq277 (X0 X1 X2 X3 : G) : (old a a X0) ∨ ¬(old X0 a b) ∨ ¬(old a (sF4 X1 X2 X3) a) ∨ ¬(sP4 X1 X2 X3) := resolve old_10 rule_def_4_4 -- resolution 123,156
  have eq279 (X0 X1 X2 X3 : G) : ¬(sP4 X1 X2 X3) ∨ ¬(old X0 a b) ∨ (old a a X0) := resolve eq277 rule_def_4_3 -- subsumption resolution 277,155
  have eq292 (X0 X1 X2 X3 : G) : ¬(old a (sF0 X1 X2 X3) a) ∨ (old a X0 a) ∨ ¬(old a X3 X0) ∨ ¬(sP1 X1 X2 X3) := resolve old_14 rule_def_1_2 -- resolution 127,137
  have eq293 (X0 X1 X2 X3 : G) : ¬(old b (sF3 X1 X2 X3) b) ∨ (old b X0 b) ∨ ¬(old b X3 X0) ∨ ¬(sP3 X1 X2 X3) := resolve old_14 rule_def_3_4 -- resolution 127,150
  have eq302 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(old a (sF3 X1 X2 X3) a) ∨ ¬(sP3 X1 X2 X3) := resolve eq173 rule_def_3_3 -- resolution 173,149
  have eq303 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP3 X1 X2 X3) := resolve eq302 rule_def_3_2 -- subsumption resolution 302,148
  have eq365 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 158,160
  have eq366 : (sP4 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) := resolve new_imp preserve_1 -- resolution 158,161
  have eq367 : (sP4 sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP3 sk1 sk3 sk4) := resolve new_imp preserve_2 -- resolution 158,162
  have eq378 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq184 rule_def_3_3 -- resolution 184,149
  have eq379 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq378 rfl -- duplicate literal removal 378
  have eq416 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq208 rule_def_1_2 -- resolution 208,137
  have eq417 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq416 rfl -- duplicate literal removal 416
  have eq426 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP3 X1 X2 X0) ∨ ¬(sP3 X1 X2 X0) := resolve eq303 rule_def_3_4 -- resolution 303,150
  have eq427 (X0 X1 X2 : G) : ¬(sP3 X1 X2 X0) ∨ (new b c X0) := resolve eq426 rfl -- duplicate literal removal 426
  have eq428 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq221 rule_def_2_4 -- resolution 221,144
  have eq431 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq428 rfl -- duplicate literal removal 428
  have eq509 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq365 rule_def_4_0 -- resolution 365,152
  have eq510 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq365 rule_def_4_1 -- resolution 365,153
  have eq511 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk2 := resolve eq365 rule_def_4_2 -- resolution 365,154
  have eq519 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq509 rule_def_0_0 -- subsumption resolution 509,131
  have eq520 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq519 rule_def_1_0 -- subsumption resolution 519,135
  have eq521 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq510 rule_def_1_1 -- subsumption resolution 510,136
  have eq522 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq521 rule_def_3_1 -- subsumption resolution 521,147
  have eq526 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 := resolve eq520 rule_def_3_1 -- resolution 520,147
  have eq539 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ a = sk1 := resolve eq366 rule_def_4_0 -- resolution 366,152
  have eq540 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ c = sk2 := resolve eq366 rule_def_4_1 -- resolution 366,153
  have eq549 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ a = sk1 := resolve eq539 rule_def_0_0 -- subsumption resolution 539,131
  have eq550 : (sP3 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 := resolve eq549 rule_def_1_0 -- subsumption resolution 549,135
  have eq551 : (sP2 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ c = sk2 := resolve eq540 rule_def_1_1 -- subsumption resolution 540,136
  have eq552 : (sP2 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq551 rule_def_3_1 -- subsumption resolution 551,147
  have eq570 : (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP3 sk1 sk3 sk4) ∨ a = sk1 := resolve eq367 rule_def_4_0 -- resolution 367,152
  have eq571 : (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP3 sk1 sk3 sk4) ∨ c = sk3 := resolve eq367 rule_def_4_1 -- resolution 367,153
  have eq572 : (sP3 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk4 := resolve eq367 rule_def_4_2 -- resolution 367,154
  have eq580 : (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP3 sk1 sk3 sk4) ∨ a = sk1 := resolve eq570 rule_def_0_0 -- subsumption resolution 570,131
  have eq581 : (sP3 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk1 := resolve eq580 rule_def_1_0 -- subsumption resolution 580,135
  have eq582 : (sP2 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP3 sk1 sk3 sk4) ∨ c = sk3 := resolve eq571 rule_def_1_1 -- subsumption resolution 571,136
  have eq583 : (sP2 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 := resolve eq582 rule_def_3_1 -- subsumption resolution 582,147
  have eq635 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq526 rule_def_2_2 -- resolution 526,142
  have eq652 (X0 X1 : G) : a = sk0 ∨ c = sk1 ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) ∨ ¬(old sk1 X1 sk2) := resolve eq635 old_11 -- resolution 635,124
  have eq695 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq522 rule_def_2_2 -- resolution 522,142
  have eq696 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq522 rule_def_2_1 -- resolution 522,141
  have eq698 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq695 rule_def_0_2 -- subsumption resolution 695,133
  have eq714 (X0 X1 : G) : ¬(old sk1 X1 sk2) ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) ∨ c = sk1 := resolve eq698 old_11 -- resolution 698,124
  have eq823 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq696 rule_def_0_1 -- resolution 696,132
  have eq876 : (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq550 rule_def_3_0 -- resolution 550,146
  have eq882 : (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 ∨ a = b := resolve eq550 eq379 -- resolution 550,379
  have eq886 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq876 rule_def_2_0 -- subsumption resolution 876,140
  have eq888 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ a = b := resolve eq882 eq431 -- subsumption resolution 882,431
  have eq1016 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = b := resolve eq552 eq431 -- resolution 552,431
  have eq1018 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq552 rule_def_2_2 -- resolution 552,142
  have eq1019 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk2 := resolve eq552 rule_def_2_1 -- resolution 552,141
  have eq1021 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq1018 rule_def_0_2 -- subsumption resolution 1018,133
  have eq1061 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = b ∨ b = sk2 := resolve eq1016 rule_def_0_1 -- resolution 1016,132
  have eq1095 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq1019 rule_def_0_1 -- resolution 1019,132
  have eq1148 : (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk1 ∨ b = sk1 := resolve eq581 rule_def_3_0 -- resolution 581,146
  have eq1154 : (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk1 ∨ a = b := resolve eq581 eq379 -- resolution 581,379
  have eq1158 : (old sk1 sk3 sk4) ∨ a = sk1 ∨ b = sk1 := resolve eq1148 rule_def_2_0 -- subsumption resolution 1148,140
  have eq1160 : (old sk1 sk3 sk4) ∨ a = sk1 ∨ a = b := resolve eq1154 eq431 -- subsumption resolution 1154,431
  have eq1163 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ b = sk1 ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ ¬(old X0 sk1 X1) := resolve eq1158 old_1 -- resolution 1158,114
  have eq1178 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ a = b ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ ¬(old X0 sk1 X1) := resolve eq1160 old_1 -- resolution 1160,114
  have eq1290 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 ∨ a = b := resolve eq583 eq431 -- resolution 583,431
  have eq1292 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq583 rule_def_2_2 -- resolution 583,142
  have eq1293 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 ∨ a = sk3 := resolve eq583 rule_def_2_1 -- resolution 583,141
  have eq1295 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq1292 rule_def_0_2 -- subsumption resolution 1292,133
  have eq1301 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ c = sk4 ∨ (old sk1 sk4 X0) ∨ c = sk3 ∨ ¬(old X0 sk1 X1) := resolve eq1295 old_1 -- resolution 1295,114
  have eq1334 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ a = b ∨ b = sk3 := resolve eq1290 rule_def_0_1 -- resolution 1290,132
  have eq1366 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ a = sk3 ∨ b = sk3 := resolve eq1293 rule_def_0_1 -- resolution 1293,132
  have eq2629 (X0 : G) : b = sk1 ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ ¬(old X0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq1163 eq886 -- resolution 1163,886
  have eq2641 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ b = sk1 := resolve eq2629 rfl -- duplicate literal removal 2629
  have eq2650 : (old sk1 sk4 sk0) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq2641 eq823 -- resolution 2641,823
  have eq2653 : (old sk1 sk4 sk0) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq2650 rfl -- duplicate literal removal 2650
  have eq2675 : a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ (new sk1 sk4 sk0) := resolve eq2653 imp_new_0 -- resolution 2653,129
  have eq2678 : b = sk1 ∨ a = sk1 ∨ c = sk1 := resolve eq2675 preserve_3 -- subsumption resolution 2675,163
  have eq2803 : a ≠ b ∨ a = sk1 ∨ c = sk1 := resolve eq2678 trans_resol -- equality factoring 2678
  have eq3227 (X0 : G) : a = b ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ ¬(old X0 sk1 sk2) ∨ a = sk1 ∨ a = b := resolve eq1178 eq888 -- resolution 1178,888
  have eq3241 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ a = sk1 ∨ a = b := resolve eq3227 rfl -- duplicate literal removal 3227
  have eq3306 : (old sk1 sk4 sk0) ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq3241 eq698 -- resolution 3241,698
  have eq3319 : (old sk1 sk4 sk0) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq3306 eq2803 -- subsumption resolution 3306,2803
  have eq3326 (X0 : G) : c = sk4 ∨ (old sk1 sk4 X0) ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq1301 eq1021 -- resolution 1301,1021
  have eq3332 (X0 : G) : c = sk4 ∨ (old sk1 sk4 X0) ∨ c = sk3 ∨ ¬(old X0 sk1 sk2) ∨ c = sk2 := resolve eq3326 rfl -- duplicate literal removal 3326
  have eq3962 : a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ (new sk1 sk4 sk0) := resolve eq3319 imp_new_0 -- resolution 3319,129
  have eq3972 : c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq3962 preserve_3 -- subsumption resolution 3962,163
  have eq4041 : (old sk1 c sk3) ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ a = sk1 := Or.assoc3 (eq3972.imp_left (fun h : c = sk2 ↦ superpose h eq888)) -- superposition 888,3972, 3972 into 888, unify on (0).2 in 3972 and (0).2 in 888
  have eq4143 : (old sk1 c sk3) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq4041 rfl -- duplicate literal removal 4041
  have eq4174 : a = sk1 ∨ a = b ∨ c = sk1 := resolve eq4143 p4XZ -- subsumption resolution 4143,111
  have eq4175 : c = sk1 ∨ a = sk1 := resolve eq4174 eq2803 -- subsumption resolution 4174,2803
  have eq4245 : (old c sk2 sk3) ∨ a = c ∨ c = b ∨ a = sk1 := Or.assoc3 (eq4175.imp_left (fun h : c = sk1 ↦ superpose h eq886)) -- superposition 886,4175, 4175 into 886, unify on (0).2 in 4175 and (0).1 in 886
  have eq4364 : a = c ∨ c = b ∨ a = sk1 := resolve eq4245 p4YZ -- subsumption resolution 4245,112
  have eq4365 : c = b ∨ a = sk1 := resolve eq4364 ac -- subsumption resolution 4364,107
  have eq4366 : a = sk1 := resolve eq4365 bc -- subsumption resolution 4365,108
  have eq4368 : (new a sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 161,4366
  have eq4369 : (new a sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 162,4366
  have eq4370 : ¬(new a sk4 sk0) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 163,4366
  have eq4372 : ∀ (X0 : G) , ¬(new a sk2 X0) ∨ sk3 = X0 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq202 -- backward demodulation 202,4366
  have eq4373 : ∀ (X0 : G) , ¬(new a sk3 X0) ∨ sk4 = X0 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq203 -- backward demodulation 203,4366
  have eq4375 : (sP3 a sk2 sk3) ∨ (sP4 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq366 -- backward demodulation 366,4366
  have eq4376 : (sP3 a sk3 sk4) ∨ (sP4 sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq367 -- backward demodulation 367,4366
  have eq4377 : (sP3 sk0 a sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq511 -- backward demodulation 511,4366
  have eq4384 : (sP3 sk0 a sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq520 -- backward demodulation 520,4366
  have eq4385 : (sP2 sk0 a sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq522 -- backward demodulation 522,4366
  have eq4421 : (sP3 a sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq572 -- backward demodulation 572,4366
  have eq4462 : ∀ (X0 X1 : G) , a = c ∨ a = sk0 ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) ∨ ¬(old sk1 X1 sk2) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq652 -- backward demodulation 652,4366
  have eq4486 : (old sk0 a sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq698 -- backward demodulation 698,4366
  have eq4496 : ∀ (X0 X1 : G) , a = c ∨ ¬(old sk1 X1 sk2) ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq714 -- backward demodulation 714,4366
  have eq4571 : (old a sk2 sk3) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1021 -- backward demodulation 1021,4366
  have eq4586 : (old a sk2 sk3) ∨ c = sk2 ∨ a = b ∨ b = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1061 -- backward demodulation 1061,4366
  have eq4601 : (old a sk2 sk3) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1095 -- backward demodulation 1095,4366
  have eq4653 : (old a sk3 sk4) ∨ c = sk3 ∨ c = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1295 -- backward demodulation 1295,4366
  have eq4670 : (old a sk3 sk4) ∨ c = sk3 ∨ a = b ∨ b = sk3 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1334 -- backward demodulation 1334,4366
  have eq4689 : (old a sk3 sk4) ∨ c = sk3 ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1366 -- backward demodulation 1366,4366
  have eq5146 : ∀ (X0 : G) , ¬(old X0 a sk2) ∨ c = sk4 ∨ (old sk1 sk4 X0) ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3332 -- backward demodulation 3332,4366
  have eq5222 : (sP4 a sk2 sk3) ∨ (sP3 a sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4375 -- forward demodulation 4375,4366
  have eq5223 : (sP2 a sk2 sk3) ∨ (sP4 a sk2 sk3) ∨ (sP3 a sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5222 -- forward demodulation 5222,4366
  have eq5224 : (sP1 a sk2 sk3) ∨ (sP2 a sk2 sk3) ∨ (sP4 a sk2 sk3) ∨ (sP3 a sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5223 -- forward demodulation 5223,4366
  have eq5225 : (sP0 a sk2 sk3) ∨ (sP1 a sk2 sk3) ∨ (sP2 a sk2 sk3) ∨ (sP4 a sk2 sk3) ∨ (sP3 a sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5224 -- forward demodulation 5224,4366
  have eq5226 : (sP4 a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (sP1 a sk2 sk3) ∨ (sP2 a sk2 sk3) ∨ (old a sk2 sk3) ∨ (sP3 a sk2 sk3) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5225 -- forward demodulation 5225,4366
  have eq5227 : (sP4 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4376 -- forward demodulation 4376,4366
  have eq5228 : (sP2 a sk3 sk4) ∨ (sP4 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (sP1 sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5227 -- forward demodulation 5227,4366
  have eq5229 : (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (sP4 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5228 -- forward demodulation 5228,4366
  have eq5230 : (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (sP4 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (old sk1 sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5229 -- forward demodulation 5229,4366
  have eq5231 : (sP4 a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5230 -- forward demodulation 5230,4366
  have eq5232 : (sP1 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4377 -- forward demodulation 4377,4366
  have eq5233 : (sP0 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5232 -- forward demodulation 5232,4366
  have eq5234 : (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5233 -- forward demodulation 5233,4366
  have eq5235 : (sP3 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ a = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5234 -- forward demodulation 5234,4366
  have eq5262 : (old sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4384 -- forward demodulation 4384,4366
  have eq5263 : (sP3 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ a = sk0 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5262 -- forward demodulation 5262,4366
  have eq5264 : (sP0 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4385 -- forward demodulation 4385,4366
  have eq5265 : (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ c = sk1 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5264 -- forward demodulation 5264,4366
  have eq5266 : a = c ∨ (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (sP2 sk0 a sk2) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5265 -- forward demodulation 5265,4366
  have eq5267 : (sP2 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) := resolve eq5266 ac -- subsumption resolution 5266,107
  have eq5336 : (sP1 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4421 -- forward demodulation 4421,4366
  have eq5337 : (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5336 -- forward demodulation 5336,4366
  have eq5338 : (old a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP3 a sk3 sk4) ∨ (sP2 sk1 sk3 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5337 -- forward demodulation 5337,4366
  have eq5339 : (sP3 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5338 -- forward demodulation 5338,4366
  have eq5428 (X0 X1 : G) : a = sk0 ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) ∨ ¬(old sk1 X1 sk2) := resolve eq4462 ac -- subsumption resolution 4462,107
  have eq5429 : ∀ (X0 X1 : G) , (old a X0 sk0) ∨ a = sk0 ∨ c = sk2 ∨ ¬(old X0 sk1 X1) ∨ ¬(old sk1 X1 sk2) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5428 -- forward demodulation 5428,4366
  have eq5430 : ∀ (X0 X1 : G) , ¬(old X0 a X1) ∨ (old a X0 sk0) ∨ a = sk0 ∨ c = sk2 ∨ ¬(old sk1 X1 sk2) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5429 -- forward demodulation 5429,4366
  have eq5431 : ∀ (X0 X1 : G) , ¬(old a X1 sk2) ∨ ¬(old X0 a X1) ∨ (old a X0 sk0) ∨ a = sk0 ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5430 -- forward demodulation 5430,4366
  have eq5464 : a = c ∨ (old sk0 a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4486 -- forward demodulation 4486,4366
  have eq5465 : (old sk0 a sk2) ∨ c = sk2 := resolve eq5464 ac -- subsumption resolution 5464,107
  have eq5491 (X0 X1 : G) : ¬(old sk1 X1 sk2) ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) := resolve eq4496 ac -- subsumption resolution 4496,107
  have eq5492 : ∀ (X0 X1 : G) , ¬(old a X1 sk2) ∨ c = sk2 ∨ (old sk1 X0 sk0) ∨ ¬(old X0 sk1 X1) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5491 -- forward demodulation 5491,4366
  have eq5493 : ∀ (X0 X1 : G) , (old a X0 sk0) ∨ ¬(old a X1 sk2) ∨ c = sk2 ∨ ¬(old X0 sk1 X1) := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5492 -- forward demodulation 5492,4366
  have eq5494 : ∀ (X0 X1 : G) , ¬(old a X1 sk2) ∨ (old a X0 sk0) ∨ ¬(old X0 a X1) ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5493 -- forward demodulation 5493,4366
  have eq6329 : ∀ (X0 : G) , ¬(old X0 a sk2) ∨ (old a sk4 X0) ∨ c = sk4 ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq4366, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5146 -- forward demodulation 5146,4366
  have eq7278 : (old a sk4 sk0) ∨ c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ c = sk2 := resolve eq6329 eq5465 -- resolution 6329,5465
  have eq7282 : (old a sk4 sk0) ∨ c = sk4 ∨ c = sk3 ∨ c = sk2 := resolve eq7278 rfl -- duplicate literal removal 7278
  have eq7329 : c = sk4 ∨ c = sk3 ∨ c = sk2 ∨ (new a sk4 sk0) := resolve eq7282 imp_new_0 -- resolution 7282,129
  have eq7331 : c = sk4 ∨ c = sk3 ∨ c = sk2 := resolve eq7329 eq4370 -- subsumption resolution 7329,4370
  have eq7346 : (new a sk3 c) ∨ c = sk3 ∨ c = sk2 := eq7331.imp_left (fun h : c = sk4 ↦ superpose h eq4369) -- superposition 4369,7331, 7331 into 4369, unify on (0).2 in 7331 and (0).3 in 4369
  have eq7347 : ¬(new a c sk0) ∨ c = sk3 ∨ c = sk2 := eq7331.imp_left (fun h : c = sk4 ↦ superpose h eq4370) -- superposition 4370,7331, 7331 into 4370, unify on (0).2 in 7331 and (0).2 in 4370
  have eq7348 : (old a sk3 c) ∨ c = sk3 ∨ a = b ∨ b = sk3 ∨ c = sk3 ∨ c = sk2 := Or.assoc4 (eq7331.imp_left (fun h : c = sk4 ↦ superpose h eq4670)) -- superposition 4670,7331, 7331 into 4670, unify on (0).2 in 7331 and (0).3 in 4670
  have eq7350 : (old a sk3 c) ∨ c = sk3 ∨ a = sk3 ∨ b = sk3 ∨ c = sk3 ∨ c = sk2 := Or.assoc4 (eq7331.imp_left (fun h : c = sk4 ↦ superpose h eq4689)) -- superposition 4689,7331, 7331 into 4689, unify on (0).2 in 7331 and (0).3 in 4689
  have eq7376 : (old a sk3 c) ∨ c = sk3 ∨ a = sk3 ∨ b = sk3 ∨ c = sk2 := resolve eq7350 rfl -- duplicate literal removal 7350
  have eq7378 : (old a sk3 c) ∨ c = sk3 ∨ a = b ∨ b = sk3 ∨ c = sk2 := resolve eq7348 rfl -- duplicate literal removal 7348
  have eq7381 : b = sk3 ∨ a = b ∨ c = sk3 ∨ c = sk2 := resolve eq7378 p4XY -- subsumption resolution 7378,110
  have eq7382 : b = sk3 ∨ a = sk3 ∨ c = sk3 ∨ c = sk2 := resolve eq7376 p4XY -- subsumption resolution 7376,110
  have eq7445 : (old a sk2 b) ∨ c = sk2 ∨ c = b ∨ a = b ∨ c = sk3 ∨ c = sk2 := Or.assoc3 (eq7381.imp_left (fun h : b = sk3 ↦ superpose h eq4571)) -- superposition 4571,7381, 7381 into 4571, unify on (0).2 in 7381 and (0).3 in 4571
  have eq7535 : (old a sk2 b) ∨ c = sk2 ∨ c = b ∨ a = b ∨ c = sk3 := resolve eq7445 rfl -- duplicate literal removal 7445
  have eq7544 : (old a sk2 b) ∨ c = sk2 ∨ a = b ∨ c = sk3 := resolve eq7535 bc -- subsumption resolution 7535,108
  have eq7588 : (old a sk2 b) ∨ c = sk2 ∨ c = b ∨ a = sk3 ∨ c = sk3 ∨ c = sk2 := Or.assoc3 (eq7382.imp_left (fun h : b = sk3 ↦ superpose h eq4571)) -- superposition 4571,7382, 7382 into 4571, unify on (0).2 in 7382 and (0).3 in 4571
  have eq7668 : (old a sk2 b) ∨ c = sk2 ∨ c = b ∨ a = sk3 ∨ c = sk3 := resolve eq7588 rfl -- duplicate literal removal 7588
  have eq7673 : (old a sk2 b) ∨ c = sk2 ∨ a = sk3 ∨ c = sk3 := resolve eq7668 bc -- subsumption resolution 7668,108
  have eq7784 (X0 : G) : ¬(old X0 a sk2) ∨ a = b ∨ c = sk3 ∨ (new a c X0) ∨ c = sk2 := resolve eq7544 eq168 -- resolution 7544,168
  have eq7849 (X0 : G) : ¬(old X0 a sk2) ∨ a = sk3 ∨ c = sk3 ∨ (new a c X0) ∨ c = sk2 := resolve eq7673 eq168 -- resolution 7673,168
  have eq8617 : a = b ∨ c = sk3 ∨ (new a c sk0) ∨ c = sk2 ∨ c = sk2 := resolve eq7784 eq5465 -- resolution 7784,5465
  have eq8623 : a = b ∨ c = sk3 ∨ (new a c sk0) ∨ c = sk2 := resolve eq8617 rfl -- duplicate literal removal 8617
  have eq8626 : c = sk3 ∨ a = b ∨ c = sk2 := resolve eq8623 eq7347 -- subsumption resolution 8623,7347
  have eq8645 : (old a sk2 c) ∨ c = sk2 ∨ a = b ∨ b = sk2 ∨ a = b ∨ c = sk2 := Or.assoc4 (eq8626.imp_left (fun h : c = sk3 ↦ superpose h eq4586)) -- superposition 4586,8626, 8626 into 4586, unify on (0).2 in 8626 and (0).3 in 4586
  have eq8650 : (sP4 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ (sP2 a c sk4) ∨ (old a c sk4) ∨ (sP3 a c sk4) ∨ a = b ∨ c = sk2 := Or.assoc6 (eq8626.imp_left (fun h : c = sk3 ↦ superpose h eq5231)) -- superposition 5231,8626, 8626 into 5231, unify on (0).2 in 8626 and (0).2 in 5231
  have eq8654 : (sP3 a c sk4) ∨ (old a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ (sP2 a c sk4) ∨ a = sk4 ∨ a = b ∨ c = sk2 := Or.assoc6 (eq8626.imp_left (fun h : c = sk3 ↦ superpose h eq5339)) -- superposition 5339,8626, 8626 into 5339, unify on (0).2 in 8626 and (0).2 in 5339
  have eq8720 : (old a sk2 c) ∨ c = sk2 ∨ a = b ∨ b = sk2 := resolve eq8645 rfl -- duplicate literal removal 8645
  have eq8731 : b = sk2 ∨ a = b ∨ c = sk2 := resolve eq8720 p4XY -- subsumption resolution 8720,110
  have eq8737 : (sP4 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ (sP2 a c sk4) ∨ (sP3 a c sk4) ∨ a = b ∨ c = sk2 := resolve eq8650 p4XZ -- subsumption resolution 8650,111
  have eq8738 : (sP4 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ (sP3 a c sk4) ∨ a = b ∨ c = sk2 := resolve eq8737 rule_def_2_0 -- subsumption resolution 8737,140
  have eq8739 : (sP4 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ a = b ∨ c = sk2 := resolve eq8738 rule_def_3_0 -- subsumption resolution 8738,146
  have eq8740 : (sP3 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ (sP2 a c sk4) ∨ a = sk4 ∨ a = b ∨ c = sk2 := resolve eq8654 p4XZ -- subsumption resolution 8654,111
  have eq8741 : (sP3 a c sk4) ∨ (sP0 a c sk4) ∨ (sP1 a c sk4) ∨ a = sk4 ∨ a = b ∨ c = sk2 := resolve eq8740 rule_def_2_0 -- subsumption resolution 8740,140
  have eq8742 : (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ a = sk4 ∨ a = b ∨ c = sk2 := resolve eq8741 rule_def_3_0 -- subsumption resolution 8741,146
  have eq8793 : (sP2 sk0 a b) ∨ (sP0 sk0 a b) ∨ (old sk0 a b) ∨ a = b ∨ c = sk2 := Or.assoc3 (eq8731.imp_left (fun h : b = sk2 ↦ superpose h eq5267)) -- superposition 5267,8731, 8731 into 5267, unify on (0).2 in 8731 and (0).3 in 5267
  have eq8810 (X0 X1 : G) : ¬(old a X0 b) ∨ (old a X1 sk0) ∨ ¬(old X1 a X0) ∨ c = b ∨ a = b ∨ c = sk2 := Or.assoc4 (eq8731.imp_left (fun h : b = sk2 ↦ superpose h eq5494)) -- superposition 5494,8731, 8731 into 5494, unify on (0).2 in 8731 and (0).3 in 5494
  have eq8907 : (sP2 sk0 a b) ∨ (old sk0 a b) ∨ a = b ∨ c = sk2 := resolve eq8793 rule_def_0_1 -- subsumption resolution 8793,132
  have eq8908 : (old sk0 a b) ∨ a = b ∨ c = sk2 := resolve eq8907 eq431 -- subsumption resolution 8907,431
  have eq8919 (X0 X1 : G) : ¬(old a X0 b) ∨ (old a X1 sk0) ∨ ¬(old X1 a X0) ∨ a = b ∨ c = sk2 := resolve eq8810 bc -- subsumption resolution 8810,108
  have eq9782 : a = sk3 ∨ c = sk3 ∨ (new a c sk0) ∨ c = sk2 ∨ c = sk2 := resolve eq7849 eq5465 -- resolution 7849,5465
  have eq9788 : a = sk3 ∨ c = sk3 ∨ (new a c sk0) ∨ c = sk2 := resolve eq9782 rfl -- duplicate literal removal 9782
  have eq9791 : c = sk3 ∨ a = sk3 ∨ c = sk2 := resolve eq9788 eq7347 -- subsumption resolution 9788,7347
  have eq9824 : (old a sk2 c) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk3 ∨ c = sk2 := Or.assoc4 (eq9791.imp_left (fun h : c = sk3 ↦ superpose h eq4601)) -- superposition 4601,9791, 9791 into 4601, unify on (0).2 in 9791 and (0).3 in 4601
  have eq9899 : (old a sk2 c) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk3 := resolve eq9824 rfl -- duplicate literal removal 9824
  have eq9907 : a = sk3 ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := resolve eq9899 p4XY -- subsumption resolution 9899,110
  have eq10139 (X0 : G) : ¬(new a a X0) ∨ sk4 = X0 ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := Or.assoc2 (eq9907.imp_left (fun h : a = sk3 ↦ superpose h eq4373)) -- superposition 4373,9907, 9907 into 4373, unify on (0).2 in 9907 and (0).2 in 4373
  have eq10140 : (old a sk2 a) ∨ c = sk2 ∨ a = c ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := Or.assoc3 (eq9907.imp_left (fun h : a = sk3 ↦ superpose h eq4571)) -- superposition 4571,9907, 9907 into 4571, unify on (0).2 in 9907 and (0).3 in 4571
  have eq10220 : (new a a c) ∨ a = c ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := Or.assoc3 (eq9907.imp_left (fun h : a = sk3 ↦ superpose h eq7346)) -- superposition 7346,9907, 9907 into 7346, unify on (0).2 in 9907 and (0).2 in 7346
  have eq10253 : (new a a c) ∨ a = c ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq10220 rfl -- duplicate literal removal 10220
  have eq10284 : (old a sk2 a) ∨ c = sk2 ∨ a = c ∨ a = sk2 ∨ b = sk2 := resolve eq10140 rfl -- duplicate literal removal 10140
  have eq10299 : (old a sk2 a) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq10284 ac -- subsumption resolution 10284,107
  have eq10328 : (new a a c) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq10253 ac -- subsumption resolution 10253,107
  have eq10708 : c = sk4 ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq10139 eq10328 -- resolution 10139,10328
  have eq10710 : c = sk4 ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := resolve eq10708 rfl -- duplicate literal removal 10708
  have eq10719 : ¬(new a c sk0) ∨ a = sk2 ∨ b = sk2 ∨ c = sk2 := eq10710.imp_left (fun h : c = sk4 ↦ superpose h eq4370) -- superposition 4370,10710, 10710 into 4370, unify on (0).2 in 10710 and (0).2 in 4370
  have eq12379 (X0 : G) : ¬(old X0 a b) ∨ (sP1 a c sk4) ∨ a = b ∨ c = sk2 ∨ (sP0 a c sk4) ∨ (old a a X0) := resolve eq8739 eq279 -- resolution 8739,279
  have eq12570 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (old a X0 sk0) ∨ a = b ∨ c = sk2 ∨ ¬(sP1 X1 X2 X3) := resolve eq8919 rule_def_1_3 -- resolution 8919,138
  have eq17935 (X0 X1 X2 : G) : (old a X0 sk0) ∨ a = b ∨ c = sk2 ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq12570 rule_def_1_2 -- resolution 12570,137
  have eq17936 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ a = b ∨ c = sk2 ∨ (old a X0 sk0) := resolve eq17935 rfl -- duplicate literal removal 17935
  have eq17943 : a = b ∨ c = sk2 ∨ (old a sk4 sk0) ∨ (sP0 a c sk4) ∨ a = sk4 ∨ a = b ∨ c = sk2 := resolve eq17936 eq8742 -- resolution 17936,8742
  have eq18011 : (sP0 a c sk4) ∨ c = sk2 ∨ (old a sk4 sk0) ∨ a = b ∨ a = sk4 := resolve eq17943 rfl -- duplicate literal removal 17943
  have eq18025 : c = sk2 ∨ (old a sk4 sk0) ∨ a = b ∨ a = sk4 ∨ c = b := resolve eq18011 rule_def_0_1 -- resolution 18011,132
  have eq18031 : (old a sk4 sk0) ∨ c = sk2 ∨ a = b ∨ a = sk4 := resolve eq18025 bc -- subsumption resolution 18025,108
  have eq18058 : c = sk2 ∨ a = b ∨ a = sk4 ∨ (new a sk4 sk0) := resolve eq18031 imp_new_0 -- resolution 18031,129
  have eq18074 : a = sk4 ∨ a = b ∨ c = sk2 := resolve eq18058 eq4370 -- subsumption resolution 18058,4370
  have eq18092 : ¬(new a a sk0) ∨ a = b ∨ c = sk2 := eq18074.imp_left (fun h : a = sk4 ↦ superpose h eq4370) -- superposition 4370,18074, 18074 into 4370, unify on (0).2 in 18074 and (0).2 in 4370
  have eq21176 : (sP1 a c sk4) ∨ a = b ∨ c = sk2 ∨ (sP0 a c sk4) ∨ (old a a sk0) ∨ a = b ∨ c = sk2 := resolve eq12379 eq8908 -- resolution 12379,8908
  have eq21177 : (sP1 a c sk4) ∨ a = b ∨ c = sk2 ∨ (sP0 a c sk4) ∨ (old a a sk0) := resolve eq21176 rfl -- duplicate literal removal 21176
  have eq21215 : (sP1 a c a) ∨ a = b ∨ c = sk2 ∨ (sP0 a c a) ∨ (old a a sk0) ∨ a = b ∨ c = sk2 := Or.assoc5 (eq18074.imp_left (fun h : a = sk4 ↦ superpose h eq21177)) -- superposition 21177,18074, 18074 into 21177, unify on (0).2 in 18074 and (0).3 in 21177
  have eq21220 : (sP1 a c a) ∨ a = b ∨ c = sk2 ∨ (sP0 a c a) ∨ (old a a sk0) := resolve eq21215 rfl -- duplicate literal removal 21215
  have eq21228 : (sP0 a c a) ∨ c = sk2 ∨ a = b ∨ (old a a sk0) := resolve eq21220 eq17936 -- subsumption resolution 21220,17936
  have eq21233 : c = sk2 ∨ a = b ∨ (old a a sk0) ∨ a = c := resolve eq21228 rule_def_0_2 -- resolution 21228,133
  have eq21236 : (old a a sk0) ∨ a = b ∨ c = sk2 := resolve eq21233 ac -- subsumption resolution 21233,107
  have eq21279 : a = b ∨ c = sk2 ∨ (new a a sk0) := resolve eq21236 imp_new_0 -- resolution 21236,129
  have eq21301 : c = sk2 ∨ a = b := resolve eq21279 eq18092 -- subsumption resolution 21279,18092
  have eq21408 : (sP3 sk0 a c) ∨ (old sk0 a c) ∨ (sP0 sk0 a c) ∨ (sP1 sk0 a c) ∨ (sP2 sk0 a c) ∨ a = c ∨ a = b := Or.assoc6 (eq21301.imp_left (fun h : c = sk2 ↦ superpose h eq5235)) -- superposition 5235,21301, 21301 into 5235, unify on (0).2 in 21301 and (0).3 in 5235
  have eq21524 : (old sk0 a c) ∨ (sP0 sk0 a c) ∨ (sP1 sk0 a c) ∨ (sP2 sk0 a c) ∨ a = c ∨ a = b := resolve eq21408 eq194 -- subsumption resolution 21408,194
  have eq21525 : (sP0 sk0 a c) ∨ (sP1 sk0 a c) ∨ (sP2 sk0 a c) ∨ a = c ∨ a = b := resolve eq21524 p4XY -- subsumption resolution 21524,110
  have eq21526 : (sP0 sk0 a c) ∨ (sP2 sk0 a c) ∨ a = c ∨ a = b := resolve eq21525 eq180 -- subsumption resolution 21525,180
  have eq21527 : (sP0 sk0 a c) ∨ (sP2 sk0 a c) ∨ a = b := resolve eq21526 ac -- subsumption resolution 21526,107
  have eq21528 : (sP2 sk0 a c) ∨ a = b := resolve eq21527 rule_def_0_1 -- subsumption resolution 21527,132
  have eq21529 : a = b := resolve eq21528 eq431 -- subsumption resolution 21528,431
  have eq21531 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 109,21529
  have eq21532 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 132,21529
  have eq21533 : ∀ (X0 X1 X2 : G) , (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_3 -- backward demodulation 138,21529
  have eq21534 : ∀ (X0 X1 X2 : G) , ¬(sP2 X0 X1 X2) ∨ a = X0 := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_0 -- backward demodulation 140,21529
  have eq21538 : ∀ (X0 X1 X2 : G) , (old X2 a (sF3 X0 X1 X2)) ∨ ¬(sP3 X0 X1 X2) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_3_4 -- backward demodulation 150,21529
  have eq21539 : ∀ (X0 X1 X2 : G) , (old a a (sF4 X0 X1 X2)) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_4 -- backward demodulation 156,21529
  have eq21541 : ∀ (X2 X3 : G) , ¬(old a X3 a) ∨ (new a c X2) ∨ ¬(old X2 a X3) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq168 -- backward demodulation 168,21529
  have eq21595 : ∀ (X0 X1 X2 X3 : G) , (old a X0 a) ∨ ¬(old b (sF3 X1 X2 X3) b) ∨ ¬(old b X3 X0) ∨ ¬(sP3 X1 X2 X3) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq293 -- backward demodulation 293,21529
  have eq21629 : ∀ (X0 X1 X2 : G) , ¬(sP3 X1 X2 X0) ∨ (new a c X0) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq427 -- backward demodulation 427,21529
  have eq22056 : a = sk2 ∨ (old a sk2 a) ∨ c = sk2 ∨ a = sk2 := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10299 -- backward demodulation 10299,21529
  have eq22129 : a = sk2 ∨ ¬(new a c sk0) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10719 -- backward demodulation 10719,21529
  have eq22787 : ¬(new a c sk0) ∨ a = sk2 ∨ c = sk2 := resolve eq22129 rfl -- duplicate literal removal 22129
  have eq22837 : (old a sk2 a) ∨ a = sk2 ∨ c = sk2 := resolve eq22056 rfl -- duplicate literal removal 22056
  have eq22960 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq21539 eq21531 -- subsumption resolution 21539,21531
  have eq22982 : ∀ (X0 X1 X2 X3 : G) , ¬(old a (sF3 X1 X2 X3) a) ∨ (old a X0 a) ∨ ¬(old b X3 X0) ∨ ¬(sP3 X1 X2 X3) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq21595 -- forward demodulation 21595,21529
  have eq22983 (X0 X1 X2 X3 : G) : (old a X0 a) ∨ ¬(old b X3 X0) ∨ ¬(sP3 X1 X2 X3) := resolve eq22982 rule_def_3_2 -- subsumption resolution 22982,148
  have eq22984 : ∀ (X0 X1 X2 X3 : G) , ¬(sP3 X1 X2 X3) ∨ (old a X0 a) ∨ ¬(old a X3 X0) := Eq.mp (by simp only [eq21529, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq22983 -- forward demodulation 22983,21529
  have eq23318 : (sP3 a sk2 sk3) ∨ (sP1 a sk2 sk3) ∨ (sP2 a sk2 sk3) ∨ (old a sk2 sk3) ∨ (sP0 a sk2 sk3) := resolve eq22960 eq5226 -- resolution 22960,5226
  have eq23319 : (sP3 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP0 a sk3 sk4) := resolve eq22960 eq5231 -- resolution 22960,5231
  have eq23360 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ (old a X3 a) ∨ ¬(old a X2 X3) ∨ ¬(sP1 X0 X1 X2) := resolve eq21533 eq292 -- resolution 21533,292
  have eq23389 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ (old a X3 a) ∨ ¬(old a X2 X3) := resolve eq23360 rfl -- duplicate literal removal 23360
  have eq23875 (X0 : G) : ¬(old X0 a sk2) ∨ c = sk2 ∨ (new a c X0) ∨ a = sk2 := resolve eq22837 eq21541 -- resolution 22837,21541
  have eq24221 (X0 : G) : (sP1 a sk2 sk3) ∨ (sP2 a sk2 sk3) ∨ (old a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old a X0 a) ∨ ¬(old a sk3 X0) := resolve eq23318 eq22984 -- resolution 23318,22984
  have eq24233 (X0 : G) : ¬(old a sk3 X0) ∨ (old a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old a X0 a) ∨ (sP2 a sk2 sk3) := resolve eq24221 eq23389 -- subsumption resolution 24221,23389
  have eq24258 : (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (new a c sk4) := resolve eq23319 eq21629 -- resolution 23319,21629
  have eq24274 : (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (new a c sk4) := resolve eq24258 eq417 -- subsumption resolution 24258,417
  have eq24472 : c = sk2 ∨ (new a c sk0) ∨ a = sk2 ∨ c = sk2 := resolve eq23875 eq5465 -- resolution 23875,5465
  have eq24473 : c = sk2 ∨ (new a c sk0) ∨ a = sk2 := resolve eq24472 rfl -- duplicate literal removal 24472
  have eq24476 : c = sk2 ∨ a = sk2 := resolve eq24473 eq22787 -- subsumption resolution 24473,22787
  have eq24481 (X0 : G) : ¬(new a c X0) ∨ sk3 = X0 ∨ a = sk2 := Or.assoc2 (eq24476.imp_left (fun h : c = sk2 ↦ superpose h eq4372)) -- superposition 4372,24476, 24476 into 4372, unify on (0).2 in 24476 and (0).2 in 4372
  have eq24486 : (sP3 sk0 a c) ∨ (old sk0 a c) ∨ (sP2 sk0 a c) ∨ a = sk0 ∨ a = sk2 := Or.assoc4 (eq24476.imp_left (fun h : c = sk2 ↦ superpose h eq5263)) -- superposition 5263,24476, 24476 into 5263, unify on (0).2 in 24476 and (0).3 in 5263
  have eq24510 : (old sk0 a c) ∨ (sP2 sk0 a c) ∨ a = sk0 ∨ a = sk2 := resolve eq24486 eq194 -- subsumption resolution 24486,194
  have eq24511 : (sP2 sk0 a c) ∨ a = sk0 ∨ a = sk2 := resolve eq24510 p4XY -- subsumption resolution 24510,110
  have eq24512 : a = sk2 ∨ a = sk0 := resolve eq24511 eq21534 -- subsumption resolution 24511,21534
  have eq24522 : (old a a sk3) ∨ a = c ∨ c = sk3 ∨ a = sk0 := Or.assoc3 (eq24512.imp_left (fun h : a = sk2 ↦ superpose h eq4571)) -- superposition 4571,24512, 24512 into 4571, unify on (0).2 in 24512 and (0).2 in 4571
  have eq24551 (X0 X1 : G) : ¬(old a X0 a) ∨ ¬(old X1 a X0) ∨ (old a X1 sk0) ∨ a = sk0 ∨ a = c ∨ a = sk0 := Or.assoc5 (eq24512.imp_left (fun h : a = sk2 ↦ superpose h eq5431)) -- superposition 5431,24512, 24512 into 5431, unify on (0).2 in 24512 and (0).3 in 5431
  have eq24608 (X0 X1 : G) : ¬(old a X0 a) ∨ ¬(old X1 a X0) ∨ (old a X1 sk0) ∨ a = sk0 ∨ a = c := resolve eq24551 rfl -- duplicate literal removal 24551
  have eq24618 : a = c ∨ c = sk3 ∨ a = sk0 := resolve eq24522 eq21531 -- subsumption resolution 24522,21531
  have eq24619 : c = sk3 ∨ a = sk0 := resolve eq24618 ac -- subsumption resolution 24618,107
  have eq24630 (X0 X1 : G) : ¬(old a X0 a) ∨ ¬(old X1 a X0) ∨ (old a X1 sk0) ∨ a = sk0 := resolve eq24608 ac -- subsumption resolution 24608,107
  have eq24725 : (old a sk3 sk4) ∨ (sP0 a sk3 sk4) ∨ (new a c sk4) ∨ c = sk4 := resolve eq24274 rule_def_2_2 -- resolution 24274,142
  have eq24734 : (new a c sk4) ∨ (old a sk3 sk4) ∨ c = sk4 := resolve eq24725 rule_def_0_2 -- subsumption resolution 24725,133
  have eq24929 : (old a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old a sk4 a) ∨ (sP2 a sk2 sk3) ∨ c = sk3 ∨ c = sk4 := resolve eq24233 eq4653 -- resolution 24233,4653
  have eq24936 : (old a sk2 sk3) ∨ (old a sk4 a) ∨ (sP2 a sk2 sk3) ∨ c = sk3 ∨ c = sk4 := resolve eq24929 rule_def_0_2 -- subsumption resolution 24929,133
  have eq24937 : (old a sk4 a) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ c = sk4 := resolve eq24936 rule_def_2_2 -- subsumption resolution 24936,142
  have eq25047 : (old a sk3 sk4) ∨ c = sk4 ∨ sk3 = sk4 ∨ a = sk2 := resolve eq24734 eq24481 -- resolution 24734,24481
  have eq25049 : (old a sk3 sk4) ∨ c = sk4 ∨ (sP3 a c sk4) ∨ (sP2 a c sk4) ∨ (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ (old a c sk4) ∨ (sP4 a c sk4) := resolve eq24734 new_imp -- resolution 24734,158
  have eq25051 : (old a sk3 sk4) ∨ c = sk4 ∨ (sP3 a c sk4) ∨ (sP2 a c sk4) ∨ (sP1 a c sk4) ∨ (sP0 a c sk4) ∨ (sP4 a c sk4) := resolve eq25049 p4XZ -- subsumption resolution 25049,111
  have eq25052 : (old a sk3 sk4) ∨ c = sk4 ∨ (sP3 a c sk4) ∨ (sP2 a c sk4) ∨ (sP1 a c sk4) ∨ (sP0 a c sk4) := resolve eq25051 eq22960 -- subsumption resolution 25051,22960
  have eq25053 : (old a sk3 sk4) ∨ c = sk4 ∨ (sP3 a c sk4) ∨ (sP2 a c sk4) ∨ (sP1 a c sk4) := resolve eq25052 rule_def_0_2 -- subsumption resolution 25052,133
  have eq25054 : (sP3 a c sk4) ∨ c = sk4 ∨ (old a sk3 sk4) ∨ (sP1 a c sk4) := resolve eq25053 rule_def_2_2 -- subsumption resolution 25053,142
  have eq25124 : c = sk4 ∨ sk3 = sk4 ∨ a = sk2 ∨ (old a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old a sk4 a) ∨ (sP2 a sk2 sk3) := resolve eq25047 eq24233 -- resolution 25047,24233
  have eq25166 : c = sk4 ∨ sk3 = sk4 ∨ a = sk2 ∨ (old a sk2 sk3) ∨ (old a sk4 a) ∨ (sP2 a sk2 sk3) := resolve eq25124 eq21532 -- subsumption resolution 25124,21532
  have eq25167 : (old a sk4 a) ∨ sk3 = sk4 ∨ a = sk2 ∨ (old a sk2 sk3) ∨ c = sk4 := resolve eq25166 rule_def_2_1 -- subsumption resolution 25166,141
  have eq25277 : (new a sk4 a) ∨ c = sk3 ∨ c = sk4 ∨ (old a sk2 sk3) := resolve eq24937 imp_new_0 -- resolution 24937,129
  have eq26033 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (old a X0 sk0) ∨ a = sk0 ∨ ¬(sP1 X1 X2 X3) := resolve eq24630 eq21533 -- resolution 24630,21533
  have eq26034 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF3 X1 X2 X3)) ∨ (old a X0 sk0) ∨ a = sk0 ∨ ¬(sP3 X1 X2 X3) := resolve eq24630 rule_def_3_2 -- resolution 24630,148
  have eq26991 : (new a sk4 a) ∨ a = sk2 ∨ (old a sk2 sk3) ∨ c = sk4 ∨ sk3 = sk4 := resolve eq25167 imp_new_0 -- resolution 25167,129
  have eq27633 (X0 X1 X2 : G) : (old a X0 sk0) ∨ a = sk0 ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq26033 rule_def_1_2 -- resolution 26033,137
  have eq27634 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ a = sk0 ∨ (old a X0 sk0) := resolve eq27633 rfl -- duplicate literal removal 27633
  have eq27645 (X0 X1 X2 : G) : (old a X0 sk0) ∨ a = sk0 ∨ ¬(sP3 X1 X2 X0) ∨ ¬(sP3 X1 X2 X0) := resolve eq26034 eq21538 -- resolution 26034,21538
  have eq27646 (X0 X1 X2 : G) : ¬(sP3 X1 X2 X0) ∨ a = sk0 ∨ (old a X0 sk0) := resolve eq27645 rfl -- duplicate literal removal 27645
  have eq27682 : a = sk0 ∨ (old a sk4 sk0) ∨ c = sk4 ∨ (old a sk3 sk4) ∨ (sP1 a c sk4) := resolve eq27646 eq25054 -- resolution 27646,25054
  have eq27707 : (old a sk4 sk0) ∨ a = sk0 ∨ c = sk4 ∨ (old a sk3 sk4) := resolve eq27682 eq27634 -- subsumption resolution 27682,27634
  have eq27749 : a = sk0 ∨ c = sk4 ∨ (old a sk3 sk4) ∨ (new a sk4 sk0) := resolve eq27707 imp_new_0 -- resolution 27707,129
  have eq27770 : (old a sk3 sk4) ∨ c = sk4 ∨ a = sk0 := resolve eq27749 eq4370 -- subsumption resolution 27749,4370
  have eq27823 : (old a c sk4) ∨ c = sk4 ∨ a = sk0 ∨ a = sk0 := Or.assoc3 (eq24619.imp_left (fun h : c = sk3 ↦ superpose h eq27770)) -- superposition 27770,24619, 24619 into 27770, unify on (0).2 in 24619 and (0).2 in 27770
  have eq27824 : (old a c sk4) ∨ c = sk4 ∨ a = sk0 := resolve eq27823 rfl -- duplicate literal removal 27823
  have eq27838 : c = sk4 ∨ a = sk0 := resolve eq27824 p4XZ -- subsumption resolution 27824,111
  have eq27849 : (sP4 a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ (old a sk3 c) ∨ (sP3 a sk3 c) ∨ a = sk0 := Or.assoc6 (eq27838.imp_left (fun h : c = sk4 ↦ superpose h eq5231)) -- superposition 5231,27838, 27838 into 5231, unify on (0).2 in 27838 and (0).3 in 5231
  have eq27942 : (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ (old a sk3 c) ∨ (sP3 a sk3 c) ∨ a = sk0 := resolve eq27849 eq22960 -- subsumption resolution 27849,22960
  have eq27943 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ (old a sk3 c) ∨ (sP3 a sk3 c) ∨ a = sk0 := resolve eq27942 eq180 -- subsumption resolution 27942,180
  have eq27944 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ (sP3 a sk3 c) ∨ a = sk0 := resolve eq27943 p4XY -- subsumption resolution 27943,110
  have eq27945 : (sP2 a sk3 c) ∨ (sP0 a sk3 c) ∨ a = sk0 := resolve eq27944 eq194 -- subsumption resolution 27944,194
  have eq28100 : (sP0 a sk3 c) ∨ a = sk0 ∨ a = sk3 := resolve eq27945 rule_def_2_1 -- resolution 27945,141
  have eq28107 : a = sk3 ∨ a = sk0 := resolve eq28100 eq21532 -- subsumption resolution 28100,21532
  have eq28115 : a = c ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq24619.imp_left (fun h : c = sk3 ↦ superpose h eq28107)) -- superposition 28107,24619, 24619 into 28107, unify on (0).2 in 24619 and (0).2 in 28107
  have eq28299 : a = c ∨ a = sk0 := resolve eq28115 rfl -- duplicate literal removal 28115
  have eq28301 : a = sk0 := resolve eq28299 ac -- subsumption resolution 28299,107
  have eq28303 : ¬(new a sk4 a) := Eq.mp (by simp only [eq28301, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4370 -- backward demodulation 4370,28301
  have eq28309 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq28301, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5465 -- backward demodulation 5465,28301
  have eq28451 : c = sk2 := resolve eq28309 eq21531 -- subsumption resolution 28309,21531
  have eq28452 : (new a c sk3) := Eq.mp (by simp only [eq28451, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4368 -- backward demodulation 4368,28451
  have eq28754 : (old a c sk3) ∨ (new a sk4 a) ∨ c = sk3 ∨ c = sk4 := Eq.mp (by simp only [eq28451, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq25277 -- backward demodulation 25277,28451
  have eq28817 : a = c ∨ (new a sk4 a) ∨ (old a sk2 sk3) ∨ c = sk4 ∨ sk3 = sk4 := Eq.mp (by simp only [eq28451, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq26991 -- backward demodulation 26991,28451
  have eq29359 : (new a sk4 a) ∨ c = sk3 ∨ c = sk4 := resolve eq28754 p4XZ -- subsumption resolution 28754,111
  have eq29360 : c = sk4 ∨ c = sk3 := resolve eq29359 eq28303 -- subsumption resolution 29359,28303
  have eq29446 : (new a sk4 a) ∨ (old a sk2 sk3) ∨ c = sk4 ∨ sk3 = sk4 := resolve eq28817 ac -- subsumption resolution 28817,107
  have eq29447 : (old a sk2 sk3) ∨ c = sk4 ∨ sk3 = sk4 := resolve eq29446 eq28303 -- subsumption resolution 29446,28303
  have eq29448 : (old a c sk3) ∨ c = sk4 ∨ sk3 = sk4 := Eq.mp (by simp only [eq28451, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq29447 -- forward demodulation 29447,28451
  have eq29449 : sk3 = sk4 ∨ c = sk4 := resolve eq29448 p4XZ -- subsumption resolution 29448,111
  have eq29800 : c ≠ sk3 ∨ c = sk4 := resolve eq29449 trans_resol -- equality factoring 29449
  have eq29848 : c = sk4 := resolve eq29800 eq29360 -- subsumption resolution 29800,29360
  have eq29862 : (sP4 a sk3 c) ∨ (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5231 -- backward demodulation 5231,29848
  have eq29991 : ¬(new a c a) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq28303 -- backward demodulation 28303,29848
  have eq30116 : (sP0 a sk3 sk4) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := resolve eq29862 eq22960 -- subsumption resolution 29862,22960
  have eq30117 : (sP0 a sk3 c) ∨ (sP1 a sk3 sk4) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq30116 -- forward demodulation 30116,29848
  have eq30118 : (sP1 a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq30117 -- forward demodulation 30117,29848
  have eq30119 : (sP0 a sk3 c) ∨ (sP2 a sk3 sk4) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := resolve eq30118 eq180 -- subsumption resolution 30118,180
  have eq30120 : (sP2 a sk3 c) ∨ (sP0 a sk3 c) ∨ (old a sk3 sk4) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq30119 -- forward demodulation 30119,29848
  have eq30121 : (old a sk3 c) ∨ (sP2 a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP3 a sk3 sk4) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq30120 -- forward demodulation 30120,29848
  have eq30122 : (sP2 a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP3 a sk3 sk4) := resolve eq30121 p4XY -- subsumption resolution 30121,110
  have eq30123 : (sP3 a sk3 c) ∨ (sP2 a sk3 c) ∨ (sP0 a sk3 c) := Eq.mp (by simp only [eq29848, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq30122 -- forward demodulation 30122,29848
  have eq30124 : (sP2 a sk3 c) ∨ (sP0 a sk3 c) := resolve eq30123 eq194 -- subsumption resolution 30123,194
  have eq30424 : (sP0 a sk3 c) ∨ a = sk3 := resolve eq30124 rule_def_2_1 -- resolution 30124,141
  have eq30426 : a = sk3 := resolve eq30424 eq21532 -- subsumption resolution 30424,21532
  have eq30427 : (new a c a) := Eq.mp (by simp only [eq30426, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq28452 -- backward demodulation 28452,30426
  subsumption eq29991 eq30427 -- subsumption resolution 30427,29991

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X0 X1)) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq179 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 137,112
  have eq193 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 150,112
  have eq371 : (sP4 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) := resolve new_imp preserve_0 -- resolution 158,161
  have eq522 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ c = sk1 := resolve eq371 rule_def_4_1 -- resolution 371,153
  have eq523 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ a = sk1 := resolve eq371 rule_def_4_2 -- resolution 371,154
  have eq533 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ c = sk1 := resolve eq522 rule_def_0_2 -- subsumption resolution 522,133
  have eq534 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ c = sk1 := resolve eq533 rule_def_1_1 -- subsumption resolution 533,136
  have eq535 : (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ c = sk1 := resolve eq534 rule_def_2_2 -- subsumption resolution 534,142
  have eq536 : (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq535 rule_def_3_1 -- subsumption resolution 535,147
  have eq537 : (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ a = sk1 := resolve eq523 rule_def_2_1 -- subsumption resolution 523,141
  have eq540 : (old sk1 sk0 sk1) ∨ c = sk1 := resolve eq536 old_2 -- resolution 536,115
  have eq571 : c = sk1 ∨ (new sk1 sk0 sk1) := resolve eq540 imp_new_0 -- resolution 540,129
  have eq573 : c = sk1 := resolve eq571 preserve_1 -- subsumption resolution 571,162
  have eq588 : (sP3 sk0 c c) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq573, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq537 -- backward demodulation 537,573
  have eq655 : (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ a = sk1 := resolve eq588 eq193 -- subsumption resolution 588,193
  have eq656 : (sP1 sk0 c c) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq573, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq655 -- forward demodulation 655,573
  have eq657 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ a = sk1 := resolve eq656 eq179 -- subsumption resolution 656,179
  have eq658 : (sP0 sk0 c c) ∨ (old sk0 sk1 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq573, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq657 -- forward demodulation 657,573
  have eq659 : (old sk0 c c) ∨ (sP0 sk0 c c) ∨ a = sk1 := Eq.mp (by simp only [eq573, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq658 -- forward demodulation 658,573
  have eq660 : (sP0 sk0 c c) ∨ a = sk1 := resolve eq659 p4XZ -- subsumption resolution 659,111
  have eq661 : a = c ∨ (sP0 sk0 c c) := Eq.mp (by simp only [eq573, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq660 -- forward demodulation 660,573
  have eq662 : (sP0 sk0 c c) := resolve eq661 ac -- subsumption resolution 661,107
  have eq669 : c = b := resolve eq662 rule_def_0_1 -- resolution 662,132
  subsumption bc eq669 -- subsumption resolution 669,108

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1, ¬ old X0 X1 X0 ∨ ¬ old X1 X0 X1 ∨ old X0 X0 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X0 ∨ ¬ new X1 X0 X1 ∨ new X0 X0 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq376 : (sP4 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 161,165
  have eq377 : (sP4 sk1 sk0 sk1) ∨ (sP2 sk1 sk0 sk1) ∨ (sP1 sk1 sk0 sk1) ∨ (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP3 sk1 sk0 sk1) := resolve new_imp preserve_1 -- resolution 161,166
  have eq529 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq376 rule_def_4_0 -- resolution 376,155
  have eq530 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq376 rule_def_4_1 -- resolution 376,156
  have eq539 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq529 rule_def_0_0 -- subsumption resolution 529,134
  have eq540 : (sP3 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 := resolve eq539 rule_def_1_0 -- subsumption resolution 539,138
  have eq541 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq530 rule_def_1_1 -- subsumption resolution 530,139
  have eq542 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq541 rule_def_3_1 -- subsumption resolution 541,150
  have eq545 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq540 rule_def_3_0 -- resolution 540,149
  have eq556 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq545 rule_def_2_0 -- subsumption resolution 545,143
  have eq560 : (sP2 sk1 sk0 sk1) ∨ (sP1 sk1 sk0 sk1) ∨ (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP3 sk1 sk0 sk1) ∨ a = sk1 := resolve eq377 rule_def_4_0 -- resolution 377,155
  have eq561 : (sP2 sk1 sk0 sk1) ∨ (sP1 sk1 sk0 sk1) ∨ (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP3 sk1 sk0 sk1) ∨ c = sk0 := resolve eq377 rule_def_4_1 -- resolution 377,156
  have eq570 : (sP2 sk1 sk0 sk1) ∨ (sP1 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP3 sk1 sk0 sk1) ∨ a = sk1 := resolve eq560 rule_def_0_0 -- subsumption resolution 560,134
  have eq571 : (sP3 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP2 sk1 sk0 sk1) ∨ a = sk1 := resolve eq570 rule_def_1_0 -- subsumption resolution 570,138
  have eq572 : (sP2 sk1 sk0 sk1) ∨ (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ (sP3 sk1 sk0 sk1) ∨ c = sk0 := resolve eq561 rule_def_1_1 -- subsumption resolution 561,139
  have eq573 : (sP2 sk1 sk0 sk1) ∨ (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ c = sk0 := resolve eq572 rule_def_3_1 -- subsumption resolution 572,150
  have eq743 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq542 rule_def_2_2 -- resolution 542,145
  have eq746 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq743 rule_def_0_2 -- subsumption resolution 743,136
  have eq901 : (old sk1 sk0 sk1) ∨ (sP2 sk1 sk0 sk1) ∨ a = sk1 ∨ b = sk1 := resolve eq571 rule_def_3_0 -- resolution 571,149
  have eq902 : (sP2 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ a = sk1 ∨ c = sk0 := resolve eq571 rule_def_3_1 -- resolution 571,150
  have eq912 : (old sk1 sk0 sk1) ∨ a = sk1 ∨ b = sk1 := resolve eq901 rule_def_2_0 -- subsumption resolution 901,143
  have eq1018 : (old sk1 sk0 sk1) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 := resolve eq902 rule_def_2_2 -- resolution 902,145
  have eq1028 : a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ (old sk0 sk0 sk0) ∨ ¬(old sk0 sk1 sk0) := resolve eq1018 old_3 -- resolution 1018,119
  have eq1050 : (old sk0 sk0 sk0) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 := resolve eq1028 eq746 -- subsumption resolution 1028,746
  have eq1130 : c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ (new sk0 sk0 sk0) := resolve eq1050 imp_new_0 -- resolution 1050,132
  have eq1134 : c = sk1 ∨ c = sk0 ∨ a = sk1 := resolve eq1130 preserve_2 -- subsumption resolution 1130,167
  have eq1154 : (old c sk0 c) ∨ a = c ∨ c = b ∨ c = sk0 ∨ a = sk1 := Or.assoc3 (eq1134.imp_left (fun h : c = sk1 ↦ superpose h eq912)) -- superposition 912,1134, 1134 into 912, unify on (0).2 in 1134 and (0).1 in 912
  have eq1180 : a = c ∨ c = b ∨ c = sk0 ∨ a = sk1 := resolve eq1154 p4YZ -- subsumption resolution 1154,115
  have eq1181 : c = b ∨ c = sk0 ∨ a = sk1 := resolve eq1180 ac -- subsumption resolution 1180,110
  have eq1182 : a = sk1 ∨ c = sk0 := resolve eq1181 bc -- subsumption resolution 1181,111
  have eq1193 : (sP2 sk0 a sk0) ∨ (sP0 sk0 a sk0) ∨ (old sk0 a sk0) ∨ a = c ∨ c = sk0 := Or.assoc4 (eq1182.imp_left (fun h : a = sk1 ↦ superpose h eq542)) -- superposition 542,1182, 1182 into 542, unify on (0).2 in 1182 and (0).2 in 542
  have eq1225 : (sP2 sk0 a sk0) ∨ (sP0 sk0 a sk0) ∨ (old sk0 a sk0) ∨ c = sk0 := resolve eq1193 ac -- subsumption resolution 1193,110
  have eq1226 : (sP2 sk0 a sk0) ∨ (old sk0 a sk0) ∨ c = sk0 := resolve eq1225 rule_def_0_2 -- subsumption resolution 1225,136
  have eq1227 : (old sk0 a sk0) ∨ c = sk0 := resolve eq1226 rule_def_2_2 -- subsumption resolution 1226,145
  have eq1413 : (sP0 sk1 sk0 sk1) ∨ (old sk1 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq573 rule_def_2_2 -- resolution 573,145
  have eq1424 : (old sk1 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1413 rule_def_0_2 -- subsumption resolution 1413,136
  have eq1450 : (old a sk0 a) ∨ c = sk0 ∨ a = c ∨ c = sk0 := Or.assoc3 (eq1182.imp_left (fun h : a = sk1 ↦ superpose h eq1424)) -- superposition 1424,1182, 1182 into 1424, unify on (0).2 in 1182 and (0).1 in 1424
  have eq1451 : (old a sk0 a) ∨ c = sk0 ∨ a = c := resolve eq1450 rfl -- duplicate literal removal 1450
  have eq1462 : (old a sk0 a) ∨ c = sk0 := resolve eq1451 ac -- subsumption resolution 1451,110
  have eq1466 : c = sk0 ∨ (old sk0 sk0 sk0) ∨ ¬(old sk0 a sk0) := resolve eq1462 old_3 -- resolution 1462,119
  have eq1484 : (old sk0 sk0 sk0) ∨ c = sk0 := resolve eq1466 eq1227 -- subsumption resolution 1466,1227
  have eq1527 : c = sk0 ∨ (new sk0 sk0 sk0) := resolve eq1484 imp_new_0 -- resolution 1484,132
  have eq1531 : c = sk0 := resolve eq1527 preserve_2 -- subsumption resolution 1527,167
  have eq1557 : (old c sk1 c) ∨ a = sk0 ∨ b = sk0 := Eq.mp (by simp only [eq1531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq556 -- backward demodulation 556,1531
  have eq1894 : a = sk0 ∨ b = sk0 := resolve eq1557 p4YZ -- subsumption resolution 1557,115
  have eq1895 : a = c ∨ b = sk0 := Eq.mp (by simp only [eq1531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1894 -- forward demodulation 1894,1531
  have eq1896 : b = sk0 := resolve eq1895 ac -- subsumption resolution 1895,110
  have eq1897 : c = b := Eq.mp (by simp only [eq1531, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1896 -- forward demodulation 1896,1531
  subsumption bc eq1897 -- subsumption resolution 1897,111

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X4 ∨ ¬ new X3 X1 X2 ∨ new X0 X3 X4) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq193 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 154,127
  have eq230 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 149,127
  have eq386 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 164,169
  have eq388 : (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) := resolve new_imp preserve_2 -- resolution 164,171
  have eq405 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq193 rule_def_3_3 -- resolution 193,155
  have eq406 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq405 rfl -- duplicate literal removal 405
  have eq451 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq230 rule_def_2_4 -- resolution 230,150
  have eq454 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq451 rfl -- duplicate literal removal 451
  have eq540 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq386 rule_def_4_0 -- resolution 386,158
  have eq541 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq386 rule_def_4_1 -- resolution 386,159
  have eq550 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq540 rule_def_0_0 -- subsumption resolution 540,137
  have eq551 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq550 rule_def_1_0 -- subsumption resolution 550,141
  have eq552 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq541 rule_def_1_1 -- subsumption resolution 541,142
  have eq553 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq552 rule_def_3_1 -- subsumption resolution 552,153
  have eq556 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq551 rule_def_3_0 -- resolution 551,152
  have eq563 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq551 eq406 -- resolution 551,406
  have eq567 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq556 rule_def_2_0 -- subsumption resolution 556,146
  have eq569 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq563 eq454 -- subsumption resolution 563,454
  have eq602 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ a = sk3 := resolve eq388 rule_def_4_0 -- resolution 388,158
  have eq603 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ c = sk1 := resolve eq388 rule_def_4_1 -- resolution 388,159
  have eq612 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ a = sk3 := resolve eq602 rule_def_0_0 -- subsumption resolution 602,137
  have eq613 : (sP3 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 := resolve eq612 rule_def_1_0 -- subsumption resolution 612,141
  have eq614 : (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ c = sk1 := resolve eq603 rule_def_1_1 -- subsumption resolution 603,142
  have eq615 : (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 := resolve eq614 rule_def_3_1 -- subsumption resolution 614,153
  have eq729 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq553 rule_def_2_2 -- resolution 553,148
  have eq732 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq729 rule_def_0_2 -- subsumption resolution 729,139
  have eq745 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 := resolve eq732 old_8 -- resolution 732,127
  have eq1183 : (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq613 rule_def_3_0 -- resolution 613,152
  have eq1190 : (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 ∨ a = b := resolve eq613 eq406 -- resolution 613,406
  have eq1194 : (old sk3 sk1 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq1183 rule_def_2_0 -- subsumption resolution 1183,146
  have eq1196 : (old sk3 sk1 sk2) ∨ a = sk3 ∨ a = b := resolve eq1190 eq454 -- subsumption resolution 1190,454
  have eq1388 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq615 rule_def_2_2 -- resolution 615,148
  have eq1393 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1388 rule_def_0_2 -- subsumption resolution 1388,139
  have eq1400 : c = sk1 ∨ c = sk2 ∨ c = sk2 ∨ sk0 = sk3 ∨ c = sk1 := resolve eq1393 eq745 -- resolution 1393,745
  have eq1420 : sk0 = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1400 rfl -- duplicate literal removal 1400
  have eq1425 : (new sk0 sk0 sk4) ∨ c = sk2 ∨ c = sk1 := eq1420.imp_left (fun h : sk0 = sk3 ↦ superpose h preserve_1) -- superposition 170,1420, 1420 into 170, unify on (0).2 in 1420 and (0).1 in 170
  have eq1427 : ¬(new sk0 sk0 sk4) ∨ c = sk2 ∨ c = sk1 := eq1420.imp_left (fun h : sk0 = sk3 ↦ superpose h preserve_3) -- superposition 172,1420, 1420 into 172, unify on (0).2 in 1420 and (0).2 in 172
  have eq1465 : c = sk2 ∨ c = sk1 := resolve eq1427 eq1425 -- subsumption resolution 1427,1425
  have eq1477 : (old sk0 sk1 c) ∨ a = sk0 ∨ b = sk0 ∨ c = sk1 := Or.assoc3 (eq1465.imp_left (fun h : c = sk2 ↦ superpose h eq567)) -- superposition 567,1465, 1465 into 567, unify on (0).2 in 1465 and (0).3 in 567
  have eq1478 : (old sk0 sk1 c) ∨ a = sk0 ∨ a = b ∨ c = sk1 := Or.assoc3 (eq1465.imp_left (fun h : c = sk2 ↦ superpose h eq569)) -- superposition 569,1465, 1465 into 569, unify on (0).2 in 1465 and (0).3 in 569
  have eq1490 : (old sk3 sk1 c) ∨ a = sk3 ∨ b = sk3 ∨ c = sk1 := Or.assoc3 (eq1465.imp_left (fun h : c = sk2 ↦ superpose h eq1194)) -- superposition 1194,1465, 1465 into 1194, unify on (0).2 in 1465 and (0).3 in 1194
  have eq1491 : (old sk3 sk1 c) ∨ a = sk3 ∨ a = b ∨ c = sk1 := Or.assoc3 (eq1465.imp_left (fun h : c = sk2 ↦ superpose h eq1196)) -- superposition 1196,1465, 1465 into 1196, unify on (0).2 in 1465 and (0).3 in 1196
  have eq1515 : c = sk1 ∨ b = sk0 ∨ a = sk0 := resolve eq1477 p4XY -- subsumption resolution 1477,116
  have eq1516 : c = sk1 ∨ a = b ∨ a = sk0 := resolve eq1478 p4XY -- subsumption resolution 1478,116
  have eq1526 : b = sk3 ∨ a = sk3 ∨ c = sk1 := resolve eq1490 p4XY -- subsumption resolution 1490,116
  have eq1527 : a = sk3 ∨ a = b ∨ c = sk1 := resolve eq1491 p4XY -- subsumption resolution 1491,116
  have eq1550 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := Or.assoc6 (eq1515.imp_left (fun h : c = sk1 ↦ superpose h eq386)) -- superposition 386,1515, 1515 into 386, unify on (0).2 in 1515 and (0).2 in 386
  have eq1575 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1550 p4XZ -- subsumption resolution 1550,117
  have eq1576 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1575 rule_def_0_0 -- subsumption resolution 1575,137
  have eq1577 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1576 rule_def_1_0 -- subsumption resolution 1576,141
  have eq1578 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1577 rule_def_4_0 -- subsumption resolution 1577,158
  have eq1579 : (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1578 rule_def_2_0 -- subsumption resolution 1578,146
  have eq1580 : b = sk0 ∨ a = sk0 := resolve eq1579 rule_def_3_0 -- subsumption resolution 1579,152
  have eq1627 : a ≠ b ∨ a = sk0 := resolve eq1580 trans_resol -- equality factoring 1580
  have eq1733 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := Or.assoc6 (eq1516.imp_left (fun h : c = sk1 ↦ superpose h eq386)) -- superposition 386,1516, 1516 into 386, unify on (0).2 in 1516 and (0).2 in 386
  have eq1771 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1733 p4XZ -- subsumption resolution 1733,117
  have eq1772 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1771 rule_def_0_0 -- subsumption resolution 1771,137
  have eq1773 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1772 rule_def_1_0 -- subsumption resolution 1772,141
  have eq1774 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1773 rule_def_4_0 -- subsumption resolution 1773,158
  have eq1775 : (sP2 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1774 eq406 -- subsumption resolution 1774,406
  have eq1776 : a = b ∨ a = sk0 := resolve eq1775 eq454 -- subsumption resolution 1775,454
  have eq1777 : a = sk0 := resolve eq1776 eq1627 -- subsumption resolution 1776,1627
  have eq1779 : (new sk3 a sk4) := Eq.mp (by simp only [eq1777, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 170,1777
  have eq1780 : ¬(new a sk3 sk4) := Eq.mp (by simp only [eq1777, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 172,1777
  have eq2705 : a ≠ b ∨ a = sk3 ∨ c = sk1 := resolve eq1526 trans_resol -- equality factoring 1526
  have eq2714 : a = sk3 ∨ c = sk1 := resolve eq2705 eq1527 -- subsumption resolution 2705,1527
  have eq2739 : (new a a sk4) ∨ c = sk1 := eq2714.imp_left (fun h : a = sk3 ↦ superpose h eq1779) -- superposition 1779,2714, 2714 into 1779, unify on (0).2 in 2714 and (0).1 in 1779
  have eq2740 : ¬(new a a sk4) ∨ c = sk1 := eq2714.imp_left (fun h : a = sk3 ↦ superpose h eq1780) -- superposition 1780,2714, 2714 into 1780, unify on (0).2 in 2714 and (0).2 in 1780
  have eq2752 : c = sk1 := resolve eq2740 eq2739 -- subsumption resolution 2740,2739
  have eq2775 : (old sk3 c sk2) ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq2752, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1194 -- backward demodulation 1194,2752
  have eq2777 : (old sk3 c sk2) ∨ a = sk3 ∨ a = b := Eq.mp (by simp only [eq2752, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1196 -- backward demodulation 1196,2752
  have eq2931 : b = sk3 ∨ a = sk3 := resolve eq2775 p4XZ -- subsumption resolution 2775,117
  have eq2933 : a = sk3 ∨ a = b := resolve eq2777 p4XZ -- subsumption resolution 2777,117
  have eq3125 : a ≠ b ∨ a = sk3 := resolve eq2931 trans_resol -- equality factoring 2931
  have eq3130 : a = sk3 := resolve eq3125 eq2933 -- subsumption resolution 3125,2933
  have eq3131 : (new a a sk4) := Eq.mp (by simp only [eq3130, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1779 -- backward demodulation 1779,3130
  have eq3132 : ¬(new a a sk4) := Eq.mp (by simp only [eq3130, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1780 -- backward demodulation 1780,3130
  subsumption eq3131 eq3132 -- subsumption resolution 3132,3131

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_5 : (∀ X0 X1 X2 X3, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X3 X0 X2 ∨ X1 = X3)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_10 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X0 ∨ ¬ old X2 X0 X3 ∨ ¬ old X3 X0 X1 ∨ old X0 X0 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X2 ∨ X1 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq192 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 145,120
  have eq196 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 156,129
  have eq206 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 158,120
  have eq233 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 151,129
  have eq286 (X0 X1 X2 X3 : G) : ¬(old a (sF0 X2 X3 X1) a) ∨ ¬(old X0 a X1) ∨ (old a a X0) ∨ ¬(sP1 X2 X3 X1) := resolve old_10 rule_def_1_2 -- resolution 131,145
  have eq287 (X0 X1 X2 X3 : G) : ¬(old b (sF3 X2 X3 X1) b) ∨ ¬(old X0 b X1) ∨ (old b b X0) ∨ ¬(sP3 X2 X3 X1) := resolve old_10 rule_def_3_4 -- resolution 131,158
  have eq404 : (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 166,172
  have eq405 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 166,173
  have eq406 : (sP4 sk3 sk0 sk2) ∨ (sP2 sk3 sk0 sk2) ∨ (sP1 sk3 sk0 sk2) ∨ (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP3 sk3 sk0 sk2) := resolve new_imp preserve_2 -- resolution 166,174
  have eq447 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq196 rule_def_3_3 -- resolution 196,157
  have eq448 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq447 rfl -- duplicate literal removal 447
  have eq486 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq233 rule_def_2_4 -- resolution 233,152
  have eq489 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq486 rfl -- duplicate literal removal 486
  have eq606 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ a = sk0 := resolve eq404 rule_def_4_0 -- resolution 404,160
  have eq607 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ c = sk0 := resolve eq404 rule_def_4_1 -- resolution 404,161
  have eq616 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ a = sk0 := resolve eq606 rule_def_0_0 -- subsumption resolution 606,139
  have eq617 : (sP2 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ a = sk0 := resolve eq616 rule_def_1_0 -- subsumption resolution 616,143
  have eq618 : (sP3 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 := resolve eq617 rule_def_2_1 -- subsumption resolution 617,149
  have eq619 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ c = sk0 := resolve eq607 rule_def_1_1 -- subsumption resolution 607,144
  have eq620 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq619 rule_def_3_1 -- subsumption resolution 619,155
  have eq630 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ a = b := resolve eq618 eq448 -- resolution 618,448
  have eq634 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq405 rule_def_4_0 -- resolution 405,160
  have eq635 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq405 rule_def_4_1 -- resolution 405,161
  have eq644 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq634 rule_def_0_0 -- subsumption resolution 634,139
  have eq645 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq644 rule_def_1_0 -- subsumption resolution 644,143
  have eq646 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq635 rule_def_1_1 -- subsumption resolution 635,144
  have eq647 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq646 rule_def_3_1 -- subsumption resolution 646,155
  have eq665 : (sP2 sk3 sk0 sk2) ∨ (sP1 sk3 sk0 sk2) ∨ (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP3 sk3 sk0 sk2) ∨ a = sk3 := resolve eq406 rule_def_4_0 -- resolution 406,160
  have eq666 : (sP2 sk3 sk0 sk2) ∨ (sP1 sk3 sk0 sk2) ∨ (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP3 sk3 sk0 sk2) ∨ c = sk0 := resolve eq406 rule_def_4_1 -- resolution 406,161
  have eq675 : (sP2 sk3 sk0 sk2) ∨ (sP1 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP3 sk3 sk0 sk2) ∨ a = sk3 := resolve eq665 rule_def_0_0 -- subsumption resolution 665,139
  have eq676 : (sP3 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP2 sk3 sk0 sk2) ∨ a = sk3 := resolve eq675 rule_def_1_0 -- subsumption resolution 675,143
  have eq677 : (sP2 sk3 sk0 sk2) ∨ (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ (sP3 sk3 sk0 sk2) ∨ c = sk0 := resolve eq666 rule_def_1_1 -- subsumption resolution 666,144
  have eq678 : (sP2 sk3 sk0 sk2) ∨ (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ c = sk0 := resolve eq677 rule_def_3_1 -- subsumption resolution 677,155
  have eq787 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq620 rule_def_2_2 -- resolution 620,150
  have eq790 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq787 rule_def_0_2 -- subsumption resolution 787,141
  have eq933 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq645 rule_def_3_0 -- resolution 645,154
  have eq940 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq645 eq448 -- resolution 645,448
  have eq944 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq933 rule_def_2_0 -- subsumption resolution 933,148
  have eq946 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq940 eq489 -- subsumption resolution 940,489
  have eq1080 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq647 rule_def_2_2 -- resolution 647,150
  have eq1081 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq647 rule_def_2_1 -- resolution 647,149
  have eq1083 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1080 rule_def_0_2 -- subsumption resolution 1080,141
  have eq1157 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1081 rule_def_0_1 -- resolution 1081,140
  have eq1210 : (old sk3 sk0 sk2) ∨ (sP2 sk3 sk0 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq676 rule_def_3_0 -- resolution 676,154
  have eq1221 : (old sk3 sk0 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq1210 rule_def_2_0 -- subsumption resolution 1210,148
  have eq1354 : (sP0 sk3 sk0 sk2) ∨ (old sk3 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq678 rule_def_2_2 -- resolution 678,150
  have eq1357 : (old sk3 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq1354 rule_def_0_2 -- subsumption resolution 1354,141
  have eq1365 (X0 : G) : ¬(old sk0 sk0 X0) ∨ c = sk2 ∨ sk3 = X0 ∨ ¬(old sk0 X0 sk2) ∨ c = sk0 := resolve eq1357 old_5 -- resolution 1357,126
  have eq3413 : c = sk2 ∨ sk1 = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq1365 eq790 -- resolution 1365,790
  have eq3414 : c = sk2 ∨ sk1 = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq1365 eq630 -- resolution 1365,630
  have eq3418 : c = sk2 ∨ sk1 = sk3 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq3413 rfl -- duplicate literal removal 3413
  have eq3421 : c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq3418 preserve_3 -- subsumption resolution 3418,175
  have eq3422 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq3421 eq1083 -- subsumption resolution 3421,1083
  have eq3423 : c = sk2 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3414 preserve_3 -- subsumption resolution 3414,175
  have eq3424 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3423 eq946 -- subsumption resolution 3423,946
  have eq3461 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 := Or.assoc4 (eq3422.imp_left (fun h : c = sk2 ↦ superpose h eq1157)) -- superposition 1157,3422, 3422 into 1157, unify on (0).2 in 3422 and (0).3 in 1157
  have eq3471 : (old sk3 sk0 c) ∨ a = sk3 ∨ b = sk3 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq3422.imp_left (fun h : c = sk2 ↦ superpose h eq1221)) -- superposition 1221,3422, 3422 into 1221, unify on (0).2 in 3422 and (0).3 in 1221
  have eq3542 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 := resolve eq3461 rfl -- duplicate literal removal 3461
  have eq3576 : c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 := resolve eq3542 p4XY -- subsumption resolution 3542,118
  have eq3578 : a = sk3 ∨ b = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq3471 p4XY -- subsumption resolution 3471,118
  have eq3622 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := Or.assoc6 (eq3424.imp_left (fun h : c = sk2 ↦ superpose h eq405)) -- superposition 405,3424, 3424 into 405, unify on (0).2 in 3424 and (0).3 in 405
  have eq3766 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3622 eq192 -- subsumption resolution 3622,192
  have eq3767 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3766 p4XY -- subsumption resolution 3766,118
  have eq3768 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3767 eq206 -- subsumption resolution 3767,206
  have eq3769 : (sP4 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3768 eq489 -- subsumption resolution 3768,489
  have eq3770 : (sP4 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3769 rule_def_0_0 -- subsumption resolution 3769,139
  have eq3771 : c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3770 rule_def_4_0 -- subsumption resolution 3770,160
  have eq3812 : (sP3 c c sk1) ∨ (old c c sk1) ∨ a = c ∨ a = sk0 ∨ a = b := Or.assoc3 (eq3771.imp_left (fun h : c = sk0 ↦ superpose h eq618)) -- superposition 618,3771, 3771 into 618, unify on (0).2 in 3771 and (0).1 in 618
  have eq3944 : (sP3 c c sk1) ∨ a = c ∨ a = sk0 ∨ a = b := resolve eq3812 p4YZ -- subsumption resolution 3812,120
  have eq3945 : (sP3 c c sk1) ∨ a = sk0 ∨ a = b := resolve eq3944 ac -- subsumption resolution 3944,115
  have eq3946 : a = sk0 ∨ a = b := resolve eq3945 eq448 -- subsumption resolution 3945,448
  have eq3995 : (sP2 a a sk1) ∨ (sP0 a a sk1) ∨ (old a a sk1) ∨ a = c ∨ a = b := Or.assoc4 (eq3946.imp_left (fun h : a = sk0 ↦ superpose h eq620)) -- superposition 620,3946, 3946 into 620, unify on (0).2 in 3946 and (0).1 in 620
  have eq4002 : (sP2 sk3 a sk2) ∨ (sP0 sk3 a sk2) ∨ (old sk3 a sk2) ∨ a = c ∨ a = b := Or.assoc4 (eq3946.imp_left (fun h : a = sk0 ↦ superpose h eq678)) -- superposition 678,3946, 3946 into 678, unify on (0).2 in 3946 and (0).2 in 678
  have eq4155 : (sP2 a a sk1) ∨ (sP0 a a sk1) ∨ (old a a sk1) ∨ a = b := resolve eq3995 ac -- subsumption resolution 3995,115
  have eq4156 : (sP2 a a sk1) ∨ (old a a sk1) ∨ a = b := resolve eq4155 rule_def_0_1 -- subsumption resolution 4155,140
  have eq4157 : (old a a sk1) ∨ a = b := resolve eq4156 rule_def_2_0 -- subsumption resolution 4156,148
  have eq4171 : (sP2 sk3 a sk2) ∨ (sP0 sk3 a sk2) ∨ (old sk3 a sk2) ∨ a = b := resolve eq4002 ac -- subsumption resolution 4002,115
  have eq4172 : (sP2 sk3 a sk2) ∨ (old sk3 a sk2) ∨ a = b := resolve eq4171 rule_def_0_1 -- subsumption resolution 4171,140
  have eq4173 : (old sk3 a sk2) ∨ a = b := resolve eq4172 eq489 -- subsumption resolution 4172,489
  have eq4301 : (old sk3 a c) ∨ a = b ∨ c = sk0 ∨ c = sk1 := Or.assoc2 (eq3422.imp_left (fun h : c = sk2 ↦ superpose h eq4173)) -- superposition 4173,3422, 3422 into 4173, unify on (0).2 in 3422 and (0).3 in 4173
  have eq4306 : c = sk1 ∨ c = sk0 ∨ a = b := resolve eq4301 p4XY -- subsumption resolution 4301,118
  have eq4385 : (old a a c) ∨ a = b ∨ c = sk0 ∨ a = b := Or.assoc2 (eq4306.imp_left (fun h : c = sk1 ↦ superpose h eq4157)) -- superposition 4157,4306, 4306 into 4157, unify on (0).2 in 4306 and (0).3 in 4157
  have eq4386 : (old a a c) ∨ a = b ∨ c = sk0 := resolve eq4385 rfl -- duplicate literal removal 4385
  have eq4434 : c = sk0 ∨ a = b := resolve eq4386 p4XY -- subsumption resolution 4386,118
  have eq4437 : a = c ∨ a = b ∨ a = b := Or.assoc2 (eq3946.imp_left (fun h : a = sk0 ↦ superpose h eq4434)) -- superposition 4434,3946, 3946 into 4434, unify on (0).2 in 3946 and (0).2 in 4434
  have eq4595 : a = c ∨ a = b := resolve eq4437 rfl -- duplicate literal removal 4437
  have eq4596 : a = b := resolve eq4595 ac -- subsumption resolution 4595,115
  have eq4598 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 117,4596
  have eq4599 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 140,4596
  have eq4600 : ∀ (X0 X1 X2 : G) , (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_3 -- backward demodulation 146,4596
  have eq4606 : ∀ (X0 X1 X2 : G) , (old a a (sF4 X0 X1 X2)) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_4 -- backward demodulation 164,4596
  have eq4652 : ∀ (X0 X1 X2 X3 : G) , ¬(old X0 a X1) ∨ ¬(old b (sF3 X2 X3 X1) b) ∨ (old b b X0) ∨ ¬(sP3 X2 X3 X1) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq287 -- backward demodulation 287,4596
  have eq4819 : a = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq944 -- backward demodulation 944,4596
  have eq5297 : a = sk1 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3576 -- backward demodulation 3576,4596
  have eq5299 : a = sk3 ∨ a = sk3 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3578 -- backward demodulation 3578,4596
  have eq5309 : a = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq5299 rfl -- duplicate literal removal 5299
  have eq5310 : a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq5297 rfl -- duplicate literal removal 5297
  have eq5403 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq4819 rfl -- duplicate literal removal 4819
  have eq5417 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq4606 eq4598 -- subsumption resolution 4606,4598
  have eq5433 : ∀ (X0 X1 X2 X3 : G) , ¬(old a (sF3 X2 X3 X1) a) ∨ ¬(old X0 a X1) ∨ (old b b X0) ∨ ¬(sP3 X2 X3 X1) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4652 -- forward demodulation 4652,4596
  have eq5434 (X0 X1 X2 X3 : G) : ¬(old X0 a X1) ∨ (old b b X0) ∨ ¬(sP3 X2 X3 X1) := resolve eq5433 rule_def_3_2 -- subsumption resolution 5433,156
  have eq5435 : ∀ (X0 X1 X2 X3 : G) , (old a a X0) ∨ ¬(old X0 a X1) ∨ ¬(sP3 X2 X3 X1) := Eq.mp (by simp only [eq4596, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5434 -- forward demodulation 5434,4596
  have eq5436 (X0 X1 X2 X3 : G) : ¬(sP3 X2 X3 X1) ∨ ¬(old X0 a X1) := resolve eq5435 eq4598 -- subsumption resolution 5435,4598
  have eq5700 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old X3 a X2) ∨ (old a a X3) ∨ ¬(sP1 X0 X1 X2) := resolve eq4600 eq286 -- resolution 4600,286
  have eq5724 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old X3 a X2) ∨ (old a a X3) := resolve eq5700 rfl -- duplicate literal removal 5700
  have eq5728 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ ¬(old X3 a X2) := resolve eq5724 eq4598 -- subsumption resolution 5724,4598
  have eq5945 : a ≠ sk1 ∨ c = sk0 ∨ c = sk1 := eq5309.imp_left (fun h : a = sk3 ↦ superpose h preserve_3) -- superposition 175,5309, 5309 into 175, unify on (0).2 in 5309 and (0).2 in 175
  have eq5966 : c = sk1 ∨ c = sk0 := resolve eq5945 eq5310 -- subsumption resolution 5945,5310
  have eq5979 : (sP3 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq5966.imp_left (fun h : c = sk1 ↦ superpose h eq618)) -- superposition 618,5966, 5966 into 618, unify on (0).2 in 5966 and (0).3 in 618
  have eq6000 : (old sk0 sk0 c) ∨ a = sk0 ∨ c = sk0 := resolve eq5979 eq206 -- subsumption resolution 5979,206
  have eq6001 : c = sk0 ∨ a = sk0 := resolve eq6000 p4XY -- subsumption resolution 6000,118
  have eq6048 : (old c sk1 sk2) ∨ a = c ∨ a = sk0 := Or.assoc2 (eq6001.imp_left (fun h : c = sk0 ↦ superpose h eq5403)) -- superposition 5403,6001, 6001 into 5403, unify on (0).2 in 6001 and (0).1 in 5403
  have eq6070 : a = c ∨ a = sk0 := resolve eq6048 p4YZ -- subsumption resolution 6048,120
  have eq6071 : a = sk0 := resolve eq6070 ac -- subsumption resolution 6070,115
  have eq6090 : (sP3 a sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq405 -- backward demodulation 405,6071
  have eq6121 : (old a a sk1) ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq790 -- backward demodulation 790,6071
  have eq6175 : (old sk3 a sk2) ∨ c = sk0 ∨ c = sk2 := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1357 -- backward demodulation 1357,6071
  have eq6455 : (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq6090 eq5417 -- subsumption resolution 6090,5417
  have eq6456 : (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6455 -- forward demodulation 6455,6071
  have eq6457 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6456 -- forward demodulation 6456,6071
  have eq6458 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6457 -- forward demodulation 6457,6071
  have eq6459 : (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6458 -- forward demodulation 6458,6071
  have eq6517 : c = sk0 ∨ c = sk1 := resolve eq6121 eq4598 -- subsumption resolution 6121,4598
  have eq6518 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6517 -- forward demodulation 6517,6071
  have eq6519 : c = sk1 := resolve eq6518 ac -- subsumption resolution 6518,115
  have eq6532 : (sP2 a c sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq6519, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6459 -- backward demodulation 6459,6519
  have eq6537 : (old a c sk2) ∨ (sP2 a c sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq6519, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6532 -- forward demodulation 6532,6519
  have eq6538 : (sP2 a c sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP3 a sk1 sk2) := resolve eq6537 p4XZ -- subsumption resolution 6537,119
  have eq6539 : (sP0 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq6519, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6538 -- forward demodulation 6538,6519
  have eq6540 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq6519, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6539 -- forward demodulation 6539,6519
  have eq6541 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) := Eq.mp (by simp only [eq6519, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6540 -- forward demodulation 6540,6519
  have eq6599 : a = c ∨ (old sk3 a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq6071, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6175 -- forward demodulation 6175,6071
  have eq6600 : (old sk3 a sk2) ∨ c = sk2 := resolve eq6599 ac -- subsumption resolution 6599,115
  have eq7318 (X0 : G) : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) ∨ ¬(old X0 a sk2) := resolve eq6541 eq5436 -- resolution 6541,5436
  have eq7321 (X0 : G) : ¬(old X0 a sk2) ∨ (sP2 a c sk2) ∨ (sP0 a c sk2) := resolve eq7318 eq5728 -- subsumption resolution 7318,5728
  have eq7346 : (sP2 a c sk2) ∨ (sP0 a c sk2) ∨ c = sk2 := resolve eq7321 eq6600 -- resolution 7321,6600
  have eq7348 : (sP2 a c sk2) ∨ c = sk2 := resolve eq7346 rule_def_0_2 -- subsumption resolution 7346,141
  have eq7349 : c = sk2 := resolve eq7348 rule_def_2_2 -- subsumption resolution 7348,150
  have eq7381 : (sP3 a c c) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) := Eq.mp (by simp only [eq7349, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6541 -- backward demodulation 6541,7349
  have eq7477 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) := resolve eq7381 eq206 -- subsumption resolution 7381,206
  have eq7478 : (sP1 a c c) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) := Eq.mp (by simp only [eq7349, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7477 -- forward demodulation 7477,7349
  have eq7479 : (sP0 a c sk2) ∨ (sP2 a c sk2) := resolve eq7478 eq192 -- subsumption resolution 7478,192
  have eq7480 : (sP0 a c c) ∨ (sP2 a c sk2) := Eq.mp (by simp only [eq7349, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7479 -- forward demodulation 7479,7349
  have eq7481 : (sP2 a c c) ∨ (sP0 a c c) := Eq.mp (by simp only [eq7349, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7480 -- forward demodulation 7480,7349
  have eq7560 : (sP0 a c c) ∨ a = c := resolve eq7481 rule_def_2_1 -- resolution 7481,149
  have eq7563 : (sP0 a c c) := resolve eq7560 ac -- subsumption resolution 7560,115
  have eq7564 : a = c := resolve eq7563 eq4599 -- resolution 7563,4599
  subsumption ac eq7564 -- subsumption resolution 7564,115

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_6_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_2 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X0 X1)) (old_6 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X2 X1 X3 ∨ ¬ old X4 X0 X1 ∨ old X0 X4 X1)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X2 X1 X3 ∨ ¬ new X4 X0 X1 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq201 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 159,132
  have eq219 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := resolve prev_0 preserve_0 -- resolution 170,176
  have eq240 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 154,132
  have eq417 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 169,176
  have eq418 : (sP4 sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) := resolve new_imp preserve_1 -- resolution 169,177
  have eq419 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) := resolve new_imp preserve_2 -- resolution 169,178
  have eq420 : (sP4 sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) := resolve new_imp preserve_3 -- resolution 169,179
  have eq471 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq201 rule_def_3_3 -- resolution 201,160
  have eq472 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq471 rfl -- duplicate literal removal 471
  have eq512 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq240 rule_def_2_4 -- resolution 240,155
  have eq515 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq512 rfl -- duplicate literal removal 512
  have eq661 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq417 rule_def_4_0 -- resolution 417,163
  have eq662 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq417 rule_def_4_1 -- resolution 417,164
  have eq671 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq661 rule_def_0_0 -- subsumption resolution 661,142
  have eq672 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq671 rule_def_1_0 -- subsumption resolution 671,146
  have eq673 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq662 rule_def_1_1 -- subsumption resolution 662,147
  have eq674 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq673 rule_def_3_1 -- subsumption resolution 673,158
  have eq677 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq672 rule_def_3_0 -- resolution 672,157
  have eq687 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq677 rule_def_2_0 -- subsumption resolution 677,151
  have eq691 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ a = sk1 := resolve eq418 rule_def_4_0 -- resolution 418,163
  have eq692 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ c = sk2 := resolve eq418 rule_def_4_1 -- resolution 418,164
  have eq701 : (sP2 sk1 sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ a = sk1 := resolve eq691 rule_def_0_0 -- subsumption resolution 691,142
  have eq702 : (sP3 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 := resolve eq701 rule_def_1_0 -- subsumption resolution 701,146
  have eq703 : (sP2 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP3 sk1 sk2 sk3) ∨ c = sk2 := resolve eq692 rule_def_1_1 -- subsumption resolution 692,147
  have eq704 : (sP2 sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq703 rule_def_3_1 -- subsumption resolution 703,158
  have eq722 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ a = sk2 := resolve eq419 rule_def_4_0 -- resolution 419,163
  have eq723 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ c = sk1 := resolve eq419 rule_def_4_1 -- resolution 419,164
  have eq732 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ a = sk2 := resolve eq722 rule_def_0_0 -- subsumption resolution 722,142
  have eq733 : (sP3 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ a = sk2 := resolve eq732 rule_def_1_0 -- subsumption resolution 732,146
  have eq734 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ c = sk1 := resolve eq723 rule_def_1_1 -- subsumption resolution 723,147
  have eq735 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq734 rule_def_3_1 -- subsumption resolution 734,158
  have eq754 : (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ c = sk0 := resolve eq420 rule_def_4_1 -- resolution 420,164
  have eq765 : (sP2 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ c = sk0 := resolve eq754 rule_def_1_1 -- subsumption resolution 754,147
  have eq766 : (sP2 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ c = sk0 := resolve eq765 rule_def_3_1 -- subsumption resolution 765,158
  have eq867 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq674 rule_def_2_2 -- resolution 674,153
  have eq868 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq674 rule_def_2_1 -- resolution 674,152
  have eq870 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq867 rule_def_0_2 -- subsumption resolution 867,144
  have eq997 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq868 rule_def_0_1 -- resolution 868,143
  have eq1050 : (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq702 rule_def_3_0 -- resolution 702,157
  have eq1056 : (old sk1 sk2 sk3) ∨ (sP2 sk1 sk2 sk3) ∨ a = sk1 ∨ a = b := resolve eq702 eq472 -- resolution 702,472
  have eq1060 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq1050 rule_def_2_0 -- subsumption resolution 1050,151
  have eq1062 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ a = b := resolve eq1056 eq515 -- subsumption resolution 1056,515
  have eq1197 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq704 rule_def_2_2 -- resolution 704,153
  have eq1198 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk2 := resolve eq704 rule_def_2_1 -- resolution 704,152
  have eq1200 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq1197 rule_def_0_2 -- subsumption resolution 1197,144
  have eq1274 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 := resolve eq1198 rule_def_0_1 -- resolution 1198,143
  have eq1327 : (old sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ a = sk2 ∨ b = sk2 := resolve eq733 rule_def_3_0 -- resolution 733,157
  have eq1337 : (old sk2 sk1 sk3) ∨ a = sk2 ∨ b = sk2 := resolve eq1327 rule_def_2_0 -- subsumption resolution 1327,151
  have eq1471 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ a = b := resolve eq735 eq515 -- resolution 735,515
  have eq1473 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq735 rule_def_2_2 -- resolution 735,153
  have eq1474 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ a = sk1 := resolve eq735 rule_def_2_1 -- resolution 735,152
  have eq1476 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq1473 rule_def_0_2 -- subsumption resolution 1473,144
  have eq1545 : (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq766 rule_def_2_2 -- resolution 766,153
  have eq1548 : (old sk4 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1545 rule_def_0_2 -- subsumption resolution 1545,144
  have eq1568 (X0 X1 : G) : ¬(old sk1 X0 X1) ∨ c = sk1 ∨ (old sk0 sk4 sk1) ∨ ¬(old X0 sk1 X1) ∨ c = sk0 ∨ ¬(old sk0 sk1 X0) := resolve eq1548 old_6 -- resolution 1548,130
  have eq1570 (X0 : G) : ¬(old X0 sk0 sk1) ∨ c = sk1 ∨ sk4 = X0 ∨ c = sk0 := resolve eq1548 old_8 -- resolution 1548,132
  have eq1721 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1474 rule_def_0_1 -- resolution 1474,143
  have eq7818 : c = sk1 ∨ (old sk0 sk4 sk1) ∨ ¬(old sk2 sk1 sk3) ∨ c = sk0 ∨ ¬(old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq1568 eq1060 -- resolution 1568,1060
  have eq7822 : c = sk1 ∨ (old sk0 sk4 sk1) ∨ ¬(old sk2 sk1 sk3) ∨ c = sk0 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq1568 eq1200 -- resolution 1568,1200
  have eq7848 : c = sk1 ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ ¬(old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq7818 eq1721 -- subsumption resolution 7818,1721
  have eq7849 : (old sk0 sk4 sk1) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk1 := resolve eq7848 eq997 -- subsumption resolution 7848,997
  have eq7854 : c = sk1 ∨ (old sk0 sk4 sk1) ∨ c = sk0 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq7822 eq1476 -- subsumption resolution 7822,1476
  have eq7855 : (old sk0 sk4 sk1) ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 := resolve eq7854 eq870 -- subsumption resolution 7854,870
  have eq7892 : c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ b = sk1 ∨ (new sk0 sk4 sk1) := resolve eq7849 imp_new_0 -- resolution 7849,140
  have eq7898 : b = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq7892 preserve_4 -- subsumption resolution 7892,180
  have eq8259 : a ≠ b ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq7898 trans_resol -- equality factoring 7898
  have eq8513 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ (new sk0 sk4 sk1) := resolve eq7855 imp_new_0 -- resolution 7855,140
  have eq8521 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq8513 preserve_4 -- subsumption resolution 8513,180
  have eq8551 : (old sk1 sk2 c) ∨ a = sk1 ∨ a = b ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq8521.imp_left (fun h : c = sk3 ↦ superpose h eq1062)) -- superposition 1062,8521, 8521 into 1062, unify on (0).2 in 8521 and (0).3 in 1062
  have eq8580 : (old sk1 sk2 c) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := Or.assoc4 (eq8521.imp_left (fun h : c = sk3 ↦ superpose h eq1274)) -- superposition 1274,8521, 8521 into 1274, unify on (0).2 in 8521 and (0).3 in 1274
  have eq8706 : (old sk1 sk2 c) ∨ c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq8580 rfl -- duplicate literal removal 8580
  have eq8732 : a = sk1 ∨ a = b ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq8551 p4XY -- subsumption resolution 8551,121
  have eq8733 : c = sk2 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq8732 eq8259 -- subsumption resolution 8732,8259
  have eq8739 : c = sk2 ∨ a = sk2 ∨ b = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq8706 p4XY -- subsumption resolution 8706,121
  have eq8809 : (sP3 c sk1 sk3) ∨ (old c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq8733.imp_left (fun h : c = sk2 ↦ superpose h eq733)) -- superposition 733,8733, 8733 into 733, unify on (0).2 in 8733 and (0).1 in 733
  have eq9073 : (sP3 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq8809 p4YZ -- subsumption resolution 8809,123
  have eq9074 : (sP3 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq9073 ac -- subsumption resolution 9073,118
  have eq9075 : (sP3 c sk1 sk3) ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq9074 rule_def_2_1 -- subsumption resolution 9074,152
  have eq9076 : c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq9075 rule_def_3_1 -- subsumption resolution 9075,158
  have eq9167 : (old c sk2 sk3) ∨ a = c ∨ c = b ∨ a = sk1 ∨ c = sk0 := Or.assoc3 (eq9076.imp_left (fun h : c = sk1 ↦ superpose h eq1060)) -- superposition 1060,9076, 9076 into 1060, unify on (0).2 in 9076 and (0).1 in 1060
  have eq9398 : a = c ∨ c = b ∨ a = sk1 ∨ c = sk0 := resolve eq9167 p4YZ -- subsumption resolution 9167,123
  have eq9399 : c = b ∨ a = sk1 ∨ c = sk0 := resolve eq9398 ac -- subsumption resolution 9398,118
  have eq9400 : a = sk1 ∨ c = sk0 := resolve eq9399 bc -- subsumption resolution 9399,119
  have eq9409 : ¬(new sk0 sk4 a) ∨ c = sk0 := eq9400.imp_left (fun h : a = sk1 ↦ superpose h preserve_4) -- superposition 180,9400, 9400 into 180, unify on (0).2 in 9400 and (0).3 in 180
  have eq9410 (X0 : G) : ¬(new sk0 a X0) ∨ sk2 = X0 ∨ c = sk0 := Or.assoc2 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq219)) -- superposition 219,9400, 9400 into 219, unify on (0).2 in 9400 and (0).2 in 219
  have eq9487 : (old sk0 a sk2) ∨ a = c ∨ c = sk2 ∨ c = sk0 := Or.assoc3 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq870)) -- superposition 870,9400, 9400 into 870, unify on (0).2 in 9400 and (0).2 in 870
  have eq9524 : (old sk2 a sk3) ∨ a = sk2 ∨ b = sk2 ∨ c = sk0 := Or.assoc3 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq1337)) -- superposition 1337,9400, 9400 into 1337, unify on (0).2 in 9400 and (0).2 in 1337
  have eq9553 : (sP0 sk2 a sk3) ∨ (old sk2 a sk3) ∨ a = c ∨ a = b ∨ c = sk0 := Or.assoc4 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq1471)) -- superposition 1471,9400, 9400 into 1471, unify on (0).2 in 9400 and (0).2 in 1471
  have eq9597 (X0 : G) : ¬(old X0 sk0 a) ∨ a = c ∨ sk4 = X0 ∨ c = sk0 ∨ c = sk0 := Or.assoc4 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq1570)) -- superposition 1570,9400, 9400 into 1570, unify on (0).2 in 9400 and (0).3 in 1570
  have eq9750 (X0 : G) : ¬(old X0 sk0 a) ∨ a = c ∨ sk4 = X0 ∨ c = sk0 := resolve eq9597 rfl -- duplicate literal removal 9597
  have eq9787 : (old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq9487 ac -- subsumption resolution 9487,118
  have eq9808 : (sP0 sk2 a sk3) ∨ (old sk2 a sk3) ∨ a = b ∨ c = sk0 := resolve eq9553 ac -- subsumption resolution 9553,118
  have eq9809 : (old sk2 a sk3) ∨ a = b ∨ c = sk0 := resolve eq9808 rule_def_0_1 -- subsumption resolution 9808,143
  have eq9828 (X0 : G) : ¬(old X0 sk0 a) ∨ sk4 = X0 ∨ c = sk0 := resolve eq9750 ac -- subsumption resolution 9750,118
  have eq10290 : (old sk2 a c) ∨ a = b ∨ c = sk0 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq8521.imp_left (fun h : c = sk3 ↦ superpose h eq9809)) -- superposition 9809,8521, 8521 into 9809, unify on (0).2 in 8521 and (0).3 in 9809
  have eq10291 : (old sk2 a c) ∨ a = b ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq10290 rfl -- duplicate literal removal 10290
  have eq10296 : c = sk2 ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq10291 p4XY -- subsumption resolution 10291,121
  have eq11784 : (sP3 c sk1 sk3) ∨ (old c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ a = c ∨ c = sk0 ∨ a = b ∨ c = sk1 := Or.assoc4 (eq10296.imp_left (fun h : c = sk2 ↦ superpose h eq733)) -- superposition 733,10296, 10296 into 733, unify on (0).2 in 10296 and (0).1 in 733
  have eq12100 : (sP3 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ a = c ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq11784 p4YZ -- subsumption resolution 11784,123
  have eq12101 : (sP3 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq12100 ac -- subsumption resolution 12100,118
  have eq12102 : (sP2 c sk1 sk3) ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq12101 eq472 -- subsumption resolution 12101,472
  have eq12103 : c = sk1 ∨ a = b ∨ c = sk0 := resolve eq12102 eq515 -- subsumption resolution 12102,515
  have eq12109 : a = c ∨ a = b ∨ c = sk0 ∨ c = sk0 := Or.assoc3 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq12103)) -- superposition 12103,9400, 9400 into 12103, unify on (0).2 in 9400 and (0).2 in 12103
  have eq12470 : a = c ∨ a = b ∨ c = sk0 := resolve eq12109 rfl -- duplicate literal removal 12109
  have eq12476 : c = sk0 ∨ a = b := resolve eq12470 ac -- subsumption resolution 12470,118
  have eq12505 : (sP3 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ a = c ∨ a = b := Or.assoc4 (eq12476.imp_left (fun h : c = sk0 ↦ superpose h eq672)) -- superposition 672,12476, 12476 into 672, unify on (0).2 in 12476 and (0).1 in 672
  have eq12690 : (sP3 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ a = c ∨ a = b := resolve eq12505 p4YZ -- subsumption resolution 12505,123
  have eq12691 : (sP3 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ a = b := resolve eq12690 ac -- subsumption resolution 12690,118
  have eq12692 : (sP2 c sk1 sk2) ∨ a = b := resolve eq12691 eq472 -- subsumption resolution 12691,472
  have eq12693 : a = b := resolve eq12692 eq515 -- subsumption resolution 12692,515
  have eq12864 : a = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq12693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq687 -- backward demodulation 687,12693
  have eq14646 : a = sk2 ∨ c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq12693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8739 -- backward demodulation 8739,12693
  have eq14685 : a = sk2 ∨ (old sk2 a sk3) ∨ a = sk2 ∨ c = sk0 := Eq.mp (by simp only [eq12693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9524 -- backward demodulation 9524,12693
  have eq14818 : (old sk2 a sk3) ∨ a = sk2 ∨ c = sk0 := resolve eq14685 rfl -- duplicate literal removal 14685
  have eq14836 : c = sk2 ∨ a = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq14646 rfl -- duplicate literal removal 14646
  have eq15145 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq12864 rfl -- duplicate literal removal 12864
  have eq16963 : (old c a sk3) ∨ a = c ∨ c = sk0 ∨ a = sk2 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq14836.imp_left (fun h : c = sk2 ↦ superpose h eq14818)) -- superposition 14818,14836, 14836 into 14818, unify on (0).2 in 14836 and (0).1 in 14818
  have eq16981 : (old c a sk3) ∨ a = c ∨ c = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq16963 rfl -- duplicate literal removal 16963
  have eq17029 : a = c ∨ c = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq16981 p4YZ -- subsumption resolution 16981,123
  have eq17030 : a = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq17029 ac -- subsumption resolution 17029,118
  have eq17033 : (new sk0 sk1 a) ∨ c = sk0 ∨ c = sk1 := eq17030.imp_left (fun h : a = sk2 ↦ superpose h preserve_0) -- superposition 176,17030, 17030 into 176, unify on (0).2 in 17030 and (0).3 in 176
  have eq17296 : (new sk0 a a) ∨ c = sk0 ∨ a = c ∨ c = sk0 := Or.assoc3 (eq9400.imp_left (fun h : a = sk1 ↦ superpose h eq17033)) -- superposition 17033,9400, 9400 into 17033, unify on (0).2 in 9400 and (0).2 in 17033
  have eq17297 : (new sk0 a a) ∨ c = sk0 ∨ a = c := resolve eq17296 rfl -- duplicate literal removal 17296
  have eq17298 : (new sk0 a a) ∨ c = sk0 := resolve eq17297 ac -- subsumption resolution 17297,118
  have eq17311 : c = sk0 ∨ a = sk2 ∨ c = sk0 := resolve eq17298 eq9410 -- resolution 17298,9410
  have eq17319 : a = sk2 ∨ c = sk0 := resolve eq17311 rfl -- duplicate literal removal 17311
  have eq17415 : (old sk0 a a) ∨ a = c ∨ c = sk0 ∨ c = sk0 := Or.assoc3 (eq17319.imp_left (fun h : a = sk2 ↦ superpose h eq9787)) -- superposition 9787,17319, 17319 into 9787, unify on (0).2 in 17319 and (0).3 in 9787
  have eq17432 : (old sk0 a a) ∨ a = c ∨ c = sk0 := resolve eq17415 rfl -- duplicate literal removal 17415
  have eq17467 : (old sk0 a a) ∨ c = sk0 := resolve eq17432 ac -- subsumption resolution 17432,118
  have eq17646 : (old a sk0 a) ∨ c = sk0 := resolve eq17467 old_2 -- resolution 17467,126
  have eq17803 : c = sk0 ∨ a = sk4 ∨ c = sk0 := resolve eq17646 eq9828 -- resolution 17646,9828
  have eq17821 : a = sk4 ∨ c = sk0 := resolve eq17803 rfl -- duplicate literal removal 17803
  have eq17862 : ¬(new sk0 a a) ∨ c = sk0 ∨ c = sk0 := Or.assoc2 (eq17821.imp_left (fun h : a = sk4 ↦ superpose h eq9409)) -- superposition 9409,17821, 17821 into 9409, unify on (0).2 in 17821 and (0).2 in 9409
  have eq17872 : ¬(new sk0 a a) ∨ c = sk0 := resolve eq17862 rfl -- duplicate literal removal 17862
  have eq17890 : c = sk0 := resolve eq17872 eq17298 -- subsumption resolution 17872,17298
  have eq18394 : (old c sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq17890, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15145 -- backward demodulation 15145,17890
  have eq19085 : a = sk0 := resolve eq18394 p4YZ -- subsumption resolution 18394,123
  have eq19086 : a = c := Eq.mp (by simp only [eq19085, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq17890 -- backward demodulation 17890,19085
  subsumption ac eq19086 -- subsumption resolution 19086,118

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_7_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X1 X3 X4 ∨ new X1 X4 X0)) (prev_4 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X4 ∨ ¬ new X3 X1 X2 ∨ new X0 X3 X4)) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X0 ∨ ¬ new X1 X3 X0 ∨ ¬ new X4 X1 X3 ∨ new X1 X2 X4) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq343 (X0 X1 : G) : ¬(new sk0 X0 X1) ∨ (new X0 sk0 X1) ∨ ¬(new X0 sk3 sk0) := resolve prev_4 preserve_1 -- resolution 176,180
  have eq444 : (new sk1 sk0 sk2) ∨ ¬(new sk1 sk3 sk0) := resolve eq343 preserve_0 -- resolution 343,179
  have eq448 : (new sk1 sk0 sk2) := resolve eq444 preserve_2 -- subsumption resolution 444,181
  have eq452 (X0 X1 : G) : ¬(new sk1 X1 sk0) ∨ (new sk1 sk2 X0) ∨ ¬(new X0 sk1 X1) := resolve eq448 prev_1 -- resolution 448,173
  have eq514 (X0 : G) : ¬(new X0 sk1 sk3) ∨ (new sk1 sk2 X0) := resolve eq452 preserve_2 -- resolution 452,181
  have eq515 : (new sk1 sk2 sk4) := resolve eq514 preserve_3 -- resolution 514,182
  subsumption preserve_4 eq515 -- subsumption resolution 515,183

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_8_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X3 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq203 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 161,134
  have eq238 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 156,134
  have eq442 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 171,180
  have eq443 : (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 171,181
  have eq474 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq203 rule_def_3_3 -- resolution 203,162
  have eq475 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq474 rfl -- duplicate literal removal 474
  have eq543 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq238 rule_def_2_4 -- resolution 238,157
  have eq546 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq543 rfl -- duplicate literal removal 543
  have eq650 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq442 rule_def_4_0 -- resolution 442,165
  have eq651 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq442 rule_def_4_1 -- resolution 442,166
  have eq660 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq650 rule_def_0_0 -- subsumption resolution 650,144
  have eq661 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq660 rule_def_1_0 -- subsumption resolution 660,148
  have eq662 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq651 rule_def_1_1 -- subsumption resolution 651,149
  have eq663 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq662 rule_def_3_1 -- subsumption resolution 662,160
  have eq666 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq661 rule_def_3_0 -- resolution 661,159
  have eq672 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq661 eq475 -- resolution 661,475
  have eq676 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq666 rule_def_2_0 -- subsumption resolution 666,153
  have eq678 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq672 eq546 -- subsumption resolution 672,546
  have eq680 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ a = sk3 := resolve eq443 rule_def_4_0 -- resolution 443,165
  have eq690 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ a = sk3 := resolve eq680 rule_def_0_0 -- subsumption resolution 680,144
  have eq691 : (sP3 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 := resolve eq690 rule_def_1_0 -- subsumption resolution 690,148
  have eq826 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq663 rule_def_2_2 -- resolution 663,155
  have eq829 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq826 rule_def_0_2 -- subsumption resolution 826,146
  have eq842 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 := resolve eq829 old_8 -- resolution 829,134
  have eq1005 : (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq691 rule_def_3_0 -- resolution 691,159
  have eq1011 : (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ a = sk3 ∨ a = b := resolve eq691 eq475 -- resolution 691,475
  have eq1015 : (old sk3 sk1 sk2) ∨ a = sk3 ∨ b = sk3 := resolve eq1005 rule_def_2_0 -- subsumption resolution 1005,153
  have eq1017 : (old sk3 sk1 sk2) ∨ a = sk3 ∨ a = b := resolve eq1011 eq546 -- subsumption resolution 1011,546
  have eq1020 : a = sk3 ∨ b = sk3 ∨ c = sk2 ∨ sk0 = sk3 ∨ c = sk1 := resolve eq1015 eq842 -- resolution 1015,842
  have eq1038 : b = sk3 ∨ a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1020 preserve_2 -- subsumption resolution 1020,182
  have eq1042 : a = sk3 ∨ a = b ∨ c = sk2 ∨ sk0 = sk3 ∨ c = sk1 := resolve eq1017 eq842 -- resolution 1017,842
  have eq1061 : a = sk3 ∨ a = b ∨ c = sk2 ∨ c = sk1 := resolve eq1042 preserve_2 -- subsumption resolution 1042,182
  have eq1119 : a ≠ b ∨ a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1038 trans_resol -- equality factoring 1038
  have eq1127 : a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq1119 eq1061 -- subsumption resolution 1119,1061
  have eq1130 : a ≠ sk0 ∨ c = sk2 ∨ c = sk1 := eq1127.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 182,1127, 1127 into 182, unify on (0).2 in 1127 and (0).2 in 182
  have eq1136 : (sP4 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := Or.assoc6 (eq1127.imp_left (fun h : a = sk3 ↦ superpose h eq443)) -- superposition 443,1127, 1127 into 443, unify on (0).2 in 1127 and (0).1 in 443
  have eq1140 : (sP4 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1136 rule_def_0_2 -- subsumption resolution 1136,146
  have eq1141 : (sP4 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1140 rule_def_1_1 -- subsumption resolution 1140,149
  have eq1142 : (sP4 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1141 rule_def_2_2 -- subsumption resolution 1141,155
  have eq1143 : (sP4 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1142 rule_def_3_1 -- subsumption resolution 1142,160
  have eq1144 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1143 rule_def_4_1 -- subsumption resolution 1143,166
  have eq1153 : c = sk2 ∨ c = sk1 ∨ c = sk2 ∨ a = sk0 ∨ c = sk1 := resolve eq1144 eq842 -- resolution 1144,842
  have eq1173 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq1153 rfl -- duplicate literal removal 1153
  have eq1174 : c = sk2 ∨ c = sk1 := resolve eq1173 eq1130 -- subsumption resolution 1173,1130
  have eq1192 : (old sk0 sk1 c) ∨ a = sk0 ∨ b = sk0 ∨ c = sk1 := Or.assoc3 (eq1174.imp_left (fun h : c = sk2 ↦ superpose h eq676)) -- superposition 676,1174, 1174 into 676, unify on (0).2 in 1174 and (0).3 in 676
  have eq1193 : (old sk0 sk1 c) ∨ a = sk0 ∨ a = b ∨ c = sk1 := Or.assoc3 (eq1174.imp_left (fun h : c = sk2 ↦ superpose h eq678)) -- superposition 678,1174, 1174 into 678, unify on (0).2 in 1174 and (0).3 in 678
  have eq1204 : (old sk3 sk1 c) ∨ a = sk3 ∨ b = sk3 ∨ c = sk1 := Or.assoc3 (eq1174.imp_left (fun h : c = sk2 ↦ superpose h eq1015)) -- superposition 1015,1174, 1174 into 1015, unify on (0).2 in 1174 and (0).3 in 1015
  have eq1205 : (old sk3 sk1 c) ∨ a = sk3 ∨ a = b ∨ c = sk1 := Or.assoc3 (eq1174.imp_left (fun h : c = sk2 ↦ superpose h eq1017)) -- superposition 1017,1174, 1174 into 1017, unify on (0).2 in 1174 and (0).3 in 1017
  have eq1226 : c = sk1 ∨ b = sk0 ∨ a = sk0 := resolve eq1192 p4XY -- subsumption resolution 1192,123
  have eq1227 : c = sk1 ∨ a = b ∨ a = sk0 := resolve eq1193 p4XY -- subsumption resolution 1193,123
  have eq1237 : b = sk3 ∨ a = sk3 ∨ c = sk1 := resolve eq1204 p4XY -- subsumption resolution 1204,123
  have eq1238 : a = sk3 ∨ a = b ∨ c = sk1 := resolve eq1205 p4XY -- subsumption resolution 1205,123
  have eq1274 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := Or.assoc6 (eq1226.imp_left (fun h : c = sk1 ↦ superpose h eq442)) -- superposition 442,1226, 1226 into 442, unify on (0).2 in 1226 and (0).2 in 442
  have eq1295 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1274 p4XZ -- subsumption resolution 1274,124
  have eq1296 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1295 rule_def_0_0 -- subsumption resolution 1295,144
  have eq1297 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1296 rule_def_1_0 -- subsumption resolution 1296,148
  have eq1298 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1297 rule_def_4_0 -- subsumption resolution 1297,165
  have eq1299 : (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 := resolve eq1298 rule_def_2_0 -- subsumption resolution 1298,153
  have eq1300 : b = sk0 ∨ a = sk0 := resolve eq1299 rule_def_3_0 -- subsumption resolution 1299,159
  have eq1328 : a ≠ b ∨ a = sk0 := resolve eq1300 trans_resol -- equality factoring 1300
  have eq1361 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := Or.assoc6 (eq1227.imp_left (fun h : c = sk1 ↦ superpose h eq442)) -- superposition 442,1227, 1227 into 442, unify on (0).2 in 1227 and (0).2 in 442
  have eq1397 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1361 p4XZ -- subsumption resolution 1361,124
  have eq1398 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1397 rule_def_0_0 -- subsumption resolution 1397,144
  have eq1399 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1398 rule_def_1_0 -- subsumption resolution 1398,148
  have eq1400 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1399 rule_def_4_0 -- subsumption resolution 1399,165
  have eq1401 : (sP2 sk0 c sk2) ∨ a = b ∨ a = sk0 := resolve eq1400 eq475 -- subsumption resolution 1400,475
  have eq1402 : a = b ∨ a = sk0 := resolve eq1401 eq546 -- subsumption resolution 1401,546
  have eq1403 : a = sk0 := resolve eq1402 eq1328 -- subsumption resolution 1402,1328
  have eq1405 : a ≠ sk3 := Eq.mp (by simp only [eq1403, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 182,1403
  have eq1777 : a ≠ b ∨ a = sk3 ∨ c = sk1 := eq1237.imp_left (fun h : b = sk3 ↦ superpose h eq1405) -- superposition 1405,1237, 1237 into 1405, unify on (0).2 in 1237 and (0).2 in 1405
  have eq1795 : a ≠ b ∨ c = sk1 := resolve eq1777 eq1405 -- subsumption resolution 1777,1405
  have eq1872 : a ≠ a ∨ a = b ∨ c = sk1 := eq1238.imp_left (fun h : a = sk3 ↦ superpose h eq1405) -- superposition 1405,1238, 1238 into 1405, unify on (0).2 in 1238 and (0).2 in 1405
  have eq1873 : a = b ∨ c = sk1 := resolve eq1872 rfl -- trivial inequality removal 1872
  have eq1877 : c = sk1 := resolve eq1873 eq1795 -- subsumption resolution 1873,1795
  have eq1920 : (old sk3 c sk2) ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq1877, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1015 -- backward demodulation 1015,1877
  have eq1922 : (old sk3 c sk2) ∨ a = sk3 ∨ a = b := Eq.mp (by simp only [eq1877, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1017 -- backward demodulation 1017,1877
  have eq2083 : a = sk3 ∨ b = sk3 := resolve eq1920 p4XZ -- subsumption resolution 1920,124
  have eq2084 : b = sk3 := resolve eq2083 eq1405 -- subsumption resolution 2083,1405
  have eq2205 : a = sk3 ∨ a = b := resolve eq1922 p4XZ -- subsumption resolution 1922,124
  have eq2206 : a = b := resolve eq2205 eq1405 -- subsumption resolution 2205,1405
  have eq2369 : a = sk3 := Eq.mp (by simp only [eq2206, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2084 -- backward demodulation 2084,2206
  subsumption eq1405 eq2369 -- subsumption resolution 2369,1405

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_9_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_9 : (∀ X0 X1 X2, ¬ old X0 X1 X0 ∨ ¬ old X0 X2 X0 ∨ ¬ old X2 X0 X1 ∨ X1 = X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X1 X0 ∨ ¬ new X0 X2 X0 ∨ ¬ new X2 X0 X1 ∨ X1 = X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq208 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 164,137
  have eq254 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 159,137
  have eq458 : (sP4 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 174,184
  have eq459 : (sP4 sk0 sk2 sk0) ∨ (sP2 sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP3 sk0 sk2 sk0) := resolve new_imp preserve_1 -- resolution 174,185
  have eq460 : (sP4 sk2 sk0 sk1) ∨ (sP2 sk2 sk0 sk1) ∨ (sP1 sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP3 sk2 sk0 sk1) := resolve new_imp preserve_2 -- resolution 174,186
  have eq509 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq208 rule_def_3_3 -- resolution 208,165
  have eq510 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq509 rfl -- duplicate literal removal 509
  have eq578 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq254 rule_def_2_4 -- resolution 254,160
  have eq581 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq578 rfl -- duplicate literal removal 578
  have eq748 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq458 rule_def_4_0 -- resolution 458,168
  have eq749 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq458 rule_def_4_1 -- resolution 458,169
  have eq758 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq748 rule_def_0_0 -- subsumption resolution 748,147
  have eq759 : (sP3 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 := resolve eq758 rule_def_1_0 -- subsumption resolution 758,151
  have eq760 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq749 rule_def_1_1 -- subsumption resolution 749,152
  have eq761 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq760 rule_def_3_1 -- subsumption resolution 760,163
  have eq765 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq759 rule_def_3_0 -- resolution 759,162
  have eq771 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ a = b := resolve eq759 eq510 -- resolution 759,510
  have eq775 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq765 rule_def_2_0 -- subsumption resolution 765,156
  have eq777 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ a = b := resolve eq771 eq581 -- subsumption resolution 771,581
  have eq780 : (sP2 sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP3 sk0 sk2 sk0) ∨ c = sk2 := resolve eq459 rule_def_4_1 -- resolution 459,169
  have eq791 : (sP2 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP3 sk0 sk2 sk0) ∨ c = sk2 := resolve eq780 rule_def_1_1 -- subsumption resolution 780,152
  have eq792 : (sP2 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ c = sk2 := resolve eq791 rule_def_3_1 -- subsumption resolution 791,163
  have eq812 : (sP2 sk2 sk0 sk1) ∨ (sP1 sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP3 sk2 sk0 sk1) ∨ a = sk2 := resolve eq460 rule_def_4_0 -- resolution 460,168
  have eq813 : (sP2 sk2 sk0 sk1) ∨ (sP1 sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP3 sk2 sk0 sk1) ∨ c = sk0 := resolve eq460 rule_def_4_1 -- resolution 460,169
  have eq822 : (sP2 sk2 sk0 sk1) ∨ (sP1 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP3 sk2 sk0 sk1) ∨ a = sk2 := resolve eq812 rule_def_0_0 -- subsumption resolution 812,147
  have eq823 : (sP3 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP2 sk2 sk0 sk1) ∨ a = sk2 := resolve eq822 rule_def_1_0 -- subsumption resolution 822,151
  have eq824 : (sP2 sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ (sP3 sk2 sk0 sk1) ∨ c = sk0 := resolve eq813 rule_def_1_1 -- subsumption resolution 813,152
  have eq825 : (sP2 sk2 sk0 sk1) ∨ (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ c = sk0 := resolve eq824 rule_def_3_1 -- subsumption resolution 824,163
  have eq987 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq761 rule_def_2_2 -- resolution 761,158
  have eq990 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq987 rule_def_0_2 -- subsumption resolution 987,149
  have eq1315 : (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ c = sk2 ∨ c = sk0 := resolve eq792 rule_def_2_2 -- resolution 792,158
  have eq1318 : (old sk0 sk2 sk0) ∨ c = sk2 ∨ c = sk0 := resolve eq1315 rule_def_0_2 -- subsumption resolution 1315,149
  have eq1448 : (old sk2 sk0 sk1) ∨ (sP2 sk2 sk0 sk1) ∨ a = sk2 ∨ b = sk2 := resolve eq823 rule_def_3_0 -- resolution 823,162
  have eq1458 : (old sk2 sk0 sk1) ∨ a = sk2 ∨ b = sk2 := resolve eq1448 rule_def_2_0 -- subsumption resolution 1448,156
  have eq1532 : (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq825 eq581 -- resolution 825,581
  have eq1534 : (sP0 sk2 sk0 sk1) ∨ (old sk2 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq825 rule_def_2_2 -- resolution 825,158
  have eq1537 : (old sk2 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1534 rule_def_0_2 -- subsumption resolution 1534,149
  have eq1548 : c = sk0 ∨ c = sk1 ∨ sk1 = sk2 ∨ ¬(old sk0 sk2 sk0) ∨ ¬(old sk0 sk1 sk0) := resolve eq1537 old_9 -- resolution 1537,138
  have eq1556 : c = sk0 ∨ c = sk1 ∨ ¬(old sk0 sk2 sk0) ∨ ¬(old sk0 sk1 sk0) := resolve eq1548 preserve_3 -- subsumption resolution 1548,187
  have eq1557 : ¬(old sk0 sk2 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq1556 eq990 -- subsumption resolution 1556,990
  have eq1565 : c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 := resolve eq1557 eq1318 -- resolution 1557,1318
  have eq1569 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1565 rfl -- duplicate literal removal 1565
  have eq1585 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (old c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := Or.assoc6 (eq1569.imp_left (fun h : c = sk2 ↦ superpose h eq460)) -- superposition 460,1569, 1569 into 460, unify on (0).2 in 1569 and (0).1 in 460
  have eq1615 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1585 p4YZ -- subsumption resolution 1585,128
  have eq1616 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1615 rule_def_0_2 -- subsumption resolution 1615,149
  have eq1617 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1616 rule_def_1_1 -- subsumption resolution 1616,152
  have eq1618 : (sP4 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1617 rule_def_2_2 -- subsumption resolution 1617,158
  have eq1619 : (sP4 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1618 rule_def_3_1 -- subsumption resolution 1618,163
  have eq1620 : c = sk1 ∨ c = sk0 := resolve eq1619 rule_def_4_1 -- subsumption resolution 1619,169
  have eq1644 : (old sk0 c sk0) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq1620.imp_left (fun h : c = sk1 ↦ superpose h eq775)) -- superposition 775,1620, 1620 into 775, unify on (0).2 in 1620 and (0).2 in 775
  have eq1645 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 := Or.assoc3 (eq1620.imp_left (fun h : c = sk1 ↦ superpose h eq777)) -- superposition 777,1620, 1620 into 777, unify on (0).2 in 1620 and (0).2 in 777
  have eq1670 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq1644 p4XZ -- subsumption resolution 1644,127
  have eq1671 : a = sk0 ∨ a = b ∨ c = sk0 := resolve eq1645 p4XZ -- subsumption resolution 1645,127
  have eq1814 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq1670 trans_resol -- equality factoring 1670
  have eq1834 : c = sk0 ∨ a = sk0 := resolve eq1814 eq1671 -- subsumption resolution 1814,1671
  have eq1887 : (old c sk1 c) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq1834.imp_left (fun h : c = sk0 ↦ superpose h eq775)) -- superposition 775,1834, 1834 into 775, unify on (0).2 in 1834 and (0).1 in 775
  have eq1937 : a = c ∨ c = b ∨ a = sk0 := resolve eq1887 p4YZ -- subsumption resolution 1887,128
  have eq1938 : c = b ∨ a = sk0 := resolve eq1937 ac -- subsumption resolution 1937,123
  have eq1939 : a = sk0 := resolve eq1938 bc -- subsumption resolution 1938,124
  have eq2206 : (old a sk2 a) ∨ c = sk2 ∨ c = sk0 := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1318 -- backward demodulation 1318,1939
  have eq2272 : (old sk2 a sk1) ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1458 -- backward demodulation 1458,1939
  have eq2316 : (sP0 sk2 a sk1) ∨ (old sk2 sk0 sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1532 -- backward demodulation 1532,1939
  have eq2349 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1620 -- backward demodulation 1620,1939
  have eq2777 : a = c ∨ (old a sk2 a) ∨ c = sk2 := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2206 -- forward demodulation 2206,1939
  have eq2778 : (old a sk2 a) ∨ c = sk2 := resolve eq2777 ac -- subsumption resolution 2777,123
  have eq2954 : (old sk2 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq2316 rule_def_0_1 -- subsumption resolution 2316,148
  have eq2955 : (old sk2 a sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2954 -- forward demodulation 2954,1939
  have eq2956 : a = c ∨ (old sk2 a sk1) ∨ a = b := Eq.mp (by simp only [eq1939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2955 -- forward demodulation 2955,1939
  have eq2957 : (old sk2 a sk1) ∨ a = b := resolve eq2956 ac -- subsumption resolution 2956,123
  have eq3049 : c = sk1 := resolve eq2349 ac -- subsumption resolution 2349,123
  have eq3074 : (old sk2 a c) ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq3049, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2272 -- backward demodulation 2272,3049
  have eq3158 : (old sk2 a c) ∨ a = b := Eq.mp (by simp only [eq3049, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2957 -- backward demodulation 2957,3049
  have eq3172 : a = sk2 ∨ b = sk2 := resolve eq3074 p4XY -- subsumption resolution 3074,126
  have eq3313 : a = b := resolve eq3158 p4XY -- subsumption resolution 3158,126
  have eq3315 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq3313, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 125,3313
  have eq3501 : a = sk2 ∨ a = sk2 := Eq.mp (by simp only [eq3313, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3172 -- backward demodulation 3172,3313
  have eq3521 : a = sk2 := resolve eq3501 rfl -- duplicate literal removal 3501
  have eq3630 : a = c ∨ (old a sk2 a) := Eq.mp (by simp only [eq3521, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2778 -- backward demodulation 2778,3521
  have eq3695 : (old a sk2 a) := resolve eq3630 ac -- subsumption resolution 3630,123
  have eq3696 : (old a a a) := Eq.mp (by simp only [eq3521, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3695 -- forward demodulation 3695,3521
  subsumption eq3315 eq3696 -- subsumption resolution 3696,3315

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_10_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_10 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X0 ∨ ¬ old X2 X0 X3 ∨ ¬ old X3 X0 X1 ∨ old X0 X0 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X0 ∨ ¬ new X2 X0 X3 ∨ ¬ new X3 X0 X1 ∨ new X0 X0 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq211 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 166,139
  have eq217 (X0 X1 : G) : ¬(sP3 X0 X1 a) := resolve rule_def_3_4 p3 -- resolution 168,127
  have eq256 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 161,139
  have eq477 : (sP4 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 176,187
  have eq478 : (sP4 sk2 sk0 sk3) ∨ (sP2 sk2 sk0 sk3) ∨ (sP1 sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP3 sk2 sk0 sk3) := resolve new_imp preserve_1 -- resolution 176,188
  have eq479 : (sP4 sk3 sk0 sk1) ∨ (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) := resolve new_imp preserve_2 -- resolution 176,189
  have eq526 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq211 rule_def_3_3 -- resolution 211,167
  have eq527 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq526 rfl -- duplicate literal removal 526
  have eq598 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq256 rule_def_2_4 -- resolution 256,162
  have eq601 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq598 rfl -- duplicate literal removal 598
  have eq769 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq477 rule_def_4_0 -- resolution 477,170
  have eq770 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq477 rule_def_4_1 -- resolution 477,171
  have eq780 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq769 rule_def_0_0 -- subsumption resolution 769,149
  have eq781 : (sP3 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 := resolve eq780 rule_def_1_0 -- subsumption resolution 780,153
  have eq782 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq770 rule_def_1_1 -- subsumption resolution 770,154
  have eq783 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq782 rule_def_3_1 -- subsumption resolution 782,165
  have eq787 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq781 rule_def_3_0 -- resolution 781,164
  have eq793 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ a = b := resolve eq781 eq527 -- resolution 781,527
  have eq797 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq787 rule_def_2_0 -- subsumption resolution 787,158
  have eq799 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ a = b := resolve eq793 eq601 -- subsumption resolution 793,601
  have eq802 : (sP2 sk2 sk0 sk3) ∨ (sP1 sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP3 sk2 sk0 sk3) ∨ c = sk0 := resolve eq478 rule_def_4_1 -- resolution 478,171
  have eq814 : (sP2 sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP3 sk2 sk0 sk3) ∨ c = sk0 := resolve eq802 rule_def_1_1 -- subsumption resolution 802,154
  have eq815 : (sP2 sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ c = sk0 := resolve eq814 rule_def_3_1 -- subsumption resolution 814,165
  have eq836 : (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq479 rule_def_4_1 -- resolution 479,171
  have eq848 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq836 rule_def_1_1 -- subsumption resolution 836,154
  have eq849 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 := resolve eq848 rule_def_3_1 -- subsumption resolution 848,165
  have eq1014 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq783 rule_def_2_2 -- resolution 783,160
  have eq1017 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq1014 rule_def_0_2 -- subsumption resolution 1014,151
  have eq1330 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq815 rule_def_2_2 -- resolution 815,160
  have eq1333 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq1330 rule_def_0_2 -- subsumption resolution 1330,151
  have eq1575 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq849 eq601 -- resolution 849,601
  have eq1577 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq849 rule_def_2_2 -- resolution 849,160
  have eq1580 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1577 rule_def_0_2 -- subsumption resolution 1577,151
  have eq1593 (X0 : G) : c = sk0 ∨ c = sk1 ∨ (old sk0 sk0 X0) ∨ ¬(old X0 sk0 sk3) ∨ ¬(old sk0 sk1 sk0) := resolve eq1580 old_10 -- resolution 1580,141
  have eq1601 (X0 : G) : ¬(old X0 sk0 sk3) ∨ c = sk1 ∨ (old sk0 sk0 X0) ∨ c = sk0 := resolve eq1593 eq1017 -- subsumption resolution 1593,1017
  have eq1792 : c = sk1 ∨ (old sk0 sk0 sk2) ∨ c = sk0 ∨ c = sk0 ∨ c = sk3 := resolve eq1601 eq1333 -- resolution 1601,1333
  have eq1799 : (old sk0 sk0 sk2) ∨ c = sk1 ∨ c = sk0 ∨ c = sk3 := resolve eq1792 rfl -- duplicate literal removal 1792
  have eq1820 : c = sk1 ∨ c = sk0 ∨ c = sk3 ∨ (new sk0 sk0 sk2) := resolve eq1799 imp_new_0 -- resolution 1799,147
  have eq1821 : c = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq1820 preserve_3 -- subsumption resolution 1820,190
  have eq1833 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (old c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := Or.assoc6 (eq1821.imp_left (fun h : c = sk3 ↦ superpose h eq479)) -- superposition 479,1821, 1821 into 479, unify on (0).2 in 1821 and (0).1 in 479
  have eq1901 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1833 p4YZ -- subsumption resolution 1833,130
  have eq1902 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1901 rule_def_0_2 -- subsumption resolution 1901,151
  have eq1903 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1902 rule_def_1_1 -- subsumption resolution 1902,154
  have eq1904 : (sP4 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1903 rule_def_2_2 -- subsumption resolution 1903,160
  have eq1905 : (sP4 c sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1904 rule_def_3_1 -- subsumption resolution 1904,165
  have eq1906 : c = sk1 ∨ c = sk0 := resolve eq1905 rule_def_4_1 -- subsumption resolution 1905,171
  have eq1919 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 := Or.assoc6 (eq1906.imp_left (fun h : c = sk1 ↦ superpose h eq477)) -- superposition 477,1906, 1906 into 477, unify on (0).2 in 1906 and (0).2 in 477
  have eq1927 : (old sk0 c sk0) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq1906.imp_left (fun h : c = sk1 ↦ superpose h eq797)) -- superposition 797,1906, 1906 into 797, unify on (0).2 in 1906 and (0).2 in 797
  have eq1928 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 := Or.assoc3 (eq1906.imp_left (fun h : c = sk1 ↦ superpose h eq799)) -- superposition 799,1906, 1906 into 799, unify on (0).2 in 1906 and (0).2 in 799
  have eq1958 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 := resolve eq1919 p4XZ -- subsumption resolution 1919,129
  have eq1959 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 := resolve eq1958 rule_def_0_2 -- subsumption resolution 1958,151
  have eq1960 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 := resolve eq1959 rule_def_2_2 -- subsumption resolution 1959,160
  have eq1968 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq1927 p4XZ -- subsumption resolution 1927,129
  have eq1969 : a = sk0 ∨ a = b ∨ c = sk0 := resolve eq1928 p4XZ -- subsumption resolution 1928,129
  have eq2113 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq1968 trans_resol -- equality factoring 1968
  have eq2131 : c = sk0 ∨ a = sk0 := resolve eq2113 eq1969 -- subsumption resolution 2113,1969
  have eq2174 : (old c sk1 c) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq2131.imp_left (fun h : c = sk0 ↦ superpose h eq797)) -- superposition 797,2131, 2131 into 797, unify on (0).2 in 2131 and (0).1 in 797
  have eq2212 : a = c ∨ c = b ∨ a = sk0 := resolve eq2174 p4YZ -- subsumption resolution 2174,130
  have eq2213 : c = b ∨ a = sk0 := resolve eq2212 ac -- subsumption resolution 2212,125
  have eq2214 : a = sk0 := resolve eq2213 bc -- subsumption resolution 2213,126
  have eq2635 : (sP0 sk3 a sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1575 -- backward demodulation 1575,2214
  have eq2736 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1906 -- backward demodulation 1906,2214
  have eq2750 : a = c ∨ (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1960 -- backward demodulation 1960,2214
  have eq3562 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq2635 rule_def_0_1 -- subsumption resolution 2635,150
  have eq3563 : (old sk3 a sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3562 -- forward demodulation 3562,2214
  have eq3564 : a = c ∨ (old sk3 a sk1) ∨ a = b := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3563 -- forward demodulation 3563,2214
  have eq3565 : (old sk3 a sk1) ∨ a = b := resolve eq3564 ac -- subsumption resolution 3564,125
  have eq3860 : c = sk1 := resolve eq2736 ac -- subsumption resolution 2736,125
  have eq3975 : (old sk3 a c) ∨ a = b := Eq.mp (by simp only [eq3860, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3565 -- backward demodulation 3565,3860
  have eq4164 : a = b := resolve eq3975 p4XY -- subsumption resolution 3975,128
  have eq4166 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq4164, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 127,4164
  have eq4174 : ∀ (X0 X1 X2 : G) , (old a a (sF4 X0 X1 X2)) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq4164, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_4 -- backward demodulation 174,4164
  have eq4445 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq4174 eq4166 -- subsumption resolution 4174,4166
  have eq4849 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) := resolve eq2750 ac -- subsumption resolution 2750,125
  have eq4850 : (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) := resolve eq4849 eq4445 -- subsumption resolution 4849,4445
  have eq4851 : (sP1 a c a) ∨ (sP3 sk0 c sk0) := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4850 -- forward demodulation 4850,2214
  have eq4852 : (sP3 a c a) ∨ (sP1 a c a) := Eq.mp (by simp only [eq2214, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4851 -- forward demodulation 4851,2214
  have eq4853 : (sP1 a c a) := resolve eq4852 eq217 -- subsumption resolution 4852,217
  have eq4919 (X0 X1 : G) : ¬(sP1 X0 X1 a) := resolve eq4166 rule_def_1_2 -- resolution 4166,155
  subsumption eq4919 eq4853 -- resolution 4853,4919

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_11_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_2 : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X0 X1)) (prev_5 : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X2 ∨ X1 = X3)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_11 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X3 X0 X1 ∨ ¬ old X4 X0 X2 ∨ old X0 X3 X4)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X1 ∨ ¬ new X4 X0 X2 ∨ new X0 X3 X4) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq194 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 150
  have eq195 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq194 rfl -- equality resolution 194
  have eq196 : (new a b c) := resolve eq195 rfl -- equality resolution 195
  have eq214 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 168,141
  have eq224 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 170,132
  have eq258 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 163,141
  have eq289 (X0 : G) : ¬(new sk0 sk0 X0) ∨ ¬(new sk0 X0 sk2) ∨ sk4 = X0 := resolve prev_5 preserve_2 -- resolution 184,192
  have eq489 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 178,190
  have eq490 : (sP4 sk3 sk0 sk1) ∨ (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) := resolve new_imp preserve_1 -- resolution 178,191
  have eq491 : (sP4 sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) := resolve new_imp preserve_2 -- resolution 178,192
  have eq535 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq214 rule_def_3_3 -- resolution 214,169
  have eq536 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq535 rfl -- duplicate literal removal 535
  have eq613 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq258 rule_def_2_4 -- resolution 258,164
  have eq616 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq613 rfl -- duplicate literal removal 613
  have eq792 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq489 rule_def_4_0 -- resolution 489,172
  have eq793 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq489 rule_def_4_1 -- resolution 489,173
  have eq804 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq792 rule_def_0_0 -- subsumption resolution 792,151
  have eq805 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq804 rule_def_1_0 -- subsumption resolution 804,155
  have eq806 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq793 rule_def_1_1 -- subsumption resolution 793,156
  have eq807 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq806 rule_def_3_1 -- subsumption resolution 806,167
  have eq810 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq805 rule_def_3_0 -- resolution 805,166
  have eq816 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq805 eq536 -- resolution 805,536
  have eq820 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq810 rule_def_2_0 -- subsumption resolution 810,160
  have eq822 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq816 eq616 -- subsumption resolution 816,616
  have eq825 : (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq490 rule_def_4_1 -- resolution 490,173
  have eq838 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq825 rule_def_1_1 -- subsumption resolution 825,156
  have eq839 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 := resolve eq838 rule_def_3_1 -- subsumption resolution 838,167
  have eq857 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ a = sk4 := resolve eq491 rule_def_4_0 -- resolution 491,172
  have eq858 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ c = sk0 := resolve eq491 rule_def_4_1 -- resolution 491,173
  have eq869 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ a = sk4 := resolve eq857 rule_def_0_0 -- subsumption resolution 857,151
  have eq870 : (sP3 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 := resolve eq869 rule_def_1_0 -- subsumption resolution 869,155
  have eq871 : (sP2 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ c = sk0 := resolve eq858 rule_def_1_1 -- subsumption resolution 858,156
  have eq872 : (sP2 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ c = sk0 := resolve eq871 rule_def_3_1 -- subsumption resolution 871,167
  have eq999 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq807 rule_def_2_2 -- resolution 807,162
  have eq1000 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq807 rule_def_2_1 -- resolution 807,161
  have eq1002 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq999 rule_def_0_2 -- subsumption resolution 999,153
  have eq1125 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq1000 rule_def_0_1 -- resolution 1000,152
  have eq1330 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq839 eq616 -- resolution 839,616
  have eq1332 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq839 rule_def_2_2 -- resolution 839,162
  have eq1335 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1332 rule_def_0_2 -- subsumption resolution 1332,153
  have eq1462 : (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 ∨ b = sk4 := resolve eq870 rule_def_3_0 -- resolution 870,166
  have eq1472 : (old sk4 sk0 sk2) ∨ a = sk4 ∨ b = sk4 := resolve eq1462 rule_def_2_0 -- subsumption resolution 1462,160
  have eq1616 : (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ c = sk0 ∨ a = b := resolve eq872 eq616 -- resolution 872,616
  have eq1618 : (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq872 rule_def_2_2 -- resolution 872,162
  have eq1621 : (old sk4 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq1618 rule_def_0_2 -- subsumption resolution 1618,153
  have eq1635 (X0 X1 : G) : ¬(old sk0 X1 sk2) ∨ c = sk2 ∨ (old sk0 X0 sk4) ∨ ¬(old X0 sk0 X1) ∨ c = sk0 := resolve eq1621 old_11 -- resolution 1621,144
  have eq3506 (X0 : G) : c = sk2 ∨ (old sk0 X0 sk4) ∨ ¬(old X0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq1635 eq1002 -- resolution 1635,1002
  have eq3510 (X0 : G) : ¬(old X0 sk0 sk1) ∨ (old sk0 X0 sk4) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq3506 rfl -- duplicate literal removal 3506
  have eq3521 : (old sk0 sk3 sk4) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 := resolve eq3510 eq1335 -- resolution 3510,1335
  have eq3528 : (old sk0 sk3 sk4) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq3521 rfl -- duplicate literal removal 3521
  have eq3551 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ (new sk0 sk3 sk4) := resolve eq3528 imp_new_0 -- resolution 3528,149
  have eq3555 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq3551 preserve_3 -- subsumption resolution 3551,193
  have eq3589 : (old sk0 sk1 c) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq3555.imp_left (fun h : c = sk2 ↦ superpose h eq820)) -- superposition 820,3555, 3555 into 820, unify on (0).2 in 3555 and (0).3 in 820
  have eq3590 : (old sk0 sk1 c) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq3555.imp_left (fun h : c = sk2 ↦ superpose h eq822)) -- superposition 822,3555, 3555 into 822, unify on (0).2 in 3555 and (0).3 in 822
  have eq3613 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 := Or.assoc4 (eq3555.imp_left (fun h : c = sk2 ↦ superpose h eq1125)) -- superposition 1125,3555, 3555 into 1125, unify on (0).2 in 3555 and (0).3 in 1125
  have eq3631 : (sP0 sk4 sk0 c) ∨ (old sk4 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk0 ∨ c = sk1 := Or.assoc4 (eq3555.imp_left (fun h : c = sk2 ↦ superpose h eq1616)) -- superposition 1616,3555, 3555 into 1616, unify on (0).2 in 3555 and (0).3 in 1616
  have eq3676 : (sP0 sk4 sk0 c) ∨ (old sk4 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq3631 rfl -- duplicate literal removal 3631
  have eq3683 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 := resolve eq3613 rfl -- duplicate literal removal 3613
  have eq3708 : c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3589 p4XY -- subsumption resolution 3589,130
  have eq3709 : c = sk1 ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq3590 p4XY -- subsumption resolution 3590,130
  have eq3718 : c = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk0 := resolve eq3683 p4XY -- subsumption resolution 3683,130
  have eq3723 : (sP0 sk4 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk1 := resolve eq3676 p4XY -- subsumption resolution 3676,130
  have eq3774 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq3708.imp_left (fun h : c = sk1 ↦ superpose h eq489)) -- superposition 489,3708, 3708 into 489, unify on (0).2 in 3708 and (0).2 in 489
  have eq3895 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3774 p4XZ -- subsumption resolution 3774,131
  have eq3896 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3895 rule_def_0_0 -- subsumption resolution 3895,151
  have eq3897 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3896 rule_def_1_0 -- subsumption resolution 3896,155
  have eq3898 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3897 rule_def_4_0 -- subsumption resolution 3897,172
  have eq3899 : (sP3 sk0 c sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3898 rule_def_2_0 -- subsumption resolution 3898,160
  have eq3900 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3899 rule_def_3_0 -- subsumption resolution 3899,166
  have eq4097 : a ≠ b ∨ c = sk0 ∨ a = sk0 := resolve eq3900 trans_resol -- equality factoring 3900
  have eq4210 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq3709.imp_left (fun h : c = sk1 ↦ superpose h eq489)) -- superposition 489,3709, 3709 into 489, unify on (0).2 in 3709 and (0).2 in 489
  have eq4357 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4210 p4XZ -- subsumption resolution 4210,131
  have eq4358 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4357 rule_def_0_0 -- subsumption resolution 4357,151
  have eq4359 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4358 rule_def_1_0 -- subsumption resolution 4358,155
  have eq4360 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4359 rule_def_4_0 -- subsumption resolution 4359,172
  have eq4361 : (sP2 sk0 c sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4360 eq536 -- subsumption resolution 4360,536
  have eq4362 : a = b ∨ c = sk0 ∨ a = sk0 := resolve eq4361 eq616 -- subsumption resolution 4361,616
  have eq4363 : c = sk0 ∨ a = sk0 := resolve eq4362 eq4097 -- subsumption resolution 4362,4097
  have eq4413 : (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq4363.imp_left (fun h : c = sk0 ↦ superpose h eq820)) -- superposition 820,4363, 4363 into 820, unify on (0).2 in 4363 and (0).1 in 820
  have eq4532 : a = c ∨ c = b ∨ a = sk0 := resolve eq4413 p4YZ -- subsumption resolution 4413,132
  have eq4533 : c = b ∨ a = sk0 := resolve eq4532 ac -- subsumption resolution 4532,127
  have eq4534 : a = sk0 := resolve eq4533 bc -- subsumption resolution 4533,128
  have eq4535 : (new a sk1 sk2) := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_0 -- backward demodulation 190,4534
  have eq4536 : (new sk3 a sk1) := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 191,4534
  have eq4538 : ¬(new a sk3 sk4) := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 193,4534
  have eq4547 : ∀ (X0 : G) , ¬(new a a X0) ∨ ¬(new sk0 X0 sk2) ∨ sk4 = X0 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq289 -- backward demodulation 289,4534
  have eq4686 : (sP3 sk4 a sk2) ∨ (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq870 -- backward demodulation 870,4534
  have eq4721 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1002 -- backward demodulation 1002,4534
  have eq4853 : (sP0 sk3 a sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1330 -- backward demodulation 1330,4534
  have eq4910 : (old sk4 a sk2) ∨ a = sk4 ∨ b = sk4 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1472 -- backward demodulation 1472,4534
  have eq5511 : a = c ∨ c = sk1 ∨ a = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3718 -- backward demodulation 3718,4534
  have eq5515 : a = c ∨ (sP0 sk4 sk0 c) ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3723 -- backward demodulation 3723,4534
  have eq5576 : ∀ (X0 : G) , ¬(new a a X0) ∨ ¬(new a X0 sk2) ∨ sk4 = X0 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4547 -- forward demodulation 4547,4534
  have eq5781 : (old sk4 a sk2) ∨ (sP3 sk4 a sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4686 -- forward demodulation 4686,4534
  have eq5782 : (sP2 sk4 a sk2) ∨ (old sk4 a sk2) ∨ (sP3 sk4 a sk2) ∨ a = sk4 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5781 -- forward demodulation 5781,4534
  have eq5951 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq4853 rule_def_0_1 -- subsumption resolution 4853,152
  have eq5952 : (old sk3 a sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5951 -- forward demodulation 5951,4534
  have eq5953 : a = c ∨ (old sk3 a sk1) ∨ a = b := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5952 -- forward demodulation 5952,4534
  have eq5954 : (old sk3 a sk1) ∨ a = b := resolve eq5953 ac -- subsumption resolution 5953,127
  have eq7185 : c = sk1 ∨ a = sk1 ∨ b = sk1 := resolve eq5511 ac -- subsumption resolution 5511,127
  have eq7188 : (sP0 sk4 sk0 c) ∨ a = b ∨ c = sk1 := resolve eq5515 ac -- subsumption resolution 5515,127
  have eq7189 : (sP0 sk4 a c) ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq4534, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7188 -- forward demodulation 7188,4534
  have eq7190 : c = sk1 ∨ a = b := resolve eq7189 rule_def_0_1 -- subsumption resolution 7189,152
  have eq7302 : (old sk3 a c) ∨ a = b ∨ a = b := Or.assoc2 (eq7190.imp_left (fun h : c = sk1 ↦ superpose h eq5954)) -- superposition 5954,7190, 7190 into 5954, unify on (0).2 in 7190 and (0).3 in 5954
  have eq7303 : (old sk3 a c) ∨ a = b := resolve eq7302 rfl -- duplicate literal removal 7302
  have eq7304 : a = b := resolve eq7303 p4XY -- subsumption resolution 7303,130
  have eq7306 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq7304, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 129,7304
  have eq7309 : ∀ (X0 X1 X2 : G) , ¬(sP2 X0 X1 X2) ∨ a = X0 := Eq.mp (by simp only [eq7304, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_0 -- backward demodulation 160,7304
  have eq7315 : (new a a c) := Eq.mp (by simp only [eq7304, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq196 -- backward demodulation 196,7304
  have eq7567 : a = sk4 ∨ (old sk4 a sk2) ∨ a = sk4 := Eq.mp (by simp only [eq7304, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4910 -- backward demodulation 4910,7304
  have eq7728 : a = sk1 ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq7304, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7185 -- backward demodulation 7185,7304
  have eq7734 : c = sk1 ∨ a = sk1 := resolve eq7728 rfl -- duplicate literal removal 7728
  have eq7770 : (old sk4 a sk2) ∨ a = sk4 := resolve eq7567 rfl -- duplicate literal removal 7567
  have eq7997 : (new a c sk2) ∨ a = sk1 := eq7734.imp_left (fun h : c = sk1 ↦ superpose h eq4535) -- superposition 4535,7734, 7734 into 4535, unify on (0).2 in 7734 and (0).2 in 4535
  have eq8149 : ¬(new a c sk2) ∨ c = sk4 := resolve eq5576 eq7315 -- resolution 5576,7315
  have eq8241 : c = sk4 ∨ a = sk1 := resolve eq7997 eq8149 -- resolution 7997,8149
  have eq8269 : (old c a sk2) ∨ a = c ∨ a = sk1 := Or.assoc2 (eq8241.imp_left (fun h : c = sk4 ↦ superpose h eq7770)) -- superposition 7770,8241, 8241 into 7770, unify on (0).2 in 8241 and (0).1 in 7770
  have eq8271 : a = c ∨ a = sk1 := resolve eq8269 p4YZ -- subsumption resolution 8269,132
  have eq8272 : a = sk1 := resolve eq8271 ac -- subsumption resolution 8271,127
  have eq8274 : (new sk3 a a) := Eq.mp (by simp only [eq8272, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4536 -- backward demodulation 4536,8272
  have eq8297 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq8272, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4721 -- backward demodulation 4721,8272
  have eq8526 : (old a sk1 sk2) ∨ c = sk2 := resolve eq8297 ac -- subsumption resolution 8297,127
  have eq8527 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq8272, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8526 -- forward demodulation 8526,8272
  have eq8528 : c = sk2 := resolve eq8527 eq7306 -- subsumption resolution 8527,7306
  have eq8555 : (sP3 sk4 a c) ∨ (sP2 sk4 a sk2) ∨ (old sk4 a sk2) ∨ a = sk4 := Eq.mp (by simp only [eq8528, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5782 -- backward demodulation 5782,8528
  have eq8641 : (sP2 sk4 a sk2) ∨ (old sk4 a sk2) ∨ a = sk4 := resolve eq8555 eq224 -- subsumption resolution 8555,224
  have eq8642 : (old sk4 a sk2) ∨ a = sk4 := resolve eq8641 eq7309 -- subsumption resolution 8641,7309
  have eq8643 : (old sk4 a c) ∨ a = sk4 := Eq.mp (by simp only [eq8528, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8642 -- forward demodulation 8642,8528
  have eq8644 : a = sk4 := resolve eq8643 p4XY -- subsumption resolution 8643,130
  have eq8645 : ¬(new a sk3 a) := Eq.mp (by simp only [eq8644, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4538 -- backward demodulation 4538,8644
  have eq9144 : (new a sk3 a) := resolve eq8274 prev_2 -- resolution 8274,181
  subsumption eq8645 eq9144 -- subsumption resolution 9144,8645

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_12_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_5 : (∀ X0 X1 X2 X3, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X2 ∨ X1 = X3)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (prev_8 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X3 = X0)) (old_12 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X2 ∨ ¬ old X4 X0 X1 ∨ ¬ old X5 X0 X3 ∨ X4 = X5)) (old_15 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X0 ∨ ¬ old X0 X2 X3 ∨ ¬ old X3 X0 X1 ∨ ¬ old X4 X0 X2 ∨ X0 = X4)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old a X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (imp_new_4 : ∀ X Y Z X3, b ≠ X ∨ c ≠ Y ∨ ¬ old a X3 a ∨ ¬ old b X3 a ∨ ¬ old Z b X3 ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X2 ∨ ¬ new X4 X0 X1 ∨ ¬ new X5 X0 X3 ∨ X4 = X5) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq199 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 153
  have eq200 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq199 rfl -- equality resolution 199
  have eq201 : (new a b c) := resolve eq200 rfl -- equality resolution 200
  have eq202 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old a X3 b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 157
  have eq203 (X2 X3 : G) : ¬(old a X3 b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq202 rfl -- equality resolution 202
  have eq207 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old X2 b X3) ∨ ¬(old b X3 a) ∨ ¬(old a X3 a) ∨ b ≠ X0 := resolve imp_new_4 rfl -- equality resolution 168
  have eq208 (X2 X3 : G) : ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ (new b c X2) ∨ ¬(old a X3 a) := resolve eq207 rfl -- equality resolution 207
  have eq215 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 160,135
  have eq219 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 171,144
  have eq229 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 173,135
  have eq244 (X0 : G) : ¬(new X0 sk0 sk1) ∨ sk4 = X0 := resolve prev_8 preserve_2 -- resolution 190,196
  have eq251 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq203 rule_def_1_3 -- resolution 203,161
  have eq264 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 166,144
  have eq295 (X0 : G) : ¬(new b b X0) ∨ ¬(new b X0 c) ∨ a = X0 := resolve prev_5 eq201 -- resolution 187,201
  have eq373 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(old a (sF3 X1 X2 X3) a) ∨ ¬(sP3 X1 X2 X3) := resolve eq208 rule_def_3_3 -- resolution 208,172
  have eq374 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF3 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP3 X1 X2 X3) := resolve eq373 rule_def_3_2 -- subsumption resolution 373,171
  have eq516 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 181,194
  have eq517 : (sP4 sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP3 sk0 sk3 sk2) := resolve new_imp preserve_1 -- resolution 181,195
  have eq518 : (sP4 sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) := resolve new_imp preserve_2 -- resolution 181,196
  have eq519 : (sP4 sk5 sk0 sk3) ∨ (sP2 sk5 sk0 sk3) ∨ (sP1 sk5 sk0 sk3) ∨ (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP3 sk5 sk0 sk3) := resolve new_imp preserve_3 -- resolution 181,197
  have eq573 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq219 rule_def_3_3 -- resolution 219,172
  have eq574 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq573 rfl -- duplicate literal removal 573
  have eq616 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq251 rule_def_1_2 -- resolution 251,160
  have eq617 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq616 rfl -- duplicate literal removal 616
  have eq626 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP3 X1 X2 X0) ∨ ¬(sP3 X1 X2 X0) := resolve eq374 rule_def_3_4 -- resolution 374,173
  have eq627 (X0 X1 X2 : G) : ¬(sP3 X1 X2 X0) ∨ (new b c X0) := resolve eq626 rfl -- duplicate literal removal 626
  have eq654 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq264 rule_def_2_4 -- resolution 264,167
  have eq657 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq654 rfl -- duplicate literal removal 654
  have eq866 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq516 rule_def_4_0 -- resolution 516,175
  have eq867 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq516 rule_def_4_1 -- resolution 516,176
  have eq878 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq866 rule_def_0_0 -- subsumption resolution 866,154
  have eq879 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq878 rule_def_1_0 -- subsumption resolution 878,158
  have eq880 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq867 rule_def_1_1 -- subsumption resolution 867,159
  have eq881 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq880 rule_def_3_1 -- subsumption resolution 880,170
  have eq884 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq879 rule_def_3_0 -- resolution 879,169
  have eq890 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq879 eq574 -- resolution 879,574
  have eq894 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq884 rule_def_2_0 -- subsumption resolution 884,163
  have eq896 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq890 eq657 -- subsumption resolution 890,657
  have eq898 : (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP3 sk0 sk3 sk2) ∨ a = sk0 := resolve eq517 rule_def_4_0 -- resolution 517,175
  have eq899 : (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP3 sk0 sk3 sk2) ∨ c = sk3 := resolve eq517 rule_def_4_1 -- resolution 517,176
  have eq900 : (sP3 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk2 := resolve eq517 rule_def_4_2 -- resolution 517,177
  have eq910 : (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP3 sk0 sk3 sk2) ∨ a = sk0 := resolve eq898 rule_def_0_0 -- subsumption resolution 898,154
  have eq911 : (sP3 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk0 := resolve eq910 rule_def_1_0 -- subsumption resolution 910,158
  have eq912 : (sP2 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP3 sk0 sk3 sk2) ∨ c = sk3 := resolve eq899 rule_def_1_1 -- subsumption resolution 899,159
  have eq913 : (sP2 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ c = sk3 := resolve eq912 rule_def_3_1 -- subsumption resolution 912,170
  have eq931 : (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ a = sk4 := resolve eq518 rule_def_4_0 -- resolution 518,175
  have eq932 : (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ c = sk0 := resolve eq518 rule_def_4_1 -- resolution 518,176
  have eq933 : (sP3 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk1 := resolve eq518 rule_def_4_2 -- resolution 518,177
  have eq943 : (sP2 sk4 sk0 sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ a = sk4 := resolve eq931 rule_def_0_0 -- subsumption resolution 931,154
  have eq944 : (sP3 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk4 := resolve eq943 rule_def_1_0 -- subsumption resolution 943,158
  have eq945 : (sP2 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP3 sk4 sk0 sk1) ∨ c = sk0 := resolve eq932 rule_def_1_1 -- subsumption resolution 932,159
  have eq946 : (sP2 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ c = sk0 := resolve eq945 rule_def_3_1 -- subsumption resolution 945,170
  have eq964 : (sP2 sk5 sk0 sk3) ∨ (sP1 sk5 sk0 sk3) ∨ (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP3 sk5 sk0 sk3) ∨ a = sk5 := resolve eq519 rule_def_4_0 -- resolution 519,175
  have eq965 : (sP2 sk5 sk0 sk3) ∨ (sP1 sk5 sk0 sk3) ∨ (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP3 sk5 sk0 sk3) ∨ c = sk0 := resolve eq519 rule_def_4_1 -- resolution 519,176
  have eq976 : (sP2 sk5 sk0 sk3) ∨ (sP1 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP3 sk5 sk0 sk3) ∨ a = sk5 := resolve eq964 rule_def_0_0 -- subsumption resolution 964,154
  have eq977 : (sP3 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP2 sk5 sk0 sk3) ∨ a = sk5 := resolve eq976 rule_def_1_0 -- subsumption resolution 976,158
  have eq978 : (sP2 sk5 sk0 sk3) ∨ (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ (sP3 sk5 sk0 sk3) ∨ c = sk0 := resolve eq965 rule_def_1_1 -- subsumption resolution 965,159
  have eq979 : (sP2 sk5 sk0 sk3) ∨ (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ c = sk0 := resolve eq978 rule_def_3_1 -- subsumption resolution 978,170
  have eq1092 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq881 rule_def_2_2 -- resolution 881,165
  have eq1093 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq881 rule_def_2_1 -- resolution 881,164
  have eq1095 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1092 rule_def_0_2 -- subsumption resolution 1092,156
  have eq1274 : (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq911 rule_def_3_0 -- resolution 911,169
  have eq1280 : (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk0 ∨ a = b := resolve eq911 eq574 -- resolution 911,574
  have eq1284 : (old sk0 sk3 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq1274 rule_def_2_0 -- subsumption resolution 1274,163
  have eq1286 : (old sk0 sk3 sk2) ∨ a = sk0 ∨ a = b := resolve eq1280 eq657 -- subsumption resolution 1280,657
  have eq1437 : (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ c = sk3 ∨ c = sk2 := resolve eq913 rule_def_2_2 -- resolution 913,165
  have eq1440 : (old sk0 sk3 sk2) ∨ c = sk3 ∨ c = sk2 := resolve eq1437 rule_def_0_2 -- subsumption resolution 1437,156
  have eq1726 : (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq946 rule_def_2_2 -- resolution 946,165
  have eq1729 : (old sk4 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1726 rule_def_0_2 -- subsumption resolution 1726,156
  have eq1730 : (old sk5 sk0 sk3) ∨ (sP2 sk5 sk0 sk3) ∨ a = sk5 ∨ b = sk5 := resolve eq977 rule_def_3_0 -- resolution 977,169
  have eq1740 : (old sk5 sk0 sk3) ∨ a = sk5 ∨ b = sk5 := resolve eq1730 rule_def_2_0 -- subsumption resolution 1730,163
  have eq1758 (X0 X1 X2 : G) : ¬(old sk0 sk1 X2) ∨ c = sk1 ∨ sk4 = X0 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ ¬(old sk0 X1 X2) := resolve eq1729 old_12 -- resolution 1729,148
  have eq1761 (X0 X1 : G) : ¬(old sk0 sk1 X0) ∨ c = sk1 ∨ sk0 = sk4 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ ¬(old sk0 X1 sk0) := resolve eq1729 old_15 -- resolution 1729,151
  have eq1764 : (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ c = sk0 ∨ a = b := resolve eq979 eq657 -- resolution 979,657
  have eq1766 : (sP0 sk5 sk0 sk3) ∨ (old sk5 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq979 rule_def_2_2 -- resolution 979,165
  have eq1769 : (old sk5 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq1766 rule_def_0_2 -- subsumption resolution 1766,156
  have eq1813 (X0 X1 : G) : ¬(old sk0 sk3 X0) ∨ c = sk3 ∨ sk0 = sk5 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ ¬(old sk0 X1 sk0) := resolve eq1769 old_15 -- resolution 1769,151
  have eq2257 : (sP2 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ a = sk2 ∨ (new b c sk2) := resolve eq900 eq627 -- resolution 900,627
  have eq4185 : (sP1 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ a = sk2 ∨ (new b c sk2) ∨ a = sk3 := resolve eq2257 rule_def_2_1 -- resolution 2257,164
  have eq8330 (X0 X1 : G) : c = sk1 ∨ sk4 = X0 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ ¬(old sk0 X1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1758 eq1095 -- resolution 1758,1095
  have eq8337 (X0 X1 : G) : ¬(old sk0 X1 sk2) ∨ sk4 = X0 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq8330 rfl -- duplicate literal removal 8330
  have eq8360 (X0 : G) : c = sk1 ∨ sk0 = sk4 ∨ ¬(old sk2 sk0 X0) ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk1 ∨ c = sk2 := resolve eq1761 eq1095 -- resolution 1761,1095
  have eq8367 (X0 : G) : c = sk1 ∨ sk0 = sk4 ∨ ¬(old sk2 sk0 X0) ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := resolve eq8360 rfl -- duplicate literal removal 8360
  have eq8430 (X0 : G) : c = sk3 ∨ sk0 = sk5 ∨ ¬(old sk2 sk0 X0) ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk3 ∨ c = sk2 := resolve eq1813 eq1440 -- resolution 1813,1440
  have eq8437 (X0 : G) : c = sk3 ∨ sk0 = sk5 ∨ ¬(old sk2 sk0 X0) ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := resolve eq8430 rfl -- duplicate literal removal 8430
  have eq10195 (X0 : G) : sk4 = X0 ∨ ¬(old X0 sk0 sk3) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk2 := resolve eq8337 eq1440 -- resolution 8337,1440
  have eq10199 (X0 : G) : ¬(old X0 sk0 sk3) ∨ sk4 = X0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq10195 rfl -- duplicate literal removal 10195
  have eq10210 : sk4 = sk5 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk0 ∨ c = sk3 := resolve eq10199 eq1769 -- resolution 10199,1769
  have eq10219 : sk4 = sk5 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq10210 rfl -- duplicate literal removal 10210
  have eq10222 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := resolve eq10219 preserve_4 -- subsumption resolution 10219,198
  have eq10257 : (old sk0 c sk2) ∨ a = sk0 ∨ b = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := Or.assoc3 (eq10222.imp_left (fun h : c = sk3 ↦ superpose h eq1284)) -- superposition 1284,10222, 10222 into 1284, unify on (0).2 in 10222 and (0).2 in 1284
  have eq10258 : (old sk0 c sk2) ∨ a = sk0 ∨ a = b ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := Or.assoc3 (eq10222.imp_left (fun h : c = sk3 ↦ superpose h eq1286)) -- superposition 1286,10222, 10222 into 1286, unify on (0).2 in 10222 and (0).2 in 1286
  have eq10290 : (old sk5 sk0 c) ∨ a = sk5 ∨ b = sk5 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := Or.assoc3 (eq10222.imp_left (fun h : c = sk3 ↦ superpose h eq1740)) -- superposition 1740,10222, 10222 into 1740, unify on (0).2 in 10222 and (0).3 in 1740
  have eq10292 : (sP0 sk5 sk0 c) ∨ (old sk5 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := Or.assoc4 (eq10222.imp_left (fun h : c = sk3 ↦ superpose h eq1764)) -- superposition 1764,10222, 10222 into 1764, unify on (0).2 in 10222 and (0).3 in 1764
  have eq10394 : (sP0 sk5 sk0 c) ∨ (old sk5 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq10292 rfl -- duplicate literal removal 10292
  have eq10418 : c = sk2 ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10257 p4XZ -- subsumption resolution 10257,134
  have eq10419 : c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10258 p4XZ -- subsumption resolution 10258,134
  have eq10420 : a = sk5 ∨ b = sk5 ∨ c = sk1 ∨ c = sk2 ∨ c = sk0 := resolve eq10290 p4XY -- subsumption resolution 10290,133
  have eq10422 : (sP0 sk5 sk0 c) ∨ c = sk0 ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq10394 p4XY -- subsumption resolution 10394,133
  have eq10511 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := Or.assoc6 (eq10418.imp_left (fun h : c = sk2 ↦ superpose h eq516)) -- superposition 516,10418, 10418 into 516, unify on (0).2 in 10418 and (0).3 in 516
  have eq10811 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10511 eq215 -- subsumption resolution 10511,215
  have eq10812 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10811 p4XY -- subsumption resolution 10811,133
  have eq10813 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10812 eq229 -- subsumption resolution 10812,229
  have eq10814 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10813 rule_def_0_0 -- subsumption resolution 10813,154
  have eq10815 : (sP2 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq10814 rule_def_4_0 -- subsumption resolution 10814,175
  have eq10816 : c = sk1 ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq10815 rule_def_2_0 -- subsumption resolution 10815,163
  have eq10834 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc6 (eq10816.imp_left (fun h : c = sk1 ↦ superpose h eq516)) -- superposition 516,10816, 10816 into 516, unify on (0).2 in 10816 and (0).2 in 516
  have eq11045 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq10834 p4XZ -- subsumption resolution 10834,134
  have eq11046 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq11045 rule_def_0_0 -- subsumption resolution 11045,154
  have eq11047 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq11046 rule_def_1_0 -- subsumption resolution 11046,158
  have eq11048 : (sP2 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq11047 rule_def_4_0 -- subsumption resolution 11047,175
  have eq11049 : (sP3 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq11048 rule_def_2_0 -- subsumption resolution 11048,163
  have eq11050 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq11049 rule_def_3_0 -- subsumption resolution 11049,169
  have eq11390 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq11050 trans_resol -- equality factoring 11050
  have eq11973 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := Or.assoc6 (eq10419.imp_left (fun h : c = sk2 ↦ superpose h eq516)) -- superposition 516,10419, 10419 into 516, unify on (0).2 in 10419 and (0).3 in 516
  have eq12327 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq11973 eq215 -- subsumption resolution 11973,215
  have eq12328 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12327 p4XY -- subsumption resolution 12327,133
  have eq12329 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12328 eq229 -- subsumption resolution 12328,229
  have eq12330 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12329 rule_def_4_1 -- subsumption resolution 12329,176
  have eq12331 : (sP2 sk0 sk1 c) ∨ a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12330 rule_def_0_0 -- subsumption resolution 12330,154
  have eq12332 : a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12331 eq657 -- subsumption resolution 12331,657
  have eq12333 : c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq12332 eq11390 -- subsumption resolution 12332,11390
  have eq12367 : (old sk0 c sk2) ∨ a = sk0 ∨ a = b ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq12333.imp_left (fun h : c = sk1 ↦ superpose h eq896)) -- superposition 896,12333, 12333 into 896, unify on (0).2 in 12333 and (0).2 in 896
  have eq12575 : (old sk0 c sk2) ∨ a = sk0 ∨ a = b ∨ c = sk0 := resolve eq12367 rfl -- duplicate literal removal 12367
  have eq12589 : a = sk0 ∨ a = b ∨ c = sk0 := resolve eq12575 p4XZ -- subsumption resolution 12575,134
  have eq12590 : c = sk0 ∨ a = sk0 := resolve eq12589 eq11390 -- subsumption resolution 12589,11390
  have eq12677 : (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq12590.imp_left (fun h : c = sk0 ↦ superpose h eq894)) -- superposition 894,12590, 12590 into 894, unify on (0).2 in 12590 and (0).1 in 894
  have eq12904 : a = c ∨ c = b ∨ a = sk0 := resolve eq12677 p4YZ -- subsumption resolution 12677,135
  have eq12905 : c = b ∨ a = sk0 := resolve eq12904 ac -- subsumption resolution 12904,130
  have eq12906 : a = sk0 := resolve eq12905 bc -- subsumption resolution 12905,131
  have eq12907 : (new a sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_0 -- backward demodulation 194,12906
  have eq12909 : (new sk4 a sk1) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 196,12906
  have eq12910 : (new sk5 a sk3) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 197,12906
  have eq12917 : ∀ (X0 : G) , ¬(new X0 a sk1) ∨ sk4 = X0 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq244 -- backward demodulation 244,12906
  have eq12951 : (sP3 a sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq516 -- backward demodulation 516,12906
  have eq12952 : (sP3 a sk3 sk2) ∨ (sP4 sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq517 -- backward demodulation 517,12906
  have eq13079 : (sP3 a sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq900 -- backward demodulation 900,12906
  have eq13095 : (sP3 sk4 a sk1) ∨ (sP1 sk4 sk0 sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq933 -- backward demodulation 933,12906
  have eq13104 : (sP3 sk4 a sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk4 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq944 -- backward demodulation 944,12906
  have eq13120 : (sP3 sk5 a sk3) ∨ (old sk5 sk0 sk3) ∨ (sP2 sk5 sk0 sk3) ∨ a = sk5 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq977 -- backward demodulation 977,12906
  have eq13151 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1093 -- backward demodulation 1093,12906
  have eq13153 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1095 -- backward demodulation 1095,12906
  have eq14131 : (sP1 a sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ a = sk2 ∨ (new b c sk2) ∨ a = sk3 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4185 -- backward demodulation 4185,12906
  have eq15523 : ∀ (X0 : G) , a = c ∨ c = sk1 ∨ sk0 = sk4 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8367 -- backward demodulation 8367,12906
  have eq15546 : ∀ (X0 : G) , a = c ∨ c = sk3 ∨ sk0 = sk5 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8437 -- backward demodulation 8437,12906
  have eq15806 : a = c ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10222 -- backward demodulation 10222,12906
  have eq15832 : a = c ∨ a = sk5 ∨ b = sk5 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10420 -- backward demodulation 10420,12906
  have eq15834 : a = c ∨ (sP0 sk5 sk0 c) ∨ a = b ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq10422 -- backward demodulation 10422,12906
  have eq15992 : (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12951 -- forward demodulation 12951,12906
  have eq15993 : (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15992 -- forward demodulation 15992,12906
  have eq15994 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15993 -- forward demodulation 15993,12906
  have eq15995 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP4 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15994 -- forward demodulation 15994,12906
  have eq15996 : (sP4 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15995 -- forward demodulation 15995,12906
  have eq15997 : (sP4 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12952 -- forward demodulation 12952,12906
  have eq15998 : (sP2 a sk3 sk2) ∨ (sP4 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (sP1 sk0 sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15997 -- forward demodulation 15997,12906
  have eq15999 : (sP1 a sk3 sk2) ∨ (sP2 a sk3 sk2) ∨ (sP4 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15998 -- forward demodulation 15998,12906
  have eq16000 : (sP0 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP2 a sk3 sk2) ∨ (sP4 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (old sk0 sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq15999 -- forward demodulation 15999,12906
  have eq16001 : (sP4 a sk3 sk2) ∨ (sP0 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP2 a sk3 sk2) ∨ (old a sk3 sk2) ∨ (sP3 a sk3 sk2) := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16000 -- forward demodulation 16000,12906
  have eq16144 : (sP1 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13079 -- forward demodulation 13079,12906
  have eq16145 : (sP0 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (old sk0 sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16144 -- forward demodulation 16144,12906
  have eq16146 : (old a sk3 sk2) ∨ (sP0 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP3 a sk3 sk2) ∨ (sP2 sk0 sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16145 -- forward demodulation 16145,12906
  have eq16147 : (sP3 a sk3 sk2) ∨ (old a sk3 sk2) ∨ (sP0 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP2 a sk3 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16146 -- forward demodulation 16146,12906
  have eq16188 : (sP1 sk4 a sk1) ∨ (sP3 sk4 a sk1) ∨ (sP0 sk4 sk0 sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13095 -- forward demodulation 13095,12906
  have eq16189 : (sP0 sk4 a sk1) ∨ (sP1 sk4 a sk1) ∨ (sP3 sk4 a sk1) ∨ (old sk4 sk0 sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16188 -- forward demodulation 16188,12906
  have eq16190 : (old sk4 a sk1) ∨ (sP0 sk4 a sk1) ∨ (sP1 sk4 a sk1) ∨ (sP3 sk4 a sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16189 -- forward demodulation 16189,12906
  have eq16191 : (sP3 sk4 a sk1) ∨ (old sk4 a sk1) ∨ (sP0 sk4 a sk1) ∨ (sP1 sk4 a sk1) ∨ (sP2 sk4 a sk1) ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16190 -- forward demodulation 16190,12906
  have eq16227 : (old sk4 a sk1) ∨ (sP3 sk4 a sk1) ∨ (sP2 sk4 sk0 sk1) ∨ a = sk4 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13104 -- forward demodulation 13104,12906
  have eq16228 : (sP3 sk4 a sk1) ∨ (old sk4 a sk1) ∨ (sP2 sk4 a sk1) ∨ a = sk4 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16227 -- forward demodulation 16227,12906
  have eq16275 : (old sk5 a sk3) ∨ (sP3 sk5 a sk3) ∨ (sP2 sk5 sk0 sk3) ∨ a = sk5 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13120 -- forward demodulation 13120,12906
  have eq16276 : (sP3 sk5 a sk3) ∨ (old sk5 a sk3) ∨ (sP2 sk5 a sk3) ∨ a = sk5 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq16275 -- forward demodulation 16275,12906
  have eq16287 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13151 -- forward demodulation 13151,12906
  have eq17732 : (old a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP0 sk0 sk3 sk2) ∨ a = sk2 ∨ (new b c sk2) ∨ a = sk3 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq14131 -- forward demodulation 14131,12906
  have eq17733 : (sP0 a sk3 sk2) ∨ (old a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ a = sk2 ∨ (new b c sk2) ∨ a = sk3 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq17732 -- forward demodulation 17732,12906
  have eq19054 (X0 : G) : c = sk1 ∨ sk0 = sk4 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := resolve eq15523 ac -- subsumption resolution 15523,130
  have eq19055 : ∀ (X0 : G) , a = sk4 ∨ c = sk1 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19054 -- forward demodulation 19054,12906
  have eq19056 : ∀ (X0 : G) , ¬(old sk2 a X0) ∨ a = sk4 ∨ c = sk1 ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19055 -- forward demodulation 19055,12906
  have eq19057 : ∀ (X0 : G) , ¬(old sk2 a X0) ∨ ¬(old a X0 a) ∨ a = sk4 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19056 -- forward demodulation 19056,12906
  have eq19110 (X0 : G) : c = sk3 ∨ sk0 = sk5 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := resolve eq15546 ac -- subsumption resolution 15546,130
  have eq19111 : ∀ (X0 : G) , a = sk5 ∨ c = sk3 ∨ ¬(old sk2 sk0 X0) ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19110 -- forward demodulation 19110,12906
  have eq19112 : ∀ (X0 : G) , ¬(old sk2 a X0) ∨ a = sk5 ∨ c = sk3 ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19111 -- forward demodulation 19111,12906
  have eq19113 : ∀ (X0 : G) , ¬(old sk2 a X0) ∨ ¬(old a X0 a) ∨ a = sk5 ∨ c = sk3 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19112 -- forward demodulation 19112,12906
  have eq19575 : c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq15806 ac -- subsumption resolution 15806,130
  have eq19641 : b = sk5 ∨ a = sk5 ∨ c = sk1 ∨ c = sk2 := resolve eq15832 ac -- subsumption resolution 15832,130
  have eq19643 : (sP0 sk5 sk0 c) ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq15834 ac -- subsumption resolution 15834,130
  have eq19644 : (sP0 sk5 a c) ∨ a = b ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq12906, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq19643 -- forward demodulation 19643,12906
  have eq19645 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq19644 rule_def_0_1 -- subsumption resolution 19644,155
  have eq20087 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP1 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b := Or.assoc6 (eq19645.imp_left (fun h : c = sk2 ↦ superpose h eq15996)) -- superposition 15996,19645, 19645 into 15996, unify on (0).2 in 19645 and (0).3 in 15996
  have eq20088 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (old a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b := resolve eq20087 eq215 -- subsumption resolution 20087,215
  have eq20089 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ (sP3 a sk1 c) ∨ c = sk1 ∨ a = b := resolve eq20088 p4XY -- subsumption resolution 20088,133
  have eq20090 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ (sP2 a sk1 c) ∨ c = sk1 ∨ a = b := resolve eq20089 eq229 -- subsumption resolution 20089,229
  have eq20091 : (sP4 a sk1 c) ∨ (sP0 a sk1 c) ∨ c = sk1 ∨ a = b := resolve eq20090 rule_def_2_0 -- subsumption resolution 20090,163
  have eq20092 : (sP0 a sk1 c) ∨ c = sk1 ∨ a = b := resolve eq20091 rule_def_4_1 -- subsumption resolution 20091,176
  have eq20208 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq20092 rule_def_0_1 -- resolution 20092,155
  have eq20216 (X0 : G) : ¬(new X0 a b) ∨ sk4 = X0 ∨ a = b ∨ c = sk1 := Or.assoc2 (eq20208.imp_left (fun h : b = sk1 ↦ superpose h eq12917)) -- superposition 12917,20208, 20208 into 12917, unify on (0).2 in 20208 and (0).3 in 12917
  have eq20645 : a ≠ b ∨ a = sk5 ∨ c = sk1 ∨ c = sk2 := resolve eq19641 trans_resol -- equality factoring 19641
  have eq20648 : a = sk5 ∨ c = sk1 ∨ c = sk2 := resolve eq20645 eq19645 -- subsumption resolution 20645,19645
  have eq20652 : a ≠ sk4 ∨ c = sk1 ∨ c = sk2 := eq20648.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 198,20648, 20648 into 198, unify on (0).2 in 20648 and (0).2 in 198
  have eq20748 : (sP3 a sk3 c) ∨ (old a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ c = sk1 ∨ a = b := Or.assoc6 (eq19645.imp_left (fun h : c = sk2 ↦ superpose h eq16147)) -- superposition 16147,19645, 19645 into 16147, unify on (0).2 in 19645 and (0).3 in 16147
  have eq20749 : (old a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq20748 eq229 -- subsumption resolution 20748,229
  have eq20750 : (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq20749 p4XY -- subsumption resolution 20749,133
  have eq20751 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq20750 eq215 -- subsumption resolution 20750,215
  have eq20752 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ c = sk1 ∨ a = b := resolve eq20751 ac -- subsumption resolution 20751,130
  have eq20753 : (sP0 a sk3 c) ∨ c = sk1 ∨ a = b := resolve eq20752 rule_def_2_0 -- subsumption resolution 20752,163
  have eq20755 : b = sk3 ∨ a = b ∨ c = sk1 := resolve eq20753 rule_def_0_1 -- resolution 20753,155
  have eq20777 : (new sk5 a b) ∨ a = b ∨ c = sk1 := eq20755.imp_left (fun h : b = sk3 ↦ superpose h eq12910) -- superposition 12910,20755, 20755 into 12910, unify on (0).2 in 20755 and (0).3 in 12910
  have eq21494 : sk4 = sk5 ∨ a = b ∨ c = sk1 ∨ a = b ∨ c = sk1 := resolve eq20216 eq20777 -- resolution 20216,20777
  have eq21495 : sk4 = sk5 ∨ a = b ∨ c = sk1 := resolve eq21494 rfl -- duplicate literal removal 21494
  have eq21497 : c = sk1 ∨ a = b := resolve eq21495 preserve_4 -- subsumption resolution 21495,198
  have eq21542 : (sP3 sk4 a c) ∨ (old sk4 a c) ∨ (sP0 sk4 a c) ∨ (sP1 sk4 a c) ∨ (sP2 sk4 a c) ∨ a = c ∨ a = b := Or.assoc6 (eq21497.imp_left (fun h : c = sk1 ↦ superpose h eq16191)) -- superposition 16191,21497, 21497 into 16191, unify on (0).2 in 21497 and (0).3 in 16191
  have eq21581 : (old sk4 a c) ∨ (sP0 sk4 a c) ∨ (sP1 sk4 a c) ∨ (sP2 sk4 a c) ∨ a = c ∨ a = b := resolve eq21542 eq229 -- subsumption resolution 21542,229
  have eq21582 : (sP0 sk4 a c) ∨ (sP1 sk4 a c) ∨ (sP2 sk4 a c) ∨ a = c ∨ a = b := resolve eq21581 p4XY -- subsumption resolution 21581,133
  have eq21583 : (sP0 sk4 a c) ∨ (sP2 sk4 a c) ∨ a = c ∨ a = b := resolve eq21582 eq215 -- subsumption resolution 21582,215
  have eq21584 : (sP0 sk4 a c) ∨ (sP2 sk4 a c) ∨ a = b := resolve eq21583 ac -- subsumption resolution 21583,130
  have eq21585 : (sP2 sk4 a c) ∨ a = b := resolve eq21584 rule_def_0_1 -- subsumption resolution 21584,155
  have eq21586 : a = b := resolve eq21585 eq657 -- subsumption resolution 21585,657
  have eq21588 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 132,21586
  have eq21589 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 155,21586
  have eq21590 : ∀ (X0 X1 X2 : G) , (old a (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_3 -- backward demodulation 161,21586
  have eq21591 : ∀ (X0 X1 X2 : G) , ¬(sP2 X0 X1 X2) ∨ a = X0 := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_0 -- backward demodulation 163,21586
  have eq21595 : ∀ (X0 X1 X2 : G) , (old X2 a (sF3 X0 X1 X2)) ∨ ¬(sP3 X0 X1 X2) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_3_4 -- backward demodulation 173,21586
  have eq21596 : ∀ (X0 X1 X2 : G) , (old a a (sF4 X0 X1 X2)) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_4 -- backward demodulation 179,21586
  have eq21597 : (new a a c) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq201 -- backward demodulation 201,21586
  have eq21631 : ∀ (X0 : G) , ¬(new a X0 c) ∨ ¬(new b b X0) ∨ a = X0 := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq295 -- backward demodulation 295,21586
  have eq21744 : ∀ (X0 X1 X2 : G) , ¬(sP3 X1 X2 X0) ∨ (new a c X0) := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq627 -- backward demodulation 627,21586
  have eq22378 : (new a c sk2) ∨ (sP0 a sk3 sk2) ∨ (old a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ a = sk2 ∨ a = sk3 := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq17733 -- backward demodulation 17733,21586
  have eq22656 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq21596 eq21588 -- subsumption resolution 21596,21588
  have eq22665 : ∀ (X0 : G) , ¬(new a a X0) ∨ ¬(new a X0 c) ∨ a = X0 := Eq.mp (by simp only [eq21586, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq21631 -- forward demodulation 21631,21586
  have eq23084 : (new a c sk2) ∨ (old a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ a = sk2 ∨ a = sk3 := resolve eq22378 eq21589 -- subsumption resolution 22378,21589
  have eq23085 : (new a c sk2) ∨ (old a sk3 sk2) ∨ a = sk2 ∨ a = sk3 := resolve eq23084 eq617 -- subsumption resolution 23084,617
  have eq23237 : (sP3 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) := resolve eq22656 eq15996 -- resolution 22656,15996
  have eq23238 : (sP3 a sk3 sk2) ∨ (sP1 a sk3 sk2) ∨ (sP2 a sk3 sk2) ∨ (old a sk3 sk2) ∨ (sP0 a sk3 sk2) := resolve eq22656 eq16001 -- resolution 22656,16001
  have eq23470 : ¬(new a c c) ∨ a = c := resolve eq22665 eq21597 -- resolution 22665,21597
  have eq23474 : ¬(new a c c) := resolve eq23470 ac -- subsumption resolution 23470,130
  have eq23972 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) := resolve eq23237 eq21744 -- resolution 23237,21744
  have eq23981 : (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) := resolve eq23972 eq617 -- subsumption resolution 23972,617
  have eq24006 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ (sP2 a c sk2) ∨ (old a c sk2) ∨ (sP0 a c sk2) ∨ c = sk1 ∨ c = sk2 := Or.assoc5 (eq19575.imp_left (fun h : c = sk3 ↦ superpose h eq23238)) -- superposition 23238,19575, 19575 into 23238, unify on (0).2 in 19575 and (0).2 in 23238
  have eq24014 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ (sP2 a c sk2) ∨ (sP0 a c sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq24006 p4XZ -- subsumption resolution 24006,134
  have eq24015 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ (sP2 a c sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq24014 rule_def_0_2 -- subsumption resolution 24014,156
  have eq24016 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq24015 rule_def_2_2 -- subsumption resolution 24015,165
  have eq24203 : (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (new a c sk2) ∨ c = sk2 := resolve eq23981 rule_def_2_2 -- resolution 23981,165
  have eq24206 : (new a c sk2) ∨ (old a sk1 sk2) ∨ c = sk2 := resolve eq24203 rule_def_0_2 -- subsumption resolution 24203,156
  have eq24232 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (old a c sk2) ∨ (sP4 a c sk2) := resolve eq24206 new_imp -- resolution 24206,181
  have eq24246 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP4 a c sk2) := resolve eq24232 p4XZ -- subsumption resolution 24232,134
  have eq24247 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) := resolve eq24246 eq22656 -- subsumption resolution 24246,22656
  have eq24248 : (old a sk1 sk2) ∨ c = sk2 ∨ (sP3 a c sk2) ∨ (sP2 a c sk2) ∨ (sP1 a c sk2) := resolve eq24247 rule_def_0_2 -- subsumption resolution 24247,156
  have eq24249 : (sP3 a c sk2) ∨ c = sk2 ∨ (old a sk1 sk2) ∨ (sP1 a c sk2) := resolve eq24248 rule_def_2_2 -- subsumption resolution 24248,165
  have eq24681 (X0 X1 : G) : ¬(old a (sF0 X0 X1 sk2) a) ∨ a = sk4 ∨ c = sk1 ∨ c = sk2 ∨ ¬(sP1 X0 X1 sk2) := resolve eq19057 rule_def_1_2 -- resolution 19057,160
  have eq24682 (X0 X1 : G) : ¬(old a (sF3 X0 X1 sk2) a) ∨ a = sk4 ∨ c = sk1 ∨ c = sk2 ∨ ¬(sP3 X0 X1 sk2) := resolve eq19057 eq21595 -- resolution 19057,21595
  have eq24683 (X0 X1 : G) : a = sk4 ∨ c = sk1 ∨ c = sk2 ∨ ¬(sP1 X0 X1 sk2) := resolve eq24681 eq21590 -- subsumption resolution 24681,21590
  have eq24684 (X0 X1 : G) : ¬(sP1 X0 X1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq24683 eq20652 -- subsumption resolution 24683,20652
  have eq24685 (X0 X1 : G) : a = sk4 ∨ c = sk1 ∨ c = sk2 ∨ ¬(sP3 X0 X1 sk2) := resolve eq24682 rule_def_3_2 -- subsumption resolution 24682,171
  have eq24686 (X0 X1 : G) : ¬(sP3 X0 X1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq24685 eq20652 -- subsumption resolution 24685,20652
  have eq24689 : c = sk2 ∨ c = sk1 ∨ (sP1 a c sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq24686 eq24016 -- resolution 24686,24016
  have eq24696 : c = sk2 ∨ c = sk1 ∨ (sP1 a c sk2) := resolve eq24689 rfl -- duplicate literal removal 24689
  have eq24700 : c = sk2 ∨ c = sk1 := resolve eq24696 eq24684 -- subsumption resolution 24696,24684
  have eq24730 : (sP0 a sk1 c) ∨ (old a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq24700.imp_left (fun h : c = sk2 ↦ superpose h eq16287)) -- superposition 16287,24700, 24700 into 16287, unify on (0).2 in 24700 and (0).3 in 16287
  have eq24789 : (sP0 a sk1 c) ∨ (old a sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq24730 rfl -- duplicate literal removal 24730
  have eq24801 : (sP0 a sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq24789 p4XY -- subsumption resolution 24789,133
  have eq24802 : c = sk1 ∨ a = sk1 := resolve eq24801 eq21589 -- subsumption resolution 24801,21589
  have eq24836 : (sP3 sk4 a c) ∨ (old sk4 a c) ∨ (sP2 sk4 a c) ∨ a = sk4 ∨ a = sk1 := Or.assoc4 (eq24802.imp_left (fun h : c = sk1 ↦ superpose h eq16228)) -- superposition 16228,24802, 24802 into 16228, unify on (0).2 in 24802 and (0).3 in 16228
  have eq24869 : (old sk4 a c) ∨ (sP2 sk4 a c) ∨ a = sk4 ∨ a = sk1 := resolve eq24836 eq229 -- subsumption resolution 24836,229
  have eq24870 : (sP2 sk4 a c) ∨ a = sk4 ∨ a = sk1 := resolve eq24869 p4XY -- subsumption resolution 24869,133
  have eq24871 : a = sk4 ∨ a = sk1 := resolve eq24870 eq21591 -- subsumption resolution 24870,21591
  have eq24989 : (new a a sk1) ∨ a = sk1 := eq24871.imp_left (fun h : a = sk4 ↦ superpose h eq12909) -- superposition 12909,24871, 24871 into 12909, unify on (0).2 in 24871 and (0).1 in 12909
  have eq25260 : a = sk1 ∨ ¬(new a sk1 c) ∨ a = sk1 := resolve eq24989 eq22665 -- resolution 24989,22665
  have eq25283 : ¬(new a sk1 c) ∨ a = sk1 := resolve eq25260 rfl -- duplicate literal removal 25260
  have eq29224 (X0 X1 : G) : ¬(old a (sF0 X0 X1 sk2) a) ∨ a = sk5 ∨ c = sk3 ∨ c = sk2 ∨ ¬(sP1 X0 X1 sk2) := resolve eq19113 rule_def_1_2 -- resolution 19113,160
  have eq29225 (X0 X1 : G) : ¬(old a (sF3 X0 X1 sk2) a) ∨ a = sk5 ∨ c = sk3 ∨ c = sk2 ∨ ¬(sP3 X0 X1 sk2) := resolve eq19113 eq21595 -- resolution 19113,21595
  have eq29226 (X0 X1 : G) : ¬(sP1 X0 X1 sk2) ∨ c = sk3 ∨ c = sk2 ∨ a = sk5 := resolve eq29224 eq21590 -- subsumption resolution 29224,21590
  have eq29227 (X0 X1 : G) : ¬(sP3 X0 X1 sk2) ∨ c = sk3 ∨ c = sk2 ∨ a = sk5 := resolve eq29225 rule_def_3_2 -- subsumption resolution 29225,171
  have eq29263 : c = sk3 ∨ c = sk2 ∨ a = sk5 ∨ c = sk2 ∨ (old a sk1 sk2) ∨ (sP1 a c sk2) := resolve eq29227 eq24249 -- resolution 29227,24249
  have eq29274 : c = sk3 ∨ c = sk2 ∨ a = sk5 ∨ (old a sk1 sk2) ∨ (sP1 a c sk2) := resolve eq29263 rfl -- duplicate literal removal 29263
  have eq29276 : (old a sk1 sk2) ∨ c = sk2 ∨ a = sk5 ∨ c = sk3 := resolve eq29274 eq29226 -- subsumption resolution 29274,29226
  have eq29325 : (old a c sk2) ∨ c = sk2 ∨ a = sk5 ∨ c = sk3 ∨ a = sk1 := Or.assoc4 (eq24802.imp_left (fun h : c = sk1 ↦ superpose h eq29276)) -- superposition 29276,24802, 24802 into 29276, unify on (0).2 in 24802 and (0).2 in 29276
  have eq29332 : a = sk5 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 := resolve eq29325 p4XZ -- subsumption resolution 29325,134
  have eq29351 : a ≠ sk4 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 := eq29332.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 198,29332, 29332 into 198, unify on (0).2 in 29332 and (0).2 in 198
  have eq29537 : c = sk3 ∨ c = sk2 ∨ a = sk1 := resolve eq29351 eq24871 -- subsumption resolution 29351,24871
  have eq29577 : (sP3 sk5 a c) ∨ (old sk5 a c) ∨ (sP2 sk5 a c) ∨ a = sk5 ∨ c = sk2 ∨ a = sk1 := Or.assoc4 (eq29537.imp_left (fun h : c = sk3 ↦ superpose h eq16276)) -- superposition 16276,29537, 29537 into 16276, unify on (0).2 in 29537 and (0).3 in 16276
  have eq29725 : (old sk5 a c) ∨ (sP2 sk5 a c) ∨ a = sk5 ∨ c = sk2 ∨ a = sk1 := resolve eq29577 eq229 -- subsumption resolution 29577,229
  have eq29726 : (sP2 sk5 a c) ∨ a = sk5 ∨ c = sk2 ∨ a = sk1 := resolve eq29725 p4XY -- subsumption resolution 29725,133
  have eq29727 : a = sk5 ∨ c = sk2 ∨ a = sk1 := resolve eq29726 eq21591 -- subsumption resolution 29726,21591
  have eq29739 : a ≠ sk4 ∨ c = sk2 ∨ a = sk1 := eq29727.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 198,29727, 29727 into 198, unify on (0).2 in 29727 and (0).2 in 198
  have eq29911 : c = sk2 ∨ a = sk1 := resolve eq29739 eq24871 -- subsumption resolution 29739,24871
  have eq29913 : (new a sk1 c) ∨ a = sk1 := eq29911.imp_left (fun h : c = sk2 ↦ superpose h eq12907) -- superposition 12907,29911, 29911 into 12907, unify on (0).2 in 29911 and (0).3 in 12907
  have eq30123 : a = sk1 := resolve eq29913 eq25283 -- subsumption resolution 29913,25283
  have eq30129 : ∀ (X0 : G) , ¬(new X0 a a) ∨ sk4 = X0 := Eq.mp (by simp only [eq30123, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12917 -- backward demodulation 12917,30123
  have eq30152 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq30123, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13153 -- backward demodulation 13153,30123
  have eq31021 : (old a sk1 sk2) ∨ c = sk2 := resolve eq30152 ac -- subsumption resolution 30152,130
  have eq31022 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq30123, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq31021 -- forward demodulation 31021,30123
  have eq31023 : c = sk2 := resolve eq31022 eq21588 -- subsumption resolution 31022,21588
  have eq31129 : a = c ∨ (new a c sk2) ∨ (old a sk3 sk2) ∨ a = sk3 := Eq.mp (by simp only [eq31023, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq23085 -- backward demodulation 23085,31023
  have eq31419 : (new a c sk2) ∨ (old a sk3 sk2) ∨ a = sk3 := resolve eq31129 ac -- subsumption resolution 31129,130
  have eq31420 : (new a c c) ∨ (old a sk3 sk2) ∨ a = sk3 := Eq.mp (by simp only [eq31023, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq31419 -- forward demodulation 31419,31023
  have eq31421 : (old a sk3 sk2) ∨ a = sk3 := resolve eq31420 eq23474 -- subsumption resolution 31420,23474
  have eq31422 : (old a sk3 c) ∨ a = sk3 := Eq.mp (by simp only [eq31023, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq31421 -- forward demodulation 31421,31023
  have eq31423 : a = sk3 := resolve eq31422 p4XY -- subsumption resolution 31422,133
  have eq31424 : (new sk5 a a) := Eq.mp (by simp only [eq31423, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12910 -- backward demodulation 12910,31423
  have eq33131 : sk4 = sk5 := resolve eq30129 eq31424 -- resolution 30129,31424
  subsumption preserve_4 eq33131 -- subsumption resolution 33131,198

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_13_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X1 X3 X4 ∨ new X1 X4 X0)) (prev_7 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X0 ∨ ¬ new X1 X3 X0 ∨ ¬ new X4 X1 X3 ∨ new X1 X2 X4)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_14 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X0 ∨ ¬ old X1 X0 X3 ∨ old X0 X2 X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old a X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z X3, a ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old a X3 a ∨ ¬ old b a X3 ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a (sF4 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X1 ∨ ¬ new X0 X4 X0 ∨ ¬ new X3 X0 X4 ∨ X2 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq202 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 155
  have eq203 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq202 rfl -- equality resolution 202
  have eq204 : (new a b c) := resolve eq203 rfl -- equality resolution 203
  have eq205 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old a X3 b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 159
  have eq206 (X2 X3 : G) : ¬(old a X3 b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq205 rfl -- equality resolution 205
  have eq212 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old b a X3) ∨ ¬(old a X3 a) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_5 rfl -- equality resolution 176
  have eq213 (X0 X3 : G) : (new X0 c a) ∨ ¬(old b a X3) ∨ ¬(old a X3 a) ∨ a ≠ X0 := resolve eq212 rfl -- equality resolution 212
  have eq214 (X3 : G) : ¬(old b a X3) ∨ (new a c a) ∨ ¬(old a X3 a) := resolve eq213 rfl -- equality resolution 213
  have eq218 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 162,137
  have eq222 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 173,146
  have eq228 (X0 X1 : G) : ¬(sP3 X0 X1 a) := resolve rule_def_3_4 p3 -- resolution 175,134
  have eq232 (X0 X1 : G) : ¬(sP3 X0 X1 c) := resolve rule_def_3_4 p4YZ -- resolution 175,137
  have eq239 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := resolve prev_0 preserve_0 -- resolution 184,197
  have eq255 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq206 rule_def_1_3 -- resolution 206,163
  have eq263 (X0 X1 X2 : G) : (new a c a) ∨ ¬(old a (sF4 X0 X1 X2) a) ∨ ¬(sP4 X0 X1 X2) := resolve eq214 rule_def_4_4 -- resolution 214,181
  have eq265 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (new a c a) := resolve eq263 rule_def_4_3 -- subsumption resolution 263,180
  have eq268 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 168,146
  have eq361 (X0 X1 : G) : ¬(new sk0 X1 sk3) ∨ (new sk0 sk1 X0) ∨ ¬(new X0 sk0 X1) := resolve prev_1 preserve_1 -- resolution 185,198
  have eq514 (X0 X1 : G) : ¬(new sk0 sk4 X1) ∨ (new sk0 X0 sk3) ∨ ¬(new X1 sk4 X1) ∨ ¬(new X1 sk0 X0) := resolve prev_7 preserve_3 -- resolution 191,200
  have eq536 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 183,197
  have eq537 : (sP4 sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP3 sk0 sk3 sk1) := resolve new_imp preserve_1 -- resolution 183,198
  have eq538 : (sP4 sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP3 sk0 sk4 sk0) := resolve new_imp preserve_2 -- resolution 183,199
  have eq539 : (sP4 sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP3 sk3 sk0 sk4) := resolve new_imp preserve_3 -- resolution 183,200
  have eq598 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq222 rule_def_3_3 -- resolution 222,174
  have eq599 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq598 rfl -- duplicate literal removal 598
  have eq651 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq255 rule_def_1_2 -- resolution 255,162
  have eq652 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq651 rfl -- duplicate literal removal 651
  have eq683 (X0 : G) : (new sk0 X0 sk3) ∨ ¬(new sk0 sk4 sk0) ∨ ¬(new sk0 sk0 X0) := resolve eq514 preserve_2 -- resolution 514,199
  have eq684 (X0 : G) : ¬(new sk0 sk0 X0) ∨ (new sk0 X0 sk3) := resolve eq683 preserve_2 -- subsumption resolution 683,199
  have eq710 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq268 rule_def_2_4 -- resolution 268,169
  have eq713 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq710 rfl -- duplicate literal removal 710
  have eq917 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq536 rule_def_4_0 -- resolution 536,177
  have eq918 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq536 rule_def_4_1 -- resolution 536,178
  have eq929 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq917 rule_def_0_0 -- subsumption resolution 917,156
  have eq930 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq929 rule_def_1_0 -- subsumption resolution 929,160
  have eq931 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq918 rule_def_1_1 -- subsumption resolution 918,161
  have eq932 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq931 rule_def_3_1 -- subsumption resolution 931,172
  have eq935 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq930 rule_def_3_0 -- resolution 930,171
  have eq941 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq930 eq599 -- resolution 930,599
  have eq945 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq935 rule_def_2_0 -- subsumption resolution 935,165
  have eq947 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq941 eq713 -- subsumption resolution 941,713
  have eq949 : (sP2 sk0 sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP3 sk0 sk3 sk1) ∨ a = sk0 := resolve eq537 rule_def_4_0 -- resolution 537,177
  have eq950 : (sP2 sk0 sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP3 sk0 sk3 sk1) ∨ c = sk3 := resolve eq537 rule_def_4_1 -- resolution 537,178
  have eq951 : (sP3 sk0 sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk1 := resolve eq537 rule_def_4_2 -- resolution 537,179
  have eq961 : (sP2 sk0 sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP3 sk0 sk3 sk1) ∨ a = sk0 := resolve eq949 rule_def_0_0 -- subsumption resolution 949,156
  have eq962 : (sP3 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk0 := resolve eq961 rule_def_1_0 -- subsumption resolution 961,160
  have eq963 : (sP2 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP3 sk0 sk3 sk1) ∨ c = sk3 := resolve eq950 rule_def_1_1 -- subsumption resolution 950,161
  have eq964 : (sP2 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ c = sk3 := resolve eq963 rule_def_3_1 -- subsumption resolution 963,172
  have eq967 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk0 ∨ sk2 = X0 ∨ a = sk0 := resolve eq945 old_0 -- resolution 945,138
  have eq983 : (sP2 sk0 sk4 sk0) ∨ (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP3 sk0 sk4 sk0) ∨ a = sk0 := resolve eq538 rule_def_4_0 -- resolution 538,177
  have eq984 : (sP2 sk0 sk4 sk0) ∨ (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP3 sk0 sk4 sk0) ∨ c = sk4 := resolve eq538 rule_def_4_1 -- resolution 538,178
  have eq987 : (sP3 sk0 sk4 sk0) ∨ (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := resolve eq538 eq265 -- resolution 538,265
  have eq995 : (sP2 sk0 sk4 sk0) ∨ (sP1 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP3 sk0 sk4 sk0) ∨ a = sk0 := resolve eq983 rule_def_0_0 -- subsumption resolution 983,156
  have eq996 : (sP3 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ a = sk0 := resolve eq995 rule_def_1_0 -- subsumption resolution 995,160
  have eq997 : (sP2 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP3 sk0 sk4 sk0) ∨ c = sk4 := resolve eq984 rule_def_1_1 -- subsumption resolution 984,161
  have eq998 : (sP2 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ c = sk4 := resolve eq997 rule_def_3_1 -- subsumption resolution 997,172
  have eq1001 (X0 : G) : ¬(old sk0 sk1 X0) ∨ a = b ∨ sk2 = X0 ∨ a = sk0 := resolve eq947 old_0 -- resolution 947,138
  have eq1017 : (sP2 sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP3 sk3 sk0 sk4) ∨ a = sk3 := resolve eq539 rule_def_4_0 -- resolution 539,177
  have eq1018 : (sP2 sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP3 sk3 sk0 sk4) ∨ c = sk0 := resolve eq539 rule_def_4_1 -- resolution 539,178
  have eq1019 : (sP3 sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk4 := resolve eq539 rule_def_4_2 -- resolution 539,179
  have eq1029 : (sP2 sk3 sk0 sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP3 sk3 sk0 sk4) ∨ a = sk3 := resolve eq1017 rule_def_0_0 -- subsumption resolution 1017,156
  have eq1030 : (sP3 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk3 := resolve eq1029 rule_def_1_0 -- subsumption resolution 1029,160
  have eq1031 : (sP2 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP3 sk3 sk0 sk4) ∨ c = sk0 := resolve eq1018 rule_def_1_1 -- subsumption resolution 1018,161
  have eq1032 : (sP2 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ c = sk0 := resolve eq1031 rule_def_3_1 -- subsumption resolution 1031,172
  have eq1149 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b := resolve eq932 eq713 -- resolution 932,713
  have eq1151 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq932 rule_def_2_2 -- resolution 932,167
  have eq1154 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1151 rule_def_0_2 -- subsumption resolution 1151,158
  have eq1162 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq1154 old_0 -- resolution 1154,138
  have eq1249 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1149 rule_def_0_1 -- resolution 1149,157
  have eq1336 : (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq962 rule_def_3_0 -- resolution 962,171
  have eq1342 : (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk0 ∨ a = b := resolve eq962 eq599 -- resolution 962,599
  have eq1346 : (old sk0 sk3 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq1336 rule_def_2_0 -- subsumption resolution 1336,165
  have eq1348 : (old sk0 sk3 sk1) ∨ a = sk0 ∨ a = b := resolve eq1342 eq713 -- subsumption resolution 1342,713
  have eq1499 : (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ c = sk3 ∨ c = sk1 := resolve eq964 rule_def_2_2 -- resolution 964,167
  have eq1502 : (old sk0 sk3 sk1) ∨ c = sk3 ∨ c = sk1 := resolve eq1499 rule_def_0_2 -- subsumption resolution 1499,158
  have eq1634 : (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ a = sk0 ∨ a = b := resolve eq996 eq599 -- resolution 996,599
  have eq1640 : (old sk0 sk4 sk0) ∨ a = sk0 ∨ a = b := resolve eq1634 eq713 -- subsumption resolution 1634,713
  have eq1791 : (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ c = sk4 ∨ c = sk0 := resolve eq998 rule_def_2_2 -- resolution 998,167
  have eq1794 : (old sk0 sk4 sk0) ∨ c = sk4 ∨ c = sk0 := resolve eq1791 rule_def_0_2 -- subsumption resolution 1791,158
  have eq1816 : (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk3 ∨ b = sk3 := resolve eq1030 rule_def_3_0 -- resolution 1030,171
  have eq1822 : (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk3 ∨ a = b := resolve eq1030 eq599 -- resolution 1030,599
  have eq1826 : (old sk3 sk0 sk4) ∨ a = sk3 ∨ b = sk3 := resolve eq1816 rule_def_2_0 -- subsumption resolution 1816,165
  have eq1828 : (old sk3 sk0 sk4) ∨ a = sk3 ∨ a = b := resolve eq1822 eq713 -- subsumption resolution 1822,713
  have eq1846 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ c = sk0 ∨ a = b := resolve eq1032 eq713 -- resolution 1032,713
  have eq1848 : (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ c = sk0 ∨ c = sk4 := resolve eq1032 rule_def_2_2 -- resolution 1032,167
  have eq1851 : (old sk3 sk0 sk4) ∨ c = sk0 ∨ c = sk4 := resolve eq1848 rule_def_0_2 -- subsumption resolution 1848,158
  have eq1879 (X0 : G) : c = sk0 ∨ c = sk4 ∨ (old sk0 X0 sk0) ∨ ¬(old sk0 sk4 sk0) ∨ ¬(old sk0 sk3 X0) := resolve eq1851 old_14 -- resolution 1851,152
  have eq1885 (X0 : G) : ¬(old sk0 sk3 X0) ∨ c = sk4 ∨ (old sk0 X0 sk0) ∨ c = sk0 := resolve eq1879 eq1794 -- subsumption resolution 1879,1794
  have eq2417 : (old sk0 sk1 sk0) ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq1885 eq1346 -- resolution 1885,1346
  have eq2418 : (old sk0 sk1 sk0) ∨ c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq1885 eq1348 -- resolution 1885,1348
  have eq2421 : c = sk4 ∨ (old sk0 sk1 sk0) ∨ c = sk0 ∨ c = sk3 ∨ c = sk1 := resolve eq1885 eq1502 -- resolution 1885,1502
  have eq3603 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 ∨ b = sk0 ∨ sk0 = sk2 ∨ a = sk0 := resolve eq2417 eq967 -- resolution 2417,967
  have eq3632 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 ∨ sk0 = sk2 := resolve eq3603 rfl -- duplicate literal removal 3603
  have eq3633 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3632 preserve_4 -- subsumption resolution 3632,201
  have eq3651 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := Or.assoc6 (eq3633.imp_left (fun h : c = sk4 ↦ superpose h eq538)) -- superposition 538,3633, 3633 into 538, unify on (0).2 in 3633 and (0).2 in 538
  have eq3720 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3651 p4XZ -- subsumption resolution 3651,136
  have eq3721 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3720 rule_def_2_0 -- subsumption resolution 3720,165
  have eq3722 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3721 rule_def_3_0 -- subsumption resolution 3721,171
  have eq3723 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3722 rule_def_0_0 -- subsumption resolution 3722,156
  have eq3724 : (sP4 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3723 rule_def_1_0 -- subsumption resolution 3723,160
  have eq3725 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq3724 rule_def_4_0 -- subsumption resolution 3724,177
  have eq3895 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq3725 trans_resol -- equality factoring 3725
  have eq4538 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ a = b ∨ sk0 = sk2 ∨ a = sk0 := resolve eq2418 eq1001 -- resolution 2418,1001
  have eq4567 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ sk0 = sk2 := resolve eq4538 rfl -- duplicate literal removal 4538
  have eq4569 : c = sk4 ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq4567 preserve_4 -- subsumption resolution 4567,201
  have eq4570 : c = sk4 ∨ c = sk0 ∨ a = sk0 := resolve eq4569 eq3895 -- subsumption resolution 4569,3895
  have eq4608 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq4570.imp_left (fun h : c = sk4 ↦ superpose h eq1640)) -- superposition 1640,4570, 4570 into 1640, unify on (0).2 in 4570 and (0).2 in 1640
  have eq4691 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 := resolve eq4608 rfl -- duplicate literal removal 4608
  have eq4712 : a = sk0 ∨ a = b ∨ c = sk0 := resolve eq4691 p4XZ -- subsumption resolution 4691,136
  have eq4713 : c = sk0 ∨ a = sk0 := resolve eq4712 eq3895 -- subsumption resolution 4712,3895
  have eq4783 : (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq4713.imp_left (fun h : c = sk0 ↦ superpose h eq945)) -- superposition 945,4713, 4713 into 945, unify on (0).2 in 4713 and (0).1 in 945
  have eq4920 : a = c ∨ c = b ∨ a = sk0 := resolve eq4783 p4YZ -- subsumption resolution 4783,137
  have eq4921 : c = b ∨ a = sk0 := resolve eq4920 ac -- subsumption resolution 4920,132
  have eq4922 : a = sk0 := resolve eq4921 bc -- subsumption resolution 4921,133
  have eq4927 : a ≠ sk2 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_4 -- backward demodulation 201,4922
  have eq4928 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ sk2 = X0 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq239 -- backward demodulation 239,4922
  have eq4945 : ∀ (X0 X1 : G) , ¬(new X0 a X1) ∨ ¬(new sk0 X1 sk3) ∨ (new sk0 sk1 X0) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq361 -- backward demodulation 361,4922
  have eq5000 : ∀ (X0 : G) , ¬(new a a X0) ∨ (new sk0 X0 sk3) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq684 -- backward demodulation 684,4922
  have eq5111 : (sP3 a sk3 sk1) ∨ (sP1 sk0 sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq951 -- backward demodulation 951,4922
  have eq5127 : (sP3 a sk4 a) ∨ (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq987 -- backward demodulation 987,4922
  have eq5142 : (sP3 sk3 a sk4) ∨ (sP1 sk3 sk0 sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1019 -- backward demodulation 1019,4922
  have eq5185 : ∀ (X0 : G) , ¬(old a sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1162 -- backward demodulation 1162,4922
  have eq5203 : (old a sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1249 -- backward demodulation 1249,4922
  have eq5427 : (old sk3 a sk4) ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1826 -- backward demodulation 1826,4922
  have eq5429 : (old sk3 a sk4) ∨ a = sk3 ∨ a = b := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1828 -- backward demodulation 1828,4922
  have eq5446 : (sP0 sk3 a sk4) ∨ (old sk3 sk0 sk4) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1846 -- backward demodulation 1846,4922
  have eq5691 : a = c ∨ c = sk4 ∨ (old sk0 sk1 sk0) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2421 -- backward demodulation 2421,4922
  have eq6207 : ∀ (X0 X1 : G) , ¬(new a X1 sk3) ∨ ¬(new X0 a X1) ∨ (new sk0 sk1 X0) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4945 -- forward demodulation 4945,4922
  have eq6208 : ∀ (X0 X1 : G) , ¬(new a X1 sk3) ∨ (new a sk1 X0) ∨ ¬(new X0 a X1) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6207 -- forward demodulation 6207,4922
  have eq6272 : ∀ (X0 : G) , ¬(new a a X0) ∨ (new a X0 sk3) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5000 -- forward demodulation 5000,4922
  have eq6441 : (sP1 a sk3 sk1) ∨ (sP3 a sk3 sk1) ∨ (sP0 sk0 sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5111 -- forward demodulation 5111,4922
  have eq6442 : (sP0 a sk3 sk1) ∨ (sP1 a sk3 sk1) ∨ (sP3 a sk3 sk1) ∨ (old sk0 sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6441 -- forward demodulation 6441,4922
  have eq6443 : (old a sk3 sk1) ∨ (sP0 a sk3 sk1) ∨ (sP1 a sk3 sk1) ∨ (sP3 a sk3 sk1) ∨ (sP2 sk0 sk3 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6442 -- forward demodulation 6442,4922
  have eq6444 : (sP3 a sk3 sk1) ∨ (old a sk3 sk1) ∨ (sP0 a sk3 sk1) ∨ (sP1 a sk3 sk1) ∨ (sP2 a sk3 sk1) ∨ a = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6443 -- forward demodulation 6443,4922
  have eq6485 : (sP1 sk0 sk4 sk0) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := resolve eq5127 eq228 -- subsumption resolution 5127,228
  have eq6486 : (sP1 a sk4 a) ∨ (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6485 -- forward demodulation 6485,4922
  have eq6487 : (sP0 sk0 sk4 sk0) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := resolve eq6486 eq652 -- subsumption resolution 6486,652
  have eq6488 : (sP0 a sk4 a) ∨ (old sk0 sk4 sk0) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6487 -- forward demodulation 6487,4922
  have eq6489 : (old a sk4 a) ∨ (sP0 a sk4 a) ∨ (sP2 sk0 sk4 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6488 -- forward demodulation 6488,4922
  have eq6490 : (sP2 a sk4 a) ∨ (old a sk4 a) ∨ (sP0 a sk4 a) ∨ (new a c a) := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6489 -- forward demodulation 6489,4922
  have eq6534 : (sP1 sk3 a sk4) ∨ (sP3 sk3 a sk4) ∨ (sP0 sk3 sk0 sk4) ∨ (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5142 -- forward demodulation 5142,4922
  have eq6535 : (sP0 sk3 a sk4) ∨ (sP1 sk3 a sk4) ∨ (sP3 sk3 a sk4) ∨ (old sk3 sk0 sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6534 -- forward demodulation 6534,4922
  have eq6536 : (old sk3 a sk4) ∨ (sP0 sk3 a sk4) ∨ (sP1 sk3 a sk4) ∨ (sP3 sk3 a sk4) ∨ (sP2 sk3 sk0 sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6535 -- forward demodulation 6535,4922
  have eq6537 : (sP3 sk3 a sk4) ∨ (old sk3 a sk4) ∨ (sP0 sk3 a sk4) ∨ (sP1 sk3 a sk4) ∨ (sP2 sk3 a sk4) ∨ a = sk4 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6536 -- forward demodulation 6536,4922
  have eq6755 : (old sk3 sk0 sk4) ∨ c = sk0 ∨ a = b := resolve eq5446 rule_def_0_1 -- subsumption resolution 5446,157
  have eq6756 : (old sk3 a sk4) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6755 -- forward demodulation 6755,4922
  have eq6757 : a = c ∨ (old sk3 a sk4) ∨ a = b := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6756 -- forward demodulation 6756,4922
  have eq6758 : (old sk3 a sk4) ∨ a = b := resolve eq6757 ac -- subsumption resolution 6757,132
  have eq7297 : c = sk4 ∨ (old sk0 sk1 sk0) ∨ c = sk3 ∨ c = sk1 := resolve eq5691 ac -- subsumption resolution 5691,132
  have eq7298 : (old a sk1 a) ∨ c = sk4 ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq4922, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7297 -- forward demodulation 7297,4922
  have eq8482 : (old a sk4 a) ∨ (sP0 a sk4 a) ∨ (new a c a) ∨ a = c := resolve eq6490 rule_def_2_2 -- resolution 6490,167
  have eq8488 : (sP0 a sk4 a) ∨ (old a sk4 a) ∨ (new a c a) := resolve eq8482 ac -- subsumption resolution 8482,132
  have eq8489 : (old a sk4 a) ∨ (new a c a) ∨ a = c := resolve eq8488 rule_def_0_2 -- resolution 8488,158
  have eq8492 : (new a c a) ∨ (old a sk4 a) := resolve eq8489 ac -- subsumption resolution 8489,132
  have eq8709 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq7298 eq5185 -- resolution 7298,5185
  have eq8727 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ a = sk2 := resolve eq8709 rfl -- duplicate literal removal 8709
  have eq8728 : c = sk4 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq8727 eq4927 -- subsumption resolution 8727,4927
  have eq8779 : (old sk3 a c) ∨ a = b ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Or.assoc2 (eq8728.imp_left (fun h : c = sk4 ↦ superpose h eq6758)) -- superposition 6758,8728, 8728 into 6758, unify on (0).2 in 8728 and (0).3 in 6758
  have eq8804 : c = sk3 ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq8779 p4XY -- subsumption resolution 8779,135
  have eq8843 : (old c a sk4) ∨ a = c ∨ c = b ∨ a = b ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq8804.imp_left (fun h : c = sk3 ↦ superpose h eq5427)) -- superposition 5427,8804, 8804 into 5427, unify on (0).2 in 8804 and (0).1 in 5427
  have eq8881 : a = c ∨ c = b ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq8843 p4YZ -- subsumption resolution 8843,137
  have eq8882 : c = b ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq8881 ac -- subsumption resolution 8881,132
  have eq8883 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq8882 bc -- subsumption resolution 8882,133
  have eq8914 : (old a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 ∨ c = sk1 ∨ a = b := Or.assoc4 (eq8883.imp_left (fun h : c = sk2 ↦ superpose h eq5203)) -- superposition 5203,8883, 8883 into 5203, unify on (0).2 in 8883 and (0).3 in 5203
  have eq8926 : (old a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq8914 rfl -- duplicate literal removal 8914
  have eq8927 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq8926 p4XY -- subsumption resolution 8926,135
  have eq8972 : (old a b a) ∨ c = sk4 ∨ c = sk3 ∨ c = b ∨ a = b ∨ c = sk1 := Or.assoc4 (eq8927.imp_left (fun h : b = sk1 ↦ superpose h eq7298)) -- superposition 7298,8927, 8927 into 7298, unify on (0).2 in 8927 and (0).2 in 7298
  have eq9002 : c = sk4 ∨ c = sk3 ∨ c = b ∨ a = b ∨ c = sk1 := resolve eq8972 p3 -- subsumption resolution 8972,134
  have eq9003 : c = sk4 ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9002 bc -- subsumption resolution 9002,133
  have eq9127 : (sP3 sk3 a c) ∨ (old sk3 a c) ∨ (sP0 sk3 a c) ∨ (sP1 sk3 a c) ∨ (sP2 sk3 a c) ∨ a = c ∨ c = sk3 ∨ a = b ∨ c = sk1 := Or.assoc6 (eq9003.imp_left (fun h : c = sk4 ↦ superpose h eq6537)) -- superposition 6537,9003, 9003 into 6537, unify on (0).2 in 9003 and (0).3 in 6537
  have eq9162 : (old sk3 a c) ∨ (sP0 sk3 a c) ∨ (sP1 sk3 a c) ∨ (sP2 sk3 a c) ∨ a = c ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9127 eq232 -- subsumption resolution 9127,232
  have eq9163 : (sP0 sk3 a c) ∨ (sP1 sk3 a c) ∨ (sP2 sk3 a c) ∨ a = c ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9162 p4XY -- subsumption resolution 9162,135
  have eq9164 : (sP0 sk3 a c) ∨ (sP2 sk3 a c) ∨ a = c ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9163 eq218 -- subsumption resolution 9163,218
  have eq9165 : (sP0 sk3 a c) ∨ (sP2 sk3 a c) ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9164 ac -- subsumption resolution 9164,132
  have eq9166 : (sP2 sk3 a c) ∨ c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9165 rule_def_0_1 -- subsumption resolution 9165,157
  have eq9167 : c = sk3 ∨ a = b ∨ c = sk1 := resolve eq9166 eq713 -- subsumption resolution 9166,713
  have eq9189 : (old c a sk4) ∨ a = c ∨ c = b ∨ a = b ∨ c = sk1 := Or.assoc3 (eq9167.imp_left (fun h : c = sk3 ↦ superpose h eq5427)) -- superposition 5427,9167, 9167 into 5427, unify on (0).2 in 9167 and (0).1 in 5427
  have eq9231 : a = c ∨ c = b ∨ a = b ∨ c = sk1 := resolve eq9189 p4YZ -- subsumption resolution 9189,137
  have eq9232 : c = b ∨ a = b ∨ c = sk1 := resolve eq9231 ac -- subsumption resolution 9231,132
  have eq9233 : c = sk1 ∨ a = b := resolve eq9232 bc -- subsumption resolution 9232,133
  have eq9244 (X0 : G) : ¬(new a c X0) ∨ sk2 = X0 ∨ a = b := Or.assoc2 (eq9233.imp_left (fun h : c = sk1 ↦ superpose h eq4928)) -- superposition 4928,9233, 9233 into 4928, unify on (0).2 in 9233 and (0).2 in 4928
  have eq9272 : (sP3 a sk3 c) ∨ (old a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ a = b := Or.assoc6 (eq9233.imp_left (fun h : c = sk1 ↦ superpose h eq6444)) -- superposition 6444,9233, 9233 into 6444, unify on (0).2 in 9233 and (0).3 in 6444
  have eq9300 : (old a sk3 c) ∨ (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ a = b := resolve eq9272 eq232 -- subsumption resolution 9272,232
  have eq9301 : (sP0 a sk3 c) ∨ (sP1 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ a = b := resolve eq9300 p4XY -- subsumption resolution 9300,135
  have eq9302 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = c ∨ a = b := resolve eq9301 eq218 -- subsumption resolution 9301,218
  have eq9303 : (sP0 a sk3 c) ∨ (sP2 a sk3 c) ∨ a = b := resolve eq9302 ac -- subsumption resolution 9302,132
  have eq9304 : (sP0 a sk3 c) ∨ a = b := resolve eq9303 rule_def_2_0 -- subsumption resolution 9303,165
  have eq9366 : b = sk3 ∨ a = b := resolve eq9304 rule_def_0_1 -- resolution 9304,157
  have eq9400 : (old b a sk4) ∨ a = b ∨ a = b ∨ a = b := Or.assoc3 (eq9366.imp_left (fun h : b = sk3 ↦ superpose h eq5429)) -- superposition 5429,9366, 9366 into 5429, unify on (0).2 in 9366 and (0).1 in 5429
  have eq9452 : (old b a sk4) ∨ a = b := resolve eq9400 rfl -- duplicate literal removal 9400
  have eq9548 : a = b ∨ (new a c a) ∨ ¬(old a sk4 a) := resolve eq9452 eq214 -- resolution 9452,214
  have eq9585 : (new a c a) ∨ a = b := resolve eq9548 eq8492 -- subsumption resolution 9548,8492
  have eq9772 : a = sk2 ∨ a = b ∨ a = b := resolve eq9244 eq9585 -- resolution 9244,9585
  have eq9778 : a = sk2 ∨ a = b := resolve eq9772 rfl -- duplicate literal removal 9772
  have eq9779 : a = b := resolve eq9778 eq4927 -- subsumption resolution 9778,4927
  have eq9790 : (new a a c) := Eq.mp (by simp only [eq9779, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq204 -- backward demodulation 204,9779
  have eq10559 : (new a c sk3) := resolve eq9790 eq6272 -- resolution 9790,6272
  have eq10597 (X0 : G) : ¬(new X0 a c) ∨ (new a sk1 X0) := resolve eq10559 eq6208 -- resolution 10559,6208
  have eq10871 : (new a sk1 a) := resolve eq10597 eq9790 -- resolution 10597,9790
  have eq10878 : a = sk2 := resolve eq10871 eq4928 -- resolution 10871,4928
  subsumption eq4927 eq10878 -- subsumption resolution 10878,4927

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_14_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_4 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X3 X0 X4 ∨ ¬ new X3 X1 X2 ∨ new X0 X3 X4)) (prev_7 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X0 ∨ ¬ new X1 X3 X0 ∨ ¬ new X4 X1 X3 ∨ new X1 X2 X4)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_14 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X3 X0 ∨ ¬ old X1 X0 X3 ∨ old X0 X2 X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, a ≠ X ∨ c ≠ Y ∨ ¬ old Z a X2 ∨ ¬ old a X2 b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old a (sF0 X Y Z) b ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z X3, a ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old a X3 a ∨ ¬ old b a X3 ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a (sF4 X Y Z) a ∨ ¬sP4 X Y Z) (rule_def_4_4 : ∀ (X Y Z : G), old b a (sF4 X Y Z) ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X0 ∨ ¬ new X1 X0 X3 ∨ new X0 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq203 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 156
  have eq204 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq203 rfl -- equality resolution 203
  have eq205 : (new a b c) := resolve eq204 rfl -- equality resolution 204
  have eq206 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old a X3 b) ∨ ¬(old X2 a X3) ∨ a ≠ X0 := resolve imp_new_2 rfl -- equality resolution 160
  have eq207 (X2 X3 : G) : ¬(old a X3 b) ∨ (new a c X2) ∨ ¬(old X2 a X3) := resolve eq206 rfl -- equality resolution 206
  have eq213 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old b a X3) ∨ ¬(old a X3 a) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_5 rfl -- equality resolution 177
  have eq214 (X0 X3 : G) : (new X0 c a) ∨ ¬(old b a X3) ∨ ¬(old a X3 a) ∨ a ≠ X0 := resolve eq213 rfl -- equality resolution 213
  have eq215 (X3 : G) : ¬(old b a X3) ∨ (new a c a) ∨ ¬(old a X3 a) := resolve eq214 rfl -- equality resolution 214
  have eq223 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 174,147
  have eq229 (X0 X1 : G) : ¬(sP3 X0 X1 a) := resolve rule_def_3_4 p3 -- resolution 176,135
  have eq240 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := resolve prev_0 preserve_0 -- resolution 185,199
  have eq255 (X0 X1 X2 X3 : G) : ¬(old X0 a (sF0 X1 X2 X3)) ∨ (new a c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq207 rule_def_1_3 -- resolution 207,164
  have eq263 (X0 X1 X2 : G) : (new a c a) ∨ ¬(old a (sF4 X0 X1 X2) a) ∨ ¬(sP4 X0 X1 X2) := resolve eq215 rule_def_4_4 -- resolution 215,182
  have eq265 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) ∨ (new a c a) := resolve eq263 rule_def_4_3 -- subsumption resolution 263,181
  have eq268 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 169,147
  have eq367 (X0 X1 : G) : ¬(new sk1 X0 X1) ∨ (new X0 sk1 X1) ∨ ¬(new X0 sk0 sk3) := resolve prev_4 preserve_2 -- resolution 189,201
  have eq529 (X0 X1 : G) : ¬(new sk0 sk3 X1) ∨ (new sk0 X0 sk1) ∨ ¬(new X1 sk3 X1) ∨ ¬(new X1 sk0 X0) := resolve prev_7 preserve_2 -- resolution 192,201
  have eq538 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 184,199
  have eq539 : (sP4 sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP3 sk0 sk3 sk0) := resolve new_imp preserve_1 -- resolution 184,200
  have eq540 : (sP4 sk1 sk0 sk3) ∨ (sP2 sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP3 sk1 sk0 sk3) := resolve new_imp preserve_2 -- resolution 184,201
  have eq552 : ¬(new sk0 sk0 sk3) ∨ (new sk0 sk1 sk3) := resolve eq367 preserve_2 -- resolution 367,201
  have eq590 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq223 rule_def_3_3 -- resolution 223,175
  have eq591 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq590 rfl -- duplicate literal removal 590
  have eq647 (X0 X1 X2 : G) : (new a c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq255 rule_def_1_2 -- resolution 255,163
  have eq648 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new a c X0) := resolve eq647 rfl -- duplicate literal removal 647
  have eq677 (X0 : G) : (new sk0 X0 sk1) ∨ ¬(new sk0 sk3 sk0) ∨ ¬(new sk0 sk0 X0) := resolve eq529 preserve_1 -- resolution 529,200
  have eq678 (X0 : G) : ¬(new sk0 sk0 X0) ∨ (new sk0 X0 sk1) := resolve eq677 preserve_1 -- subsumption resolution 677,200
  have eq706 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq268 rule_def_2_4 -- resolution 268,170
  have eq709 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq706 rfl -- duplicate literal removal 706
  have eq883 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq538 rule_def_4_0 -- resolution 538,178
  have eq884 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq538 rule_def_4_1 -- resolution 538,179
  have eq896 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq883 rule_def_0_0 -- subsumption resolution 883,157
  have eq897 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq896 rule_def_1_0 -- subsumption resolution 896,161
  have eq898 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq884 rule_def_1_1 -- subsumption resolution 884,162
  have eq899 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq898 rule_def_3_1 -- subsumption resolution 898,173
  have eq902 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq897 rule_def_3_0 -- resolution 897,172
  have eq908 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq897 eq591 -- resolution 897,591
  have eq912 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq902 rule_def_2_0 -- subsumption resolution 902,166
  have eq914 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ a = b := resolve eq908 eq709 -- subsumption resolution 908,709
  have eq916 : (sP2 sk0 sk3 sk0) ∨ (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP3 sk0 sk3 sk0) ∨ a = sk0 := resolve eq539 rule_def_4_0 -- resolution 539,178
  have eq917 : (sP2 sk0 sk3 sk0) ∨ (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP3 sk0 sk3 sk0) ∨ c = sk3 := resolve eq539 rule_def_4_1 -- resolution 539,179
  have eq920 : (sP3 sk0 sk3 sk0) ∨ (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := resolve eq539 eq265 -- resolution 539,265
  have eq929 : (sP2 sk0 sk3 sk0) ∨ (sP1 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP3 sk0 sk3 sk0) ∨ a = sk0 := resolve eq916 rule_def_0_0 -- subsumption resolution 916,157
  have eq930 : (sP3 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ a = sk0 := resolve eq929 rule_def_1_0 -- subsumption resolution 929,161
  have eq931 : (sP2 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP3 sk0 sk3 sk0) ∨ c = sk3 := resolve eq917 rule_def_1_1 -- subsumption resolution 917,162
  have eq932 : (sP2 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ c = sk3 := resolve eq931 rule_def_3_1 -- subsumption resolution 931,173
  have eq950 : (sP2 sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP3 sk1 sk0 sk3) ∨ a = sk1 := resolve eq540 rule_def_4_0 -- resolution 540,178
  have eq951 : (sP2 sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP3 sk1 sk0 sk3) ∨ c = sk0 := resolve eq540 rule_def_4_1 -- resolution 540,179
  have eq963 : (sP2 sk1 sk0 sk3) ∨ (sP1 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP3 sk1 sk0 sk3) ∨ a = sk1 := resolve eq950 rule_def_0_0 -- subsumption resolution 950,157
  have eq964 : (sP3 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP2 sk1 sk0 sk3) ∨ a = sk1 := resolve eq963 rule_def_1_0 -- subsumption resolution 963,161
  have eq965 : (sP2 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ (sP3 sk1 sk0 sk3) ∨ c = sk0 := resolve eq951 rule_def_1_1 -- subsumption resolution 951,162
  have eq966 : (sP2 sk1 sk0 sk3) ∨ (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ c = sk0 := resolve eq965 rule_def_3_1 -- subsumption resolution 965,173
  have eq1094 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b := resolve eq899 eq709 -- resolution 899,709
  have eq1096 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq899 rule_def_2_2 -- resolution 899,168
  have eq1097 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := resolve eq899 rule_def_2_1 -- resolution 899,167
  have eq1099 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq1096 rule_def_0_2 -- subsumption resolution 1096,159
  have eq1194 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq1094 rule_def_0_1 -- resolution 1094,158
  have eq1284 : (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ a = sk0 ∨ a = b := resolve eq930 eq591 -- resolution 930,591
  have eq1290 : (old sk0 sk3 sk0) ∨ a = sk0 ∨ a = b := resolve eq1284 eq709 -- subsumption resolution 1284,709
  have eq1451 : (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ c = sk3 ∨ c = sk0 := resolve eq932 rule_def_2_2 -- resolution 932,168
  have eq1454 : (old sk0 sk3 sk0) ∨ c = sk3 ∨ c = sk0 := resolve eq1451 rule_def_0_2 -- subsumption resolution 1451,159
  have eq1586 : (old sk1 sk0 sk3) ∨ (sP2 sk1 sk0 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq964 rule_def_3_0 -- resolution 964,172
  have eq1587 : (sP2 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk0 := resolve eq964 rule_def_3_1 -- resolution 964,173
  have eq1592 : (old sk1 sk0 sk3) ∨ (sP2 sk1 sk0 sk3) ∨ a = sk1 ∨ a = b := resolve eq964 eq591 -- resolution 964,591
  have eq1596 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq1586 rule_def_2_0 -- subsumption resolution 1586,166
  have eq1598 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ a = b := resolve eq1592 eq709 -- subsumption resolution 1592,709
  have eq1685 : (old sk1 sk0 sk3) ∨ a = sk1 ∨ c = sk0 ∨ c = sk3 := resolve eq1587 rule_def_2_2 -- resolution 1587,168
  have eq1716 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ c = sk0 ∨ a = b := resolve eq966 eq709 -- resolution 966,709
  have eq1718 : (sP0 sk1 sk0 sk3) ∨ (old sk1 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq966 rule_def_2_2 -- resolution 966,168
  have eq1721 : (old sk1 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq1718 rule_def_0_2 -- subsumption resolution 1718,159
  have eq1738 (X0 : G) : c = sk0 ∨ c = sk3 ∨ (old sk0 X0 sk0) ∨ ¬(old sk0 sk3 sk0) ∨ ¬(old sk0 sk1 X0) := resolve eq1721 old_14 -- resolution 1721,153
  have eq1744 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk3 ∨ (old sk0 X0 sk0) ∨ c = sk0 := resolve eq1738 eq1454 -- subsumption resolution 1738,1454
  have eq1937 : (old sk0 sk2 sk0) ∨ c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq1744 eq912 -- resolution 1744,912
  have eq1938 : (old sk0 sk2 sk0) ∨ c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq1744 eq914 -- resolution 1744,914
  have eq1941 : c = sk3 ∨ (old sk0 sk2 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq1744 eq1099 -- resolution 1744,1099
  have eq3004 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 ∨ (new sk0 sk2 sk0) := resolve eq1937 imp_new_0 -- resolution 1937,155
  have eq3006 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3004 preserve_3 -- subsumption resolution 3004,202
  have eq3025 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := Or.assoc6 (eq3006.imp_left (fun h : c = sk3 ↦ superpose h eq539)) -- superposition 539,3006, 3006 into 539, unify on (0).2 in 3006 and (0).2 in 539
  have eq3092 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3025 p4XZ -- subsumption resolution 3025,137
  have eq3093 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3092 rule_def_2_0 -- subsumption resolution 3092,166
  have eq3094 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3093 rule_def_3_0 -- subsumption resolution 3093,172
  have eq3095 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3094 rule_def_0_0 -- subsumption resolution 3094,157
  have eq3096 : (sP4 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq3095 rule_def_1_0 -- subsumption resolution 3095,161
  have eq3097 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq3096 rule_def_4_0 -- subsumption resolution 3096,178
  have eq3235 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq3097 trans_resol -- equality factoring 3097
  have eq3544 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ (new sk0 sk2 sk0) := resolve eq1938 imp_new_0 -- resolution 1938,155
  have eq3562 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ a = b := resolve eq3544 preserve_3 -- subsumption resolution 3544,202
  have eq3563 : c = sk3 ∨ c = sk0 ∨ a = sk0 := resolve eq3562 eq3235 -- subsumption resolution 3562,3235
  have eq3598 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq3563.imp_left (fun h : c = sk3 ↦ superpose h eq1290)) -- superposition 1290,3563, 3563 into 1290, unify on (0).2 in 3563 and (0).2 in 1290
  have eq3668 : (old sk0 c sk0) ∨ a = sk0 ∨ a = b ∨ c = sk0 := resolve eq3598 rfl -- duplicate literal removal 3598
  have eq3689 : a = sk0 ∨ a = b ∨ c = sk0 := resolve eq3668 p4XZ -- subsumption resolution 3668,137
  have eq3690 : c = sk0 ∨ a = sk0 := resolve eq3689 eq3235 -- subsumption resolution 3689,3235
  have eq3747 : (old c sk1 sk2) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq3690.imp_left (fun h : c = sk0 ↦ superpose h eq912)) -- superposition 912,3690, 3690 into 912, unify on (0).2 in 3690 and (0).1 in 912
  have eq3830 : a = c ∨ c = b ∨ a = sk0 := resolve eq3747 p4YZ -- subsumption resolution 3747,138
  have eq3831 : c = b ∨ a = sk0 := resolve eq3830 ac -- subsumption resolution 3830,133
  have eq3832 : a = sk0 := resolve eq3831 bc -- subsumption resolution 3831,134
  have eq3834 : (new a sk3 a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 200,3832
  have eq3836 : ¬(new a sk2 a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 202,3832
  have eq3837 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ sk2 = X0 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq240 -- backward demodulation 240,3832
  have eq3885 : (new a sk1 sk3) ∨ ¬(new sk0 sk0 sk3) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq552 -- backward demodulation 552,3832
  have eq3893 : ∀ (X0 : G) , ¬(new a a X0) ∨ (new sk0 X0 sk1) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq678 -- backward demodulation 678,3832
  have eq3989 : (sP3 a sk3 a) ∨ (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq920 -- backward demodulation 920,3832
  have eq4051 : (sP0 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1097 -- backward demodulation 1097,3832
  have eq4053 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1099 -- backward demodulation 1099,3832
  have eq4071 : (old a sk1 sk2) ∨ c = sk1 ∨ a = b ∨ b = sk1 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1194 -- backward demodulation 1194,3832
  have eq4233 : (old sk1 a sk3) ∨ a = sk1 ∨ b = sk1 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1596 -- backward demodulation 1596,3832
  have eq4235 : (old sk1 a sk3) ∨ a = sk1 ∨ a = b := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1598 -- backward demodulation 1598,3832
  have eq4282 : (old sk1 a sk3) ∨ a = sk1 ∨ c = sk0 ∨ c = sk3 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1685 -- backward demodulation 1685,3832
  have eq4299 : (sP0 sk1 a sk3) ∨ (old sk1 sk0 sk3) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1716 -- backward demodulation 1716,3832
  have eq4303 : (old sk1 a sk3) ∨ c = sk0 ∨ c = sk3 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1721 -- backward demodulation 1721,3832
  have eq4372 : a = c ∨ c = sk3 ∨ (old sk0 sk2 sk0) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1941 -- backward demodulation 1941,3832
  have eq4747 : ¬(new a a sk3) ∨ (new a sk1 sk3) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3885 -- forward demodulation 3885,3832
  have eq4752 : ∀ (X0 : G) , ¬(new a a X0) ∨ (new a X0 sk1) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3893 -- forward demodulation 3893,3832
  have eq4899 : (sP1 sk0 sk3 sk0) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := resolve eq3989 eq229 -- subsumption resolution 3989,229
  have eq4900 : (sP1 a sk3 a) ∨ (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4899 -- forward demodulation 4899,3832
  have eq4901 : (sP0 sk0 sk3 sk0) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := resolve eq4900 eq648 -- subsumption resolution 4900,648
  have eq4902 : (sP0 a sk3 a) ∨ (old sk0 sk3 sk0) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4901 -- forward demodulation 4901,3832
  have eq4903 : (old a sk3 a) ∨ (sP0 a sk3 a) ∨ (sP2 sk0 sk3 sk0) ∨ (new a c a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4902 -- forward demodulation 4902,3832
  have eq4904 : (sP2 a sk3 a) ∨ (old a sk3 a) ∨ (sP0 a sk3 a) ∨ (new a c a) := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4903 -- forward demodulation 4903,3832
  have eq5008 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4051 -- forward demodulation 4051,3832
  have eq5232 : a = c ∨ (old sk1 a sk3) ∨ a = sk1 ∨ c = sk3 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4282 -- forward demodulation 4282,3832
  have eq5233 : (old sk1 a sk3) ∨ a = sk1 ∨ c = sk3 := resolve eq5232 ac -- subsumption resolution 5232,133
  have eq5281 : (old sk1 sk0 sk3) ∨ c = sk0 ∨ a = b := resolve eq4299 rule_def_0_1 -- subsumption resolution 4299,158
  have eq5282 : (old sk1 a sk3) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5281 -- forward demodulation 5281,3832
  have eq5283 : a = c ∨ (old sk1 a sk3) ∨ a = b := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5282 -- forward demodulation 5282,3832
  have eq5284 : (old sk1 a sk3) ∨ a = b := resolve eq5283 ac -- subsumption resolution 5283,133
  have eq5291 : a = c ∨ (old sk1 a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4303 -- forward demodulation 4303,3832
  have eq5292 : (old sk1 a sk3) ∨ c = sk3 := resolve eq5291 ac -- subsumption resolution 5291,133
  have eq5478 : c = sk3 ∨ (old sk0 sk2 sk0) ∨ c = sk1 ∨ c = sk2 := resolve eq4372 ac -- subsumption resolution 4372,133
  have eq5479 : (old a sk2 a) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq3832, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5478 -- forward demodulation 5478,3832
  have eq6320 : (old a sk3 a) ∨ (sP0 a sk3 a) ∨ (new a c a) ∨ a = c := resolve eq4904 rule_def_2_2 -- resolution 4904,168
  have eq6326 : (sP0 a sk3 a) ∨ (old a sk3 a) ∨ (new a c a) := resolve eq6320 ac -- subsumption resolution 6320,133
  have eq6330 : (old a sk3 a) ∨ (new a c a) ∨ a = c := resolve eq6326 rule_def_0_2 -- resolution 6326,159
  have eq6333 : (new a c a) ∨ (old a sk3 a) := resolve eq6330 ac -- subsumption resolution 6330,133
  have eq6583 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ (new a sk2 a) := resolve eq5479 imp_new_0 -- resolution 5479,155
  have eq6585 : c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq6583 eq3836 -- subsumption resolution 6583,3836
  have eq6613 : ¬(new a a c) ∨ (new a sk1 c) ∨ c = sk1 ∨ c = sk2 := Or.assoc2 (eq6585.imp_left (fun h : c = sk3 ↦ superpose h eq4747)) -- superposition 4747,6585, 6585 into 4747, unify on (0).2 in 6585 and (0).3 in 4747
  have eq6622 : (old sk1 a c) ∨ a = b ∨ c = sk1 ∨ c = sk2 := Or.assoc2 (eq6585.imp_left (fun h : c = sk3 ↦ superpose h eq5284)) -- superposition 5284,6585, 6585 into 5284, unify on (0).2 in 6585 and (0).3 in 5284
  have eq6644 : ¬(new a a c) ∨ c = sk1 ∨ c = sk2 := resolve eq6613 eq3837 -- subsumption resolution 6613,3837
  have eq6651 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq6622 p4XY -- subsumption resolution 6622,136
  have eq6655 : ¬(new a c a) ∨ c = sk1 ∨ a = b := eq6651.imp_left (fun h : c = sk2 ↦ superpose h eq3836) -- superposition 3836,6651, 6651 into 3836, unify on (0).2 in 6651 and (0).2 in 3836
  have eq6667 : (old a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 ∨ c = sk1 ∨ a = b := Or.assoc4 (eq6651.imp_left (fun h : c = sk2 ↦ superpose h eq4071)) -- superposition 4071,6651, 6651 into 4071, unify on (0).2 in 6651 and (0).3 in 4071
  have eq6682 : (old a sk1 c) ∨ c = sk1 ∨ a = b ∨ b = sk1 := resolve eq6667 rfl -- duplicate literal removal 6667
  have eq6683 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq6682 p4XY -- subsumption resolution 6682,136
  have eq6712 : (old b a sk3) ∨ a = b ∨ a = b ∨ a = b ∨ c = sk1 := Or.assoc3 (eq6683.imp_left (fun h : b = sk1 ↦ superpose h eq4235)) -- superposition 4235,6683, 6683 into 4235, unify on (0).2 in 6683 and (0).1 in 4235
  have eq6757 : (old b a sk3) ∨ a = b ∨ c = sk1 := resolve eq6712 rfl -- duplicate literal removal 6712
  have eq6839 : c = sk1 ∨ a = b ∨ (old a sk3 a) := resolve eq6655 eq6333 -- resolution 6655,6333
  have eq6899 : a = b ∨ c = sk1 ∨ (new a c a) ∨ ¬(old a sk3 a) := resolve eq6757 eq215 -- resolution 6757,215
  have eq6934 : a = b ∨ c = sk1 ∨ ¬(old a sk3 a) := resolve eq6899 eq6655 -- subsumption resolution 6899,6655
  have eq6935 : c = sk1 ∨ a = b := resolve eq6934 eq6839 -- subsumption resolution 6934,6839
  have eq6962 : (old c a sk3) ∨ a = c ∨ c = b ∨ a = b := Or.assoc3 (eq6935.imp_left (fun h : c = sk1 ↦ superpose h eq4233)) -- superposition 4233,6935, 6935 into 4233, unify on (0).2 in 6935 and (0).1 in 4233
  have eq7007 : a = c ∨ c = b ∨ a = b := resolve eq6962 p4YZ -- subsumption resolution 6962,138
  have eq7008 : c = b ∨ a = b := resolve eq7007 ac -- subsumption resolution 7007,133
  have eq7009 : a = b := resolve eq7008 bc -- subsumption resolution 7008,134
  have eq7011 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq7009, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 135,7009
  have eq7012 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq7009, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 158,7009
  have eq7020 : (new a a c) := Eq.mp (by simp only [eq7009, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq205 -- backward demodulation 205,7009
  have eq7678 : c = sk2 ∨ c = sk1 := resolve eq7020 eq6644 -- resolution 7020,6644
  have eq7679 : (new a c sk1) := resolve eq7020 eq4752 -- resolution 7020,4752
  have eq7715 (X0 : G) : sk1 = X0 ∨ ¬(new a c X0) := resolve eq7679 prev_0 -- resolution 7679,185
  have eq7753 : (sP0 a sk1 c) ∨ (old a sk1 c) ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq7678.imp_left (fun h : c = sk2 ↦ superpose h eq5008)) -- superposition 5008,7678, 7678 into 5008, unify on (0).2 in 7678 and (0).3 in 5008
  have eq7757 : (sP0 a sk1 c) ∨ (old a sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq7753 rfl -- duplicate literal removal 7753
  have eq7764 : (sP0 a sk1 c) ∨ c = sk1 ∨ a = sk1 := resolve eq7757 p4XY -- subsumption resolution 7757,136
  have eq7765 : c = sk1 ∨ a = sk1 := resolve eq7764 eq7012 -- subsumption resolution 7764,7012
  have eq7829 : (old c a sk3) ∨ a = c ∨ c = sk3 ∨ a = sk1 := Or.assoc3 (eq7765.imp_left (fun h : c = sk1 ↦ superpose h eq5233)) -- superposition 5233,7765, 7765 into 5233, unify on (0).2 in 7765 and (0).1 in 5233
  have eq7855 : a = c ∨ c = sk3 ∨ a = sk1 := resolve eq7829 p4YZ -- subsumption resolution 7829,138
  have eq7856 : c = sk3 ∨ a = sk1 := resolve eq7855 ac -- subsumption resolution 7855,133
  have eq7890 : (new a c a) ∨ a = sk1 := eq7856.imp_left (fun h : c = sk3 ↦ superpose h eq3834) -- superposition 3834,7856, 7856 into 3834, unify on (0).2 in 7856 and (0).2 in 3834
  have eq7932 : a = sk1 := resolve eq7890 eq7715 -- subsumption resolution 7890,7715
  have eq7965 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq7932, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4053 -- backward demodulation 4053,7932
  have eq8010 : (old a a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq7932, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5292 -- backward demodulation 5292,7932
  have eq8250 : (old a sk1 sk2) ∨ c = sk2 := resolve eq7965 ac -- subsumption resolution 7965,133
  have eq8251 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq7932, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8250 -- forward demodulation 8250,7932
  have eq8252 : c = sk2 := resolve eq8251 eq7011 -- subsumption resolution 8251,7011
  have eq8253 : ¬(new a c a) := Eq.mp (by simp only [eq8252, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3836 -- backward demodulation 3836,8252
  have eq8325 : c = sk3 := resolve eq8010 eq7011 -- subsumption resolution 8010,7011
  have eq8326 : (new a c a) := Eq.mp (by simp only [eq8325, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3834 -- backward demodulation 3834,8325
  subsumption eq8253 eq8326 -- subsumption resolution 8326,8253

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_15_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_7 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X0 X3 X0 ∨ ¬ new X1 X3 X0 ∨ ¬ new X4 X1 X3 ∨ new X1 X2 X4)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_15 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X0 ∨ ¬ old X0 X2 X3 ∨ ¬ old X3 X0 X1 ∨ ¬ old X4 X0 X2 ∨ X0 = X4)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X0 ∨ ¬ new X0 X2 X3 ∨ ¬ new X3 X0 X1 ∨ ¬ new X4 X0 X2 ∨ X0 = X4) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq208 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 159
  have eq209 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq208 rfl -- equality resolution 208
  have eq210 : (new a b c) := resolve eq209 rfl -- equality resolution 209
  have eq228 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 177,150
  have eq246 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk0 = X0 := resolve prev_0 preserve_0 -- resolution 188,203
  have eq274 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 172,150
  have eq543 (X0 X1 : G) : ¬(new sk0 sk2 X1) ∨ (new sk0 X0 sk4) ∨ ¬(new X1 sk2 X1) ∨ ¬(new X1 sk0 X0) := resolve prev_7 preserve_3 -- resolution 195,206
  have eq569 : (sP4 sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 187,203
  have eq570 : (sP4 sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) := resolve new_imp preserve_1 -- resolution 187,204
  have eq571 : (sP4 sk3 sk0 sk1) ∨ (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) := resolve new_imp preserve_2 -- resolution 187,205
  have eq572 : (sP4 sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) := resolve new_imp preserve_3 -- resolution 187,206
  have eq622 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq228 rule_def_3_3 -- resolution 228,178
  have eq623 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq622 rfl -- duplicate literal removal 622
  have eq738 (X0 : G) : ¬(new sk3 sk2 sk3) ∨ (new sk0 X0 sk4) ∨ ¬(new sk3 sk0 X0) := resolve eq543 preserve_1 -- resolution 543,204
  have eq768 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq274 rule_def_2_4 -- resolution 274,173
  have eq771 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq768 rfl -- duplicate literal removal 768
  have eq965 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq569 rule_def_4_0 -- resolution 569,181
  have eq966 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq569 rule_def_4_1 -- resolution 569,182
  have eq979 : (sP2 sk0 sk1 sk0) ∨ (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ a = sk0 := resolve eq965 rule_def_0_0 -- subsumption resolution 965,160
  have eq980 : (sP3 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 := resolve eq979 rule_def_1_0 -- subsumption resolution 979,164
  have eq981 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP3 sk0 sk1 sk0) ∨ c = sk1 := resolve eq966 rule_def_1_1 -- subsumption resolution 966,165
  have eq982 : (sP2 sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq981 rule_def_3_1 -- subsumption resolution 981,176
  have eq987 : (old sk0 sk1 sk0) ∨ (sP2 sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq980 rule_def_3_0 -- resolution 980,175
  have eq997 : (old sk0 sk1 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq987 rule_def_2_0 -- subsumption resolution 987,169
  have eq1001 : (sP2 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ a = sk0 := resolve eq570 rule_def_4_0 -- resolution 570,181
  have eq1002 : (sP2 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ c = sk2 := resolve eq570 rule_def_4_1 -- resolution 570,182
  have eq1015 : (sP2 sk0 sk2 sk3) ∨ (sP1 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ a = sk0 := resolve eq1001 rule_def_0_0 -- subsumption resolution 1001,160
  have eq1016 : (sP3 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ a = sk0 := resolve eq1015 rule_def_1_0 -- subsumption resolution 1015,164
  have eq1017 : (sP2 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ (sP3 sk0 sk2 sk3) ∨ c = sk2 := resolve eq1002 rule_def_1_1 -- subsumption resolution 1002,165
  have eq1018 : (sP2 sk0 sk2 sk3) ∨ (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk2 := resolve eq1017 rule_def_3_1 -- subsumption resolution 1017,176
  have eq1038 : (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ a = sk3 := resolve eq571 rule_def_4_0 -- resolution 571,181
  have eq1039 : (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq571 rule_def_4_1 -- resolution 571,182
  have eq1052 : (sP2 sk3 sk0 sk1) ∨ (sP1 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ a = sk3 := resolve eq1038 rule_def_0_0 -- subsumption resolution 1038,160
  have eq1053 : (sP3 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP2 sk3 sk0 sk1) ∨ a = sk3 := resolve eq1052 rule_def_1_0 -- subsumption resolution 1052,164
  have eq1054 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ (sP3 sk3 sk0 sk1) ∨ c = sk0 := resolve eq1039 rule_def_1_1 -- subsumption resolution 1039,165
  have eq1055 : (sP2 sk3 sk0 sk1) ∨ (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 := resolve eq1054 rule_def_3_1 -- subsumption resolution 1054,176
  have eq1075 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ a = sk4 := resolve eq572 rule_def_4_0 -- resolution 572,181
  have eq1076 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ c = sk0 := resolve eq572 rule_def_4_1 -- resolution 572,182
  have eq1089 : (sP2 sk4 sk0 sk2) ∨ (sP1 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ a = sk4 := resolve eq1075 rule_def_0_0 -- subsumption resolution 1075,160
  have eq1090 : (sP3 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 := resolve eq1089 rule_def_1_0 -- subsumption resolution 1089,164
  have eq1091 : (sP2 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ (sP3 sk4 sk0 sk2) ∨ c = sk0 := resolve eq1076 rule_def_1_1 -- subsumption resolution 1076,165
  have eq1092 : (sP2 sk4 sk0 sk2) ∨ (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ c = sk0 := resolve eq1091 rule_def_3_1 -- subsumption resolution 1091,176
  have eq1216 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq982 rule_def_2_2 -- resolution 982,171
  have eq1219 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq1216 rule_def_0_2 -- subsumption resolution 1216,162
  have eq1405 : (old sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 := resolve eq1016 rule_def_3_0 -- resolution 1016,175
  have eq1411 : (old sk0 sk2 sk3) ∨ (sP2 sk0 sk2 sk3) ∨ a = sk0 ∨ a = b := resolve eq1016 eq623 -- resolution 1016,623
  have eq1415 : (old sk0 sk2 sk3) ∨ a = sk0 ∨ b = sk0 := resolve eq1405 rule_def_2_0 -- subsumption resolution 1405,169
  have eq1417 : (old sk0 sk2 sk3) ∨ a = sk0 ∨ a = b := resolve eq1411 eq771 -- subsumption resolution 1411,771
  have eq1571 : (sP0 sk0 sk2 sk3) ∨ (old sk0 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq1018 rule_def_2_2 -- resolution 1018,171
  have eq1574 : (old sk0 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq1571 rule_def_0_2 -- subsumption resolution 1571,162
  have eq1698 : (old sk3 sk0 sk1) ∨ (sP2 sk3 sk0 sk1) ∨ a = sk3 ∨ b = sk3 := resolve eq1053 rule_def_3_0 -- resolution 1053,175
  have eq1708 : (old sk3 sk0 sk1) ∨ a = sk3 ∨ b = sk3 := resolve eq1698 rule_def_2_0 -- subsumption resolution 1698,169
  have eq1852 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq1055 eq771 -- resolution 1055,771
  have eq1854 : (sP0 sk3 sk0 sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1055 rule_def_2_2 -- resolution 1055,171
  have eq1857 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq1854 rule_def_0_2 -- subsumption resolution 1854,162
  have eq1881 : (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 ∨ b = sk4 := resolve eq1090 rule_def_3_0 -- resolution 1090,175
  have eq1887 : (old sk4 sk0 sk2) ∨ (sP2 sk4 sk0 sk2) ∨ a = sk4 ∨ a = b := resolve eq1090 eq623 -- resolution 1090,623
  have eq1891 : (old sk4 sk0 sk2) ∨ a = sk4 ∨ b = sk4 := resolve eq1881 rule_def_2_0 -- subsumption resolution 1881,169
  have eq1893 : (old sk4 sk0 sk2) ∨ a = sk4 ∨ a = b := resolve eq1887 eq771 -- subsumption resolution 1887,771
  have eq1914 : (sP0 sk4 sk0 sk2) ∨ (old sk4 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq1092 rule_def_2_2 -- resolution 1092,171
  have eq1917 : (old sk4 sk0 sk2) ∨ c = sk0 ∨ c = sk2 := resolve eq1914 rule_def_0_2 -- subsumption resolution 1914,162
  have eq1949 (X0 X1 : G) : c = sk0 ∨ c = sk2 ∨ sk0 = sk4 ∨ ¬(old X0 sk0 X1) ∨ ¬(old sk0 sk2 X0) ∨ ¬(old sk0 X1 sk0) := resolve eq1917 old_15 -- resolution 1917,157
  have eq1951 (X0 X1 : G) : ¬(old sk0 sk2 X0) ∨ c = sk2 ∨ ¬(old X0 sk0 X1) ∨ c = sk0 ∨ ¬(old sk0 X1 sk0) := resolve eq1949 preserve_4 -- subsumption resolution 1949,207
  have eq5147 (X0 : G) : c = sk2 ∨ ¬(old sk3 sk0 X0) ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk2 ∨ c = sk3 := resolve eq1951 eq1574 -- resolution 1951,1574
  have eq5154 (X0 : G) : ¬(old sk3 sk0 X0) ∨ c = sk2 ∨ c = sk0 ∨ ¬(old sk0 X0 sk0) ∨ c = sk3 := resolve eq5147 rfl -- duplicate literal removal 5147
  have eq5161 : c = sk2 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk0) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq5154 eq1857 -- resolution 5154,1857
  have eq5168 : c = sk2 ∨ c = sk0 ∨ ¬(old sk0 sk1 sk0) ∨ c = sk3 ∨ c = sk1 := resolve eq5161 rfl -- duplicate literal removal 5161
  have eq5172 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5168 eq1219 -- subsumption resolution 5168,1219
  have eq5193 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (old c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := Or.assoc6 (eq5172.imp_left (fun h : c = sk3 ↦ superpose h eq571)) -- superposition 571,5172, 5172 into 571, unify on (0).2 in 5172 and (0).1 in 571
  have eq5390 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP0 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5193 p4YZ -- subsumption resolution 5193,141
  have eq5391 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP1 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5390 rule_def_0_2 -- subsumption resolution 5390,162
  have eq5392 : (sP4 c sk0 sk1) ∨ (sP2 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5391 rule_def_1_1 -- subsumption resolution 5391,165
  have eq5393 : (sP4 c sk0 sk1) ∨ (sP3 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5392 rule_def_2_2 -- subsumption resolution 5392,171
  have eq5394 : (sP4 c sk0 sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk1 := resolve eq5393 rule_def_3_1 -- subsumption resolution 5393,176
  have eq5395 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq5394 rule_def_4_1 -- subsumption resolution 5394,182
  have eq5434 : (old sk0 c sk3) ∨ a = sk0 ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq5395.imp_left (fun h : c = sk2 ↦ superpose h eq1415)) -- superposition 1415,5395, 5395 into 1415, unify on (0).2 in 5395 and (0).2 in 1415
  have eq5435 : (old sk0 c sk3) ∨ a = sk0 ∨ a = b ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq5395.imp_left (fun h : c = sk2 ↦ superpose h eq1417)) -- superposition 1417,5395, 5395 into 1417, unify on (0).2 in 5395 and (0).2 in 1417
  have eq5457 : (old sk4 sk0 c) ∨ a = sk4 ∨ b = sk4 ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq5395.imp_left (fun h : c = sk2 ↦ superpose h eq1891)) -- superposition 1891,5395, 5395 into 1891, unify on (0).2 in 5395 and (0).3 in 1891
  have eq5458 : (old sk4 sk0 c) ∨ a = sk4 ∨ a = b ∨ c = sk0 ∨ c = sk1 := Or.assoc3 (eq5395.imp_left (fun h : c = sk2 ↦ superpose h eq1893)) -- superposition 1893,5395, 5395 into 1893, unify on (0).2 in 5395 and (0).3 in 1893
  have eq5538 : c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5434 p4XZ -- subsumption resolution 5434,140
  have eq5539 : c = sk1 ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq5435 p4XZ -- subsumption resolution 5435,140
  have eq5540 : a = sk4 ∨ b = sk4 ∨ c = sk0 ∨ c = sk1 := resolve eq5457 p4XY -- subsumption resolution 5457,139
  have eq5541 : a = sk4 ∨ a = b ∨ c = sk0 ∨ c = sk1 := resolve eq5458 p4XY -- subsumption resolution 5458,139
  have eq5620 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq5538.imp_left (fun h : c = sk1 ↦ superpose h eq569)) -- superposition 569,5538, 5538 into 569, unify on (0).2 in 5538 and (0).2 in 569
  have eq5744 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5620 p4XZ -- subsumption resolution 5620,140
  have eq5745 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5744 rule_def_0_0 -- subsumption resolution 5744,160
  have eq5746 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5745 rule_def_1_0 -- subsumption resolution 5745,164
  have eq5747 : (sP2 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5746 rule_def_4_0 -- subsumption resolution 5746,181
  have eq5748 : (sP3 sk0 c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5747 rule_def_2_2 -- subsumption resolution 5747,171
  have eq5749 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq5748 rule_def_3_0 -- subsumption resolution 5748,175
  have eq6076 : a ≠ b ∨ c = sk0 ∨ a = sk0 := resolve eq5749 trans_resol -- equality factoring 5749
  have eq6265 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq5539.imp_left (fun h : c = sk1 ↦ superpose h eq569)) -- superposition 569,5539, 5539 into 569, unify on (0).2 in 5539 and (0).2 in 569
  have eq6419 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6265 p4XZ -- subsumption resolution 6265,140
  have eq6420 : (sP4 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6419 rule_def_0_2 -- subsumption resolution 6419,162
  have eq6421 : (sP4 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6420 rule_def_2_2 -- subsumption resolution 6420,171
  have eq6422 : (sP4 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6421 rule_def_1_0 -- subsumption resolution 6421,164
  have eq6423 : (sP3 sk0 c sk0) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6422 rule_def_4_0 -- subsumption resolution 6422,181
  have eq6424 : a = b ∨ c = sk0 ∨ a = sk0 := resolve eq6423 eq623 -- subsumption resolution 6423,623
  have eq6425 : c = sk0 ∨ a = sk0 := resolve eq6424 eq6076 -- subsumption resolution 6424,6076
  have eq6537 : (old c sk1 c) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq6425.imp_left (fun h : c = sk0 ↦ superpose h eq997)) -- superposition 997,6425, 6425 into 997, unify on (0).2 in 6425 and (0).1 in 997
  have eq6722 : a = c ∨ c = b ∨ a = sk0 := resolve eq6537 p4YZ -- subsumption resolution 6537,141
  have eq6723 : c = b ∨ a = sk0 := resolve eq6722 ac -- subsumption resolution 6722,136
  have eq6724 : a = sk0 := resolve eq6723 bc -- subsumption resolution 6723,137
  have eq6726 : (new a sk2 sk3) := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 204,6724
  have eq6729 : a ≠ sk4 := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_4 -- backward demodulation 207,6724
  have eq6730 : ∀ (X0 : G) , a = X0 ∨ ¬(new sk0 sk1 X0) := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq246 -- backward demodulation 246,6724
  have eq6823 : ∀ (X0 : G) , ¬(new sk3 a X0) ∨ ¬(new sk3 sk2 sk3) ∨ (new sk0 X0 sk4) := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq738 -- backward demodulation 738,6724
  have eq7204 : (old sk3 a sk1) ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1708 -- backward demodulation 1708,6724
  have eq7273 : (sP0 sk3 a sk1) ∨ (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1852 -- backward demodulation 1852,6724
  have eq8291 : a = c ∨ a = sk4 ∨ b = sk4 ∨ c = sk1 := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5540 -- backward demodulation 5540,6724
  have eq8292 : a = c ∨ a = sk4 ∨ a = b ∨ c = sk1 := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq5541 -- backward demodulation 5541,6724
  have eq8368 : ∀ (X0 : G) , ¬(new a sk1 X0) ∨ a = X0 := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6730 -- forward demodulation 6730,6724
  have eq8522 : ∀ (X0 : G) , (new a X0 sk4) ∨ ¬(new sk3 a X0) ∨ ¬(new sk3 sk2 sk3) := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6823 -- forward demodulation 6823,6724
  have eq9097 : (old sk3 sk0 sk1) ∨ c = sk0 ∨ a = b := resolve eq7273 rule_def_0_1 -- subsumption resolution 7273,161
  have eq9098 : (old sk3 a sk1) ∨ c = sk0 ∨ a = b := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9097 -- forward demodulation 9097,6724
  have eq9099 : a = c ∨ (old sk3 a sk1) ∨ a = b := Eq.mp (by simp only [eq6724, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9098 -- forward demodulation 9098,6724
  have eq9100 : (old sk3 a sk1) ∨ a = b := resolve eq9099 ac -- subsumption resolution 9099,136
  have eq10935 : a = sk4 ∨ b = sk4 ∨ c = sk1 := resolve eq8291 ac -- subsumption resolution 8291,136
  have eq10936 : b = sk4 ∨ c = sk1 := resolve eq10935 eq6729 -- subsumption resolution 10935,6729
  have eq10937 : a = sk4 ∨ a = b ∨ c = sk1 := resolve eq8292 ac -- subsumption resolution 8292,136
  have eq10938 : a = b ∨ c = sk1 := resolve eq10937 eq6729 -- subsumption resolution 10937,6729
  have eq11051 : a ≠ b ∨ c = sk1 := eq10936.imp_left (fun h : b = sk4 ↦ superpose h eq6729) -- superposition 6729,10936, 10936 into 6729, unify on (0).2 in 10936 and (0).2 in 6729
  have eq11052 : c = sk1 := resolve eq11051 eq10938 -- subsumption resolution 11051,10938
  have eq11090 : (old sk3 a c) ∨ a = sk3 ∨ b = sk3 := Eq.mp (by simp only [eq11052, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7204 -- backward demodulation 7204,11052
  have eq11126 : ∀ (X0 : G) , ¬(new a c X0) ∨ a = X0 := Eq.mp (by simp only [eq11052, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8368 -- backward demodulation 8368,11052
  have eq11203 : (old sk3 a c) ∨ a = b := Eq.mp (by simp only [eq11052, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9100 -- backward demodulation 9100,11052
  have eq11300 : a = sk3 ∨ b = sk3 := resolve eq11090 p4XY -- subsumption resolution 11090,139
  have eq11501 : a = b := resolve eq11203 p4XY -- subsumption resolution 11203,139
  have eq11512 : (new a a c) := Eq.mp (by simp only [eq11501, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq210 -- backward demodulation 210,11501
  have eq11932 : a = sk3 ∨ a = sk3 := Eq.mp (by simp only [eq11501, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq11300 -- backward demodulation 11300,11501
  have eq11967 : a = sk3 := resolve eq11932 rfl -- duplicate literal removal 11932
  have eq12197 : (new a sk2 a) := Eq.mp (by simp only [eq11967, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6726 -- backward demodulation 6726,11967
  have eq12233 : ∀ (X0 : G) , ¬(new a sk2 a) ∨ (new a X0 sk4) ∨ ¬(new sk3 a X0) := Eq.mp (by simp only [eq11967, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8522 -- backward demodulation 8522,11967
  have eq12365 (X0 : G) : (new a X0 sk4) ∨ ¬(new sk3 a X0) := resolve eq12233 eq12197 -- subsumption resolution 12233,12197
  have eq12366 : ∀ (X0 : G) , ¬(new a a X0) ∨ (new a X0 sk4) := Eq.mp (by simp only [eq11967, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq12365 -- forward demodulation 12365,11967
  have eq12861 : (new a c sk4) := resolve eq12366 eq11512 -- resolution 12366,11512
  have eq12867 : a = sk4 := resolve eq12861 eq11126 -- resolution 12861,11126
  subsumption eq6729 eq12867 -- subsumption resolution 12867,6729

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq375 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 163,167
  have eq513 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq375 rule_def_4_0 -- resolution 375,157
  have eq524 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := resolve eq513 preserve_1 -- subsumption resolution 513,168
  have eq525 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 := resolve eq524 rule_def_3_0 -- resolution 524,151
  have eq537 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve eq525 preserve_2 -- subsumption resolution 525,169
  have eq538 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk0 := resolve eq537 rule_def_2_0 -- resolution 537,145
  have eq546 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq538 preserve_2 -- subsumption resolution 538,169
  have eq547 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq546 rule_def_1_0 -- resolution 546,140
  have eq557 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq547 preserve_1 -- subsumption resolution 547,168
  have eq560 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq557 rule_def_0_0 -- resolution 557,136
  have eq561 : (old sk0 sk1 sk2) := resolve eq560 preserve_1 -- subsumption resolution 560,168
  have eq577 : memold sk0 := resolve eq561 old_mem1 -- resolution 561,164
  subsumption preserve_3 eq577 -- subsumption resolution 577,170

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (memold : G → Prop) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq198 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 153,126
  have eq242 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 148,126
  have eq375 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 163,167
  have eq412 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq198 rule_def_3_3 -- resolution 198,154
  have eq413 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq412 rfl -- duplicate literal removal 412
  have eq443 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq242 rule_def_2_4 -- resolution 242,149
  have eq446 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq443 rfl -- duplicate literal removal 443
  have eq513 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq375 rule_def_4_0 -- resolution 375,157
  have eq514 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq375 rule_def_4_1 -- resolution 375,158
  have eq524 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq513 rule_def_0_0 -- subsumption resolution 513,136
  have eq525 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq524 rule_def_1_0 -- subsumption resolution 524,140
  have eq526 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve eq514 preserve_4 -- subsumption resolution 514,171
  have eq527 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq525 rule_def_3_0 -- resolution 525,151
  have eq539 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq527 rule_def_2_0 -- subsumption resolution 527,145
  have eq557 : a = sk0 ∨ b = sk0 ∨ memold sk1 := resolve eq539 old_mem2 -- resolution 539,165
  have eq559 : b = sk0 ∨ a = sk0 := resolve eq557 preserve_3 -- subsumption resolution 557,170
  have eq560 : (sP3 b sk1 sk2) ∨ (old b sk1 sk2) ∨ (sP2 b sk1 sk2) ∨ a = b ∨ a = sk0 := Or.assoc4 (eq559.imp_left (fun h : b = sk0 ↦ superpose h eq525)) -- superposition 525,559, 559 into 525, unify on (0).2 in 559 and (0).1 in 525
  have eq563 : a ≠ b ∨ a = sk0 := resolve eq559 trans_resol -- equality factoring 559
  have eq564 : (old b sk1 sk2) ∨ (sP2 b sk1 sk2) ∨ a = b ∨ a = sk0 := resolve eq560 eq413 -- subsumption resolution 560,413
  have eq565 : (old b sk1 sk2) ∨ a = b ∨ a = sk0 := resolve eq564 eq446 -- subsumption resolution 564,446
  have eq584 : a = b ∨ a = sk0 ∨ memold sk1 := resolve eq565 old_mem2 -- resolution 565,165
  have eq603 : a = b ∨ a = sk0 := resolve eq584 preserve_3 -- subsumption resolution 584,170
  have eq604 : a = sk0 := resolve eq603 eq563 -- subsumption resolution 603,563
  have eq608 : (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq604, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq526 -- backward demodulation 526,604
  have eq616 : (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq604, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq608 -- forward demodulation 608,604
  have eq617 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq604, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq616 -- forward demodulation 616,604
  have eq618 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq604, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq617 -- forward demodulation 617,604
  have eq619 : (sP3 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq604, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq618 -- forward demodulation 618,604
  have eq632 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b := resolve eq619 rule_def_3_0 -- resolution 619,151
  have eq633 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := resolve eq619 rule_def_3_1 -- resolution 619,152
  have eq644 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b := resolve eq632 rule_def_2_0 -- subsumption resolution 632,145
  have eq645 : (sP2 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := resolve eq633 preserve_4 -- subsumption resolution 633,171
  have eq647 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq644 rule_def_1_1 -- resolution 644,141
  have eq656 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b := resolve eq647 preserve_4 -- subsumption resolution 647,171
  have eq658 : (old a sk1 sk2) ∨ a = b ∨ b = sk1 := resolve eq656 rule_def_0_1 -- resolution 656,137
  have eq660 : (old a sk1 sk2) ∨ a = b := resolve eq658 preserve_2 -- subsumption resolution 658,169
  have eq680 : a = b ∨ memold sk1 := resolve eq660 old_mem2 -- resolution 660,165
  have eq683 : a = b := resolve eq680 preserve_3 -- subsumption resolution 680,170
  have eq686 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 137,683
  have eq943 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = sk1 := resolve eq645 rule_def_2_1 -- resolution 645,146
  have eq947 : (sP1 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := resolve eq943 preserve_1 -- subsumption resolution 943,168
  have eq951 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := resolve eq947 rule_def_1_1 -- resolution 947,141
  have eq962 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) := resolve eq951 preserve_4 -- subsumption resolution 951,171
  have eq963 : (old a sk1 sk2) ∨ a = sk1 := resolve eq962 eq686 -- resolution 962,686
  have eq966 : (old a sk1 sk2) := resolve eq963 preserve_1 -- subsumption resolution 963,168
  have eq983 : memold sk1 := resolve eq966 old_mem2 -- resolution 966,165
  subsumption preserve_3 eq983 -- subsumption resolution 983,170

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (sF1 : G → G → G → G) (sF2 : G → G → G → G) (sP2 : G → G → G → Prop) (sF3 : G → G → G → G) (sP3 : G → G → G → Prop) (sF4 : G → G → G → G) (sP4 : G → G → G → Prop) (memold : G → Prop) (ac : a ≠ c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), a = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), b = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_2_4 : ∀ (X Y Z : G), old a (sF1 X Y Z) (sF2 X Y Z) ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), old a (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b (sF3 X Y Z) a ∨ ¬sP3 X Y Z) (rule_def_3_4 : ∀ (X Y Z : G), old Z b (sF3 X Y Z) ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq190 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X2 := resolve rule_def_1_2 old_mem1 -- resolution 142,164
  have eq198 (X0 X1 X2 X3 : G) : ¬(old X3 (sF3 X0 X1 X2) a) ∨ a = X3 ∨ ¬(sP3 X0 X1 X2) := resolve rule_def_3_2 old_8 -- resolution 153,126
  have eq216 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ memold X2 := resolve rule_def_3_4 old_mem1 -- resolution 155,164
  have eq242 (X0 X1 X2 X3 : G) : ¬(old X3 (sF1 X0 X1 X2) (sF2 X0 X1 X2)) ∨ b = X3 ∨ ¬(sP2 X0 X1 X2) := resolve rule_def_2_3 old_8 -- resolution 148,126
  have eq375 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 163,167
  have eq412 (X0 X1 X2 : G) : a = b ∨ ¬(sP3 X0 X1 X2) ∨ ¬(sP3 X0 X1 X2) := resolve eq198 rule_def_3_3 -- resolution 198,154
  have eq413 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) ∨ a = b := resolve eq412 rfl -- duplicate literal removal 412
  have eq443 (X0 X1 X2 : G) : a = b ∨ ¬(sP2 X0 X1 X2) ∨ ¬(sP2 X0 X1 X2) := resolve eq242 rule_def_2_4 -- resolution 242,149
  have eq446 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) ∨ a = b := resolve eq443 rfl -- duplicate literal removal 443
  have eq513 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq375 rule_def_4_0 -- resolution 375,157
  have eq514 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq375 rule_def_4_1 -- resolution 375,158
  have eq515 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk2 := resolve eq375 rule_def_4_2 -- resolution 375,159
  have eq524 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = sk0 := resolve eq513 rule_def_0_0 -- subsumption resolution 513,136
  have eq525 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 := resolve eq524 rule_def_1_0 -- subsumption resolution 524,140
  have eq526 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk1 := resolve eq514 rule_def_1_1 -- subsumption resolution 514,141
  have eq527 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq526 rule_def_3_1 -- subsumption resolution 526,152
  have eq528 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve eq515 preserve_1 -- subsumption resolution 515,168
  have eq529 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq525 rule_def_3_0 -- resolution 525,151
  have eq541 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ b = sk0 := resolve eq529 rule_def_2_0 -- subsumption resolution 529,145
  have eq603 : a = sk0 ∨ b = sk0 ∨ memold sk2 := resolve eq541 old_mem3 -- resolution 541,166
  have eq604 : b = sk0 ∨ a = sk0 := resolve eq603 preserve_3 -- subsumption resolution 603,170
  have eq608 : (sP3 b sk1 sk2) ∨ (old b sk1 sk2) ∨ (sP2 b sk1 sk2) ∨ a = b ∨ a = sk0 := Or.assoc4 (eq604.imp_left (fun h : b = sk0 ↦ superpose h eq525)) -- superposition 525,604, 604 into 525, unify on (0).2 in 604 and (0).1 in 525
  have eq613 : a ≠ b ∨ a = sk0 := resolve eq604 trans_resol -- equality factoring 604
  have eq615 : (old b sk1 sk2) ∨ (sP2 b sk1 sk2) ∨ a = b ∨ a = sk0 := resolve eq608 eq413 -- subsumption resolution 608,413
  have eq616 : (old b sk1 sk2) ∨ a = b ∨ a = sk0 := resolve eq615 eq446 -- subsumption resolution 615,446
  have eq643 : a = b ∨ a = sk0 ∨ memold sk2 := resolve eq616 old_mem3 -- resolution 616,166
  have eq661 : a = b ∨ a = sk0 := resolve eq643 preserve_3 -- subsumption resolution 643,170
  have eq662 : a = sk0 := resolve eq661 eq613 -- subsumption resolution 661,613
  have eq666 : (sP2 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq527 -- backward demodulation 527,662
  have eq667 : (sP3 a sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq528 -- backward demodulation 528,662
  have eq679 : (sP0 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq666 -- forward demodulation 666,662
  have eq680 : (sP2 a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq679 -- forward demodulation 679,662
  have eq681 : (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq667 -- forward demodulation 667,662
  have eq682 : (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq681 -- forward demodulation 681,662
  have eq683 : (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq682 -- forward demodulation 682,662
  have eq684 : (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) ∨ (sP3 a sk1 sk2) := Eq.mp (by simp only [eq662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq683 -- forward demodulation 683,662
  have eq699 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq680 rule_def_2_2 -- resolution 680,147
  have eq705 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ c = sk1 := resolve eq699 preserve_4 -- subsumption resolution 699,171
  have eq709 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq705 rule_def_0_2 -- resolution 705,138
  have eq712 : (old a sk1 sk2) ∨ c = sk1 := resolve eq709 preserve_4 -- subsumption resolution 709,171
  have eq757 : c = sk1 ∨ memold sk2 := resolve eq712 old_mem3 -- resolution 712,166
  have eq759 : c = sk1 := resolve eq757 preserve_3 -- subsumption resolution 757,170
  have eq762 : (sP3 a c sk2) ∨ (old a sk1 sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) := Eq.mp (by simp only [eq759, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq684 -- backward demodulation 684,759
  have eq769 : (old a c sk2) ∨ (sP3 a c sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) := Eq.mp (by simp only [eq759, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq762 -- forward demodulation 762,759
  have eq770 : (sP3 a c sk2) ∨ (sP0 a sk1 sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) := resolve eq769 p4XZ -- subsumption resolution 769,116
  have eq771 : (sP0 a c sk2) ∨ (sP3 a c sk2) ∨ (sP1 a sk1 sk2) ∨ (sP2 a sk1 sk2) := Eq.mp (by simp only [eq759, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq770 -- forward demodulation 770,759
  have eq772 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP3 a c sk2) ∨ (sP2 a sk1 sk2) := Eq.mp (by simp only [eq759, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq771 -- forward demodulation 771,759
  have eq773 : (sP3 a c sk2) ∨ (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) := Eq.mp (by simp only [eq759, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq772 -- forward demodulation 772,759
  have eq816 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) ∨ a = b := resolve eq773 rule_def_3_0 -- resolution 773,151
  have eq821 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ (sP2 a c sk2) ∨ memold sk2 := resolve eq773 eq216 -- resolution 773,216
  have eq828 : (sP1 a c sk2) ∨ (sP0 a c sk2) ∨ a = b := resolve eq816 rule_def_2_0 -- subsumption resolution 816,145
  have eq833 : (sP2 a c sk2) ∨ (sP0 a c sk2) ∨ (sP1 a c sk2) := resolve eq821 preserve_3 -- subsumption resolution 821,170
  have eq846 : (sP0 a c sk2) ∨ a = b ∨ memold sk2 := resolve eq828 eq190 -- resolution 828,190
  have eq852 : (sP0 a c sk2) ∨ a = b := resolve eq846 preserve_3 -- subsumption resolution 846,170
  have eq853 : a = b ∨ c = sk2 := resolve eq852 rule_def_0_2 -- resolution 852,138
  have eq856 : a = b := resolve eq853 preserve_4 -- subsumption resolution 853,171
  have eq859 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq856, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 137,856
  have eq1107 : (sP0 a c sk2) ∨ (sP1 a c sk2) ∨ a = c := resolve eq833 rule_def_2_1 -- resolution 833,146
  have eq1111 : (sP1 a c sk2) ∨ (sP0 a c sk2) := resolve eq1107 ac -- subsumption resolution 1107,112
  have eq1118 : (sP0 a c sk2) ∨ memold sk2 := resolve eq1111 eq190 -- resolution 1111,190
  have eq1123 : (sP0 a c sk2) := resolve eq1118 preserve_3 -- subsumption resolution 1118,170
  have eq1126 : a = c := resolve eq1123 eq859 -- resolution 1123,859
  subsumption ac eq1126 -- subsumption resolution 1126,112

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X3 ∨ ¬ R X1 X3 X4 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1, ¬ R X0 X1 X1 ∨ R X1 X0 X1)
  rule_3 : (∀ X0 X1, ¬ R X0 X1 X0 ∨ ¬ R X1 X0 X1 ∨ R X0 X0 X0)
  rule_4 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X3 X0 X4 ∨ ¬ R X3 X1 X2 ∨ R X0 X3 X4)
  rule_5 : (∀ X0 X1 X2 X3, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X3 X0 X2 ∨ X1 = X3)
  rule_6 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X3 ∨ ¬ R X2 X1 X3 ∨ ¬ R X4 X0 X1 ∨ R X0 X4 X1)
  rule_7 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X0 ∨ ¬ R X1 X3 X0 ∨ ¬ R X4 X1 X3 ∨ R X1 X2 X4)
  rule_8 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X3 = X0)
  rule_9 : (∀ X0 X1 X2, ¬ R X0 X1 X0 ∨ ¬ R X0 X2 X0 ∨ ¬ R X2 X0 X1 ∨ X1 = X2)
  rule_10 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X0 ∨ ¬ R X2 X0 X3 ∨ ¬ R X3 X0 X1 ∨ R X0 X0 X2)
  rule_11 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X3 X0 X1 ∨ ¬ R X4 X0 X2 ∨ R X0 X3 X4)
  rule_12 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X2 ∨ ¬ R X4 X0 X1 ∨ ¬ R X5 X0 X3 ∨ X4 = X5)
  rule_13 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X1 ∨ ¬ R X0 X4 X0 ∨ ¬ R X3 X0 X4 ∨ X2 = X0)
  rule_14 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X3 X0 ∨ ¬ R X1 X0 X3 ∨ R X0 X2 X0)
  rule_15 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X0 ∨ ¬ R X0 X2 X3 ∨ ¬ R X3 X0 X1 ∨ ¬ R X4 X0 X2 ∨ X0 = X4)
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
  let sP1 (X Y Z) := ∃ sF0, a = X ∧ c = Y ∧ ps.R Z a sF0 ∧ ps.R a sF0 b
  choose! sF0 hsP1 using fun (X Y Z) (h : sP1 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2, rule_def_1_3⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3
  let sP2 (X Y Z) := ∃ sF1 sF2, b = X ∧ a = Y ∧ c = Z ∧ ps.R b sF1 sF2 ∧ ps.R a sF1 sF2
  choose! sF1 sF2 hsP2 using fun (X Y Z) (h : sP2 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3, rule_def_2_4⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4
  let sP3 (X Y Z) := ∃ sF3, b = X ∧ c = Y ∧ ps.R a sF3 a ∧ ps.R b sF3 a ∧ ps.R Z b sF3
  choose! sF3 hsP3 using fun (X Y Z) (h : sP3 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3, rule_def_3_4⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4
  let sP4 (X Y Z) := ∃ sF4, a = X ∧ c = Y ∧ a = Z ∧ ps.R a sF4 a ∧ ps.R b a sF4
  choose! sF4 hsP4 using fun (X Y Z) (h : sP4 X Y Z) ↦ h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3, rule_def_4_4⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_4 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_5 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [not_and, not_exists, imp_iff_not_or, sP3, ← forall_or_right, or_assoc] at imp_new_4
  simp only [not_and, not_exists, imp_iff_not_or, sP4, ← forall_or_right, or_assoc] at imp_new_5
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 sP3 sP4 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_8 ps.rule_12 ps.rule_15 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_8 ps.rule_10 ps.rule_11 ps.rule_14 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p4XZ p4YZ ps.rule_2 rule_def_0_1 rule_def_0_2 rule_def_1_1 rule_def_1_2 rule_def_2_1 rule_def_2_2 rule_def_3_1 rule_def_3_4 rule_def_4_1 rule_def_4_2 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p4YZ ps.rule_3 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_2 rule_def_3_0 rule_def_3_1 rule_def_4_0 rule_def_4_1 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 p4XY p4XZ ps.rule_8 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac p3 p4XY p4XZ p4YZ ps.rule_5 ps.rule_8 ps.rule_10 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_4 new_imp
  have prev_6 := rule_6_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p4XY p4YZ prev_0 ps.rule_2 ps.rule_6 ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp imp_new_0
  have prev_7 := rule_7_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 prev_1 prev_4
  have prev_8 := rule_8_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 p4XY p4XZ ps.rule_8 rule_def_0_0 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp
  have prev_9 := rule_9_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ ps.rule_8 ps.rule_9 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp
  have prev_10 := rule_10_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ ps.rule_8 ps.rule_10 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_4 new_imp imp_new_0
  have prev_11 := rule_11_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ prev_2 prev_5 ps.rule_8 ps.rule_11 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 new_imp imp_new_0
  have prev_12 := rule_12_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ prev_5 ps.rule_8 prev_8 ps.rule_12 ps.rule_15 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_4 new_imp
  have prev_13 := rule_13_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 prev_1 prev_7 ps.rule_8 ps.rule_14 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_4_4 new_imp
  have prev_14 := rule_14_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p3 p4XY p4XZ p4YZ prev_0 prev_4 prev_7 ps.rule_8 ps.rule_14 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_4_4 new_imp imp_new_0
  have prev_15 := rule_15_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 ac bc p4XY p4XZ p4YZ prev_0 prev_7 ps.rule_8 ps.rule_15 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    rule_6 := prev_6
    rule_7 := prev_7
    rule_8 := prev_8
    rule_9 := prev_9
    rule_10 := prev_10
    rule_11 := prev_11
    rule_12 := prev_12
    rule_13 := prev_13
    rule_14 := prev_14
    rule_15 := prev_15
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_0 rule_def_2_0 rule_def_3_0 rule_def_4_0 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 (· ∈ ps.finsupp) ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 sF1 sF2 sP2 sF3 sP3 sF4 sP4 (· ∈ ps.finsupp) ac p4XZ ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_2_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_3_4 rule_def_4_0 rule_def_4_1 rule_def_4_2 new_imp ps.mem_1 ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X2 X3 ∨ ¬ ps.compl X1 X3 X4 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X2) (max (Nat.pair X1 X3) (max (Nat.pair X1 X4) 0)))
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

theorem PartialSolution.toMagma_equation511 :
    letI := ps.toMagma
    Equation511 ℕ := by
  simp only [Equation511, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun X1 (ps.complFun X0 X1)) (ps.complFun X1 (ps.complFun X1 (ps.complFun X0 X1)))

macro "solution_enumerator" : tactic => `(tactic| (
  simp only [← imp_iff_not_or, Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton]
  intros
  repeat
    rename_i h1
    contrapose h1
    simp_all
    try split_ands
))

set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter614 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 3, 4), (1, 4, 5), (1, 5, 2), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3, 4, 5}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation614 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation614 G := by
  use ℕ, PartialSolution.counter614.toMagma, PartialSolution.counter614.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter614.of_R 1 1 2] | rw [PartialSolution.counter614.of_R 1 3 4] | rw [PartialSolution.counter614.of_R 1 4 5] | rw [PartialSolution.counter614.of_R 1 5 2] | rw [PartialSolution.counter614.of_R 2 1 3])
  all_goals simp [PartialSolution.counter614]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter714 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 1)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation714 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation714 G := by
  use ℕ, PartialSolution.counter714.toMagma, PartialSolution.counter714.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter714.of_R 1 1 1] | rw [PartialSolution.counter714.of_R 1 2 1])
  all_goals simp [PartialSolution.counter714]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1020 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 3), (1, 4, 5), (3, 1, 4)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3, 4, 5}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation1020 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation1020 G := by
  use ℕ, PartialSolution.counter1020.toMagma, PartialSolution.counter1020.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter1020.of_R 1 1 2] | rw [PartialSolution.counter1020.of_R 1 2 3] | rw [PartialSolution.counter1020.of_R 1 4 5] | rw [PartialSolution.counter1020.of_R 3 1 4])
  all_goals simp [PartialSolution.counter1020]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1223 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 4, 5), (2, 1, 3), (3, 1, 4)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3, 4, 5}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation1223 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation1223 G := by
  use ℕ, PartialSolution.counter1223.toMagma, PartialSolution.counter1223.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter1223.of_R 1 1 2] | rw [PartialSolution.counter1223.of_R 1 4 5] | rw [PartialSolution.counter1223.of_R 2 1 3] | rw [PartialSolution.counter1223.of_R 3 1 4])
  all_goals simp [PartialSolution.counter1223]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2238 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation2238 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation2238 G := by
  use ℕ, PartialSolution.counter2238.toMagma, PartialSolution.counter2238.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2238.of_R 1 1 2] | rw [PartialSolution.counter2238.of_R 1 2 1] | rw [PartialSolution.counter2238.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2238]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2338 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 1)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation2338 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation2338 G := by
  use ℕ, PartialSolution.counter2338.toMagma, PartialSolution.counter2338.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter2338.of_R 1 1 1] | rw [PartialSolution.counter2338.of_R 1 2 1])
  all_goals simp [PartialSolution.counter2338]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2441 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (1, 3, 2), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation2441 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation2441 G := by
  use ℕ, PartialSolution.counter2441.toMagma, PartialSolution.counter2441.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2441.of_R 1 1 2] | rw [PartialSolution.counter2441.of_R 1 2 1] | rw [PartialSolution.counter2441.of_R 1 3 2] | rw [PartialSolution.counter2441.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2441]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2847 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation2847 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation2847 G := by
  use ℕ, PartialSolution.counter2847.toMagma, PartialSolution.counter2847.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2847.of_R 1 1 2] | rw [PartialSolution.counter2847.of_R 1 2 1] | rw [PartialSolution.counter2847.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2847]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter3050 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 3), (3, 1, 4), (4, 1, 5)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3, 4, 5}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation3050 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation3050 G := by
  use ℕ, PartialSolution.counter3050.toMagma, PartialSolution.counter3050.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter3050.of_R 1 1 2] | rw [PartialSolution.counter3050.of_R 2 1 3] | rw [PartialSolution.counter3050.of_R 3 1 4] | rw [PartialSolution.counter3050.of_R 4 1 5])
  all_goals simp [PartialSolution.counter3050]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter4380 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation4380 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation4380 G := by
  use ℕ, PartialSolution.counter4380.toMagma, PartialSolution.counter4380.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter4380.of_R 1 1 2] | rw [PartialSolution.counter4380.of_R 1 2 1] | rw [PartialSolution.counter4380.of_R 2 1 3])
  all_goals simp [PartialSolution.counter4380]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter4435 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (1, 2, 1), (2, 1, 3)} : Finset _)
  rule_0 := by solution_enumerator
  rule_1 := by solution_enumerator
  rule_2 := by solution_enumerator
  rule_3 := by solution_enumerator
  rule_4 := by solution_enumerator
  rule_5 := by solution_enumerator
  rule_6 := by solution_enumerator
  rule_7 := by solution_enumerator
  rule_8 := by solution_enumerator
  rule_9 := by solution_enumerator
  rule_10 := by solution_enumerator
  rule_11 := by solution_enumerator
  rule_12 := by solution_enumerator
  rule_13 := by solution_enumerator
  rule_14 := by solution_enumerator
  rule_15 := by solution_enumerator
  finsupp := {1, 2, 3}
  mem_1 := by solution_enumerator
  mem_2 := by solution_enumerator
  mem_3 := by solution_enumerator

@[equational_result]
theorem _root_.Equation511_not_implies_Equation4435 : ∃ (G : Type) (_ : Magma G), Equation511 G ∧ ¬Equation4435 G := by
  use ℕ, PartialSolution.counter4435.toMagma, PartialSolution.counter4435.toMagma_equation511
  simp only [not_forall, PartialSolution.toMagma]
  use 1, 1
  repeat (first | rw [PartialSolution.counter4435.of_R 1 1 2] | rw [PartialSolution.counter4435.of_R 1 2 1] | rw [PartialSolution.counter4435.of_R 2 1 3])
  all_goals simp [PartialSolution.counter4435]

end Eq511
