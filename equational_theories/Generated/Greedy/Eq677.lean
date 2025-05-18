import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq677

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq97 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 68,69
  have eq98 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 68,70
  have eq110 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq97 rule_def_1_1 -- resolution 97,64
  have eq111 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq97 rule_def_1_0 -- resolution 97,63
  have eq117 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk3 := resolve eq98 rule_def_1_1 -- resolution 98,64
  have eq118 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq98 rule_def_1_0 -- resolution 98,63
  have eq120 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk1 := resolve eq110 rule_def_0_1 -- resolution 110,60
  have eq140 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq111 rule_def_0_2 -- resolution 111,61
  have eq141 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq111 rule_def_0_1 -- resolution 111,60
  have eq142 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq111 rule_def_0_0 -- resolution 111,59
  have eq151 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ c = sk1 := resolve eq141 old_0 -- resolution 141,52
  have eq153 : (old sk0 sk1 sk3) ∨ a = sk3 ∨ c = sk3 := resolve eq117 rule_def_0_2 -- resolution 117,61
  have eq154 : (old sk0 sk1 sk3) ∨ a = sk3 ∨ b = sk1 := resolve eq117 rule_def_0_1 -- resolution 117,60
  have eq158 (X0 : G) : ¬(old sk0 sk1 X0) ∨ a = sk0 ∨ sk2 = X0 ∨ c = sk1 := resolve eq142 old_0 -- resolution 142,52
  have eq160 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq118 rule_def_0_2 -- resolution 118,61
  have eq161 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq118 rule_def_0_1 -- resolution 118,60
  have eq162 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq118 rule_def_0_0 -- resolution 118,59
  have eq364 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq151 eq161 -- resolution 151,161
  have eq371 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq364 rfl -- duplicate literal removal 364
  have eq378 : b = sk1 ∨ c = sk1 := resolve eq371 preserve_2 -- subsumption resolution 371,71
  have eq393 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq378.imp_left (fun h : b = sk1 ↦ superpose h eq140)) -- superposition 140,378, 378 into 140, unify on (0).2 in 378 and (0).2 in 140
  have eq398 : (old sk0 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq378.imp_left (fun h : b = sk1 ↦ superpose h eq160)) -- superposition 160,378, 378 into 160, unify on (0).2 in 378 and (0).2 in 160
  have eq403 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq393 bc -- subsumption resolution 393,47
  have eq406 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq398 bc -- subsumption resolution 398,47
  have eq414 : a = sk0 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq158 eq162 -- resolution 158,162
  have eq424 : a = sk0 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq414 rfl -- duplicate literal removal 414
  have eq429 : c = sk1 ∨ a = sk0 := resolve eq424 preserve_2 -- subsumption resolution 424,71
  have eq436 : (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ a = sk2 ∨ a = sk0 := Or.assoc3 (eq429.imp_left (fun h : c = sk1 ↦ superpose h eq110)) -- superposition 110,429, 429 into 110, unify on (0).2 in 429 and (0).2 in 110
  have eq438 : (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ a = sk3 ∨ a = sk0 := Or.assoc3 (eq429.imp_left (fun h : c = sk1 ↦ superpose h eq117)) -- superposition 117,429, 429 into 117, unify on (0).2 in 429 and (0).2 in 117
  have eq457 : (sP0 sk0 c sk2) ∨ a = sk2 ∨ a = sk0 := resolve eq436 p4XZ -- subsumption resolution 436,50
  have eq458 : a = sk2 ∨ a = sk0 := resolve eq457 rule_def_0_0 -- subsumption resolution 457,59
  have eq459 : (sP0 sk0 c sk3) ∨ a = sk3 ∨ a = sk0 := resolve eq438 p4XZ -- subsumption resolution 438,50
  have eq460 : a = sk3 ∨ a = sk0 := resolve eq459 rule_def_0_0 -- subsumption resolution 459,59
  have eq508 : a ≠ sk2 ∨ a = sk0 := eq460.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 71,460, 460 into 71, unify on (0).2 in 460 and (0).2 in 71
  have eq516 : a = sk0 := resolve eq508 eq458 -- subsumption resolution 508,458
  have eq530 : (old a sk1 sk2) ∨ a = sk2 ∨ b = sk1 := Eq.mp (by simp only [eq516, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120 -- backward demodulation 120,516
  have eq547 : (old a sk1 sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq516, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq153 -- backward demodulation 153,516
  have eq548 : (old a sk1 sk3) ∨ a = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq516, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq154 -- backward demodulation 154,516
  have eq602 : (old a b sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq516, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq403 -- backward demodulation 403,516
  have eq604 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq516, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq406 -- backward demodulation 406,516
  have eq675 : c = sk2 ∨ c = sk1 := resolve eq602 p3 -- subsumption resolution 602,48
  have eq676 : c = sk3 ∨ c = sk1 := resolve eq604 p3 -- subsumption resolution 604,48
  have eq698 : c ≠ sk2 ∨ c = sk1 := eq676.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 71,676, 676 into 71, unify on (0).2 in 676 and (0).2 in 71
  have eq701 : c = sk1 := resolve eq698 eq675 -- subsumption resolution 698,675
  have eq707 : c = b ∨ (old a sk1 sk2) ∨ a = sk2 := Eq.mp (by simp only [eq701, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq530 -- backward demodulation 530,701
  have eq712 : (old a c sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq701, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq547 -- backward demodulation 547,701
  have eq713 : c = b ∨ (old a sk1 sk3) ∨ a = sk3 := Eq.mp (by simp only [eq701, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq548 -- backward demodulation 548,701
  have eq747 : (old a sk1 sk2) ∨ a = sk2 := resolve eq707 bc -- subsumption resolution 707,47
  have eq748 : (old a c sk2) ∨ a = sk2 := Eq.mp (by simp only [eq701, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq747 -- forward demodulation 747,701
  have eq749 : a = sk2 := resolve eq748 p4XZ -- subsumption resolution 748,50
  have eq750 : a ≠ sk3 := Eq.mp (by simp only [eq749, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 71,749
  have eq752 : a = sk3 ∨ c = sk3 := resolve eq712 p4XZ -- subsumption resolution 712,50
  have eq753 : c = sk3 := resolve eq752 eq750 -- subsumption resolution 752,750
  have eq755 : (old a sk1 sk3) ∨ a = sk3 := resolve eq713 bc -- subsumption resolution 713,47
  have eq756 : (old a sk1 sk3) := resolve eq755 eq750 -- subsumption resolution 755,750
  have eq757 : (old a sk1 c) := Eq.mp (by simp only [eq753, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq756 -- forward demodulation 756,753
  subsumption p4XY eq757 -- subsumption resolution 757,49

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X4 ∨ ¬ old X2 X0 X3 ∨ old X0 X4 X1)) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X2 X1 X3 ∨ old X2 X3 X1)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ a ≠ Z ∨ ¬ old X a X2 ∨ ¬ old X2 X b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X3 X4 ∨ ¬ new X2 X0 X3 ∨ new X0 X4 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq77 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 61
  have eq78 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq77 rfl -- equality resolution 77
  have eq79 : (new a b c) := resolve eq78 rfl -- equality resolution 78
  have eq80 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old X3 X0 b) ∨ ¬(old X0 a X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 65
  have eq81 (X0 X3 : G) : ¬(old X3 X0 b) ∨ (new X0 c a) ∨ ¬(old X0 a X3) := resolve eq80 rfl -- equality resolution 80
  have eq82 (X0 X1 X2 X3 : G) : ¬(sP1 X0 X1 X2) ∨ (sF0 X0 X1 X2) = X3 ∨ ¬(old X0 a X3) := resolve rule_def_1_2 old_0 -- resolution 68,55
  have eq84 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 68,54
  have eq88 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq79 -- resolution 72,79
  have eq91 (X0 : G) : ¬(new sk2 sk0 X0) ∨ sk3 = X0 := resolve prev_0 preserve_2 -- resolution 72,75
  have eq95 (X0 X1 X2 : G) : (new X0 c a) ∨ ¬(old X0 a (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve eq81 rule_def_1_3 -- resolution 81,69
  have eq96 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c a) := resolve eq95 rule_def_1_2 -- subsumption resolution 95,68
  have eq107 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 71,73
  have eq108 : (sP1 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) := resolve new_imp preserve_1 -- resolution 71,74
  have eq109 : (sP1 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ (sP0 sk2 sk0 sk3) := resolve new_imp preserve_2 -- resolution 71,75
  have eq121 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq107 rule_def_1_1 -- resolution 107,67
  have eq122 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq107 rule_def_1_0 -- resolution 107,66
  have eq126 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ (new sk1 c a) := resolve eq108 eq96 -- resolution 108,96
  have eq127 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ a = sk4 := resolve eq108 rule_def_1_1 -- resolution 108,67
  have eq128 : (sP0 sk1 sk3 sk4) ∨ (old sk1 sk3 sk4) ∨ c = sk3 := resolve eq108 rule_def_1_0 -- resolution 108,66
  have eq129 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq121 rule_def_0_2 -- resolution 121,64
  have eq131 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ a = sk0 := resolve eq121 rule_def_0_0 -- resolution 121,62
  have eq133 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ a = sk3 := resolve eq109 rule_def_1_1 -- resolution 109,67
  have eq134 : (sP0 sk2 sk0 sk3) ∨ (old sk2 sk0 sk3) ∨ c = sk0 := resolve eq109 rule_def_1_0 -- resolution 109,66
  have eq141 (X0 : G) : ¬(old sk1 a X0) ∨ (sF0 sk1 sk3 sk4) = X0 ∨ (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) := resolve eq82 eq108 -- resolution 82,108
  have eq154 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq122 rule_def_0_2 -- resolution 122,64
  have eq159 (X0 : G) : ¬(old sk1 sk2 X0) ∨ c = sk2 ∨ (old sk0 sk2 sk1) ∨ c = sk1 ∨ ¬(old X0 sk1 sk0) := resolve eq154 old_4 -- resolution 154,59
  have eq176 : (old sk1 sk3 sk4) ∨ a = sk4 ∨ b = sk3 := resolve eq127 rule_def_0_1 -- resolution 127,63
  have eq184 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ c = sk4 := resolve eq128 rule_def_0_2 -- resolution 128,64
  have eq185 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ b = sk3 := resolve eq128 rule_def_0_1 -- resolution 128,63
  have eq186 : (old sk1 sk3 sk4) ∨ c = sk3 ∨ a = sk1 := resolve eq128 rule_def_0_0 -- resolution 128,62
  have eq192 : (old sk2 sk0 sk3) ∨ a = sk3 ∨ b = sk0 := resolve eq133 rule_def_0_1 -- resolution 133,63
  have eq193 : (old sk2 sk0 sk3) ∨ a = sk3 ∨ a = sk2 := resolve eq133 rule_def_0_0 -- resolution 133,62
  have eq198 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ c = sk3 := resolve eq134 rule_def_0_2 -- resolution 134,64
  have eq199 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ b = sk0 := resolve eq134 rule_def_0_1 -- resolution 134,63
  have eq200 : (old sk2 sk0 sk3) ∨ c = sk0 ∨ a = sk2 := resolve eq134 rule_def_0_0 -- resolution 134,62
  have eq214 : (new sk1 c a) ∨ (old sk1 sk3 sk4) ∨ a = sk1 := resolve eq126 rule_def_0_0 -- resolution 126,62
  have eq238 (X0 X1 : G) : ¬(old sk0 X1 sk2) ∨ a = sk2 ∨ (old sk0 X0 X1) ∨ ¬(old X1 sk3 X0) ∨ a = sk3 := resolve eq193 old_1 -- resolution 193,56
  have eq242 (X0 X1 : G) : ¬(old sk0 X1 sk2) ∨ c = sk3 ∨ (old sk0 X0 X1) ∨ ¬(old X1 sk3 X0) ∨ c = sk0 := resolve eq198 old_1 -- resolution 198,56
  have eq250 (X0 X1 : G) : ¬(sP1 sk1 X0 X1) ∨ (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (sF0 sk1 sk3 sk4) = (sF0 sk1 X0 X1) := resolve eq141 rule_def_1_2 -- resolution 141,68
  have eq252 (X0 X1 : G) : ¬(old sk0 X1 sk2) ∨ a = sk2 ∨ (old sk0 X0 X1) ∨ ¬(old X1 sk3 X0) ∨ c = sk0 := resolve eq200 old_1 -- resolution 200,56
  have eq272 : (old sk1 sk3 sk4) ∨ a = sk1 ∨ (sP0 sk1 c a) ∨ (old sk1 c a) ∨ (sP1 sk1 c a) := resolve eq214 new_imp -- resolution 214,71
  have eq274 : (old sk1 sk3 sk4) ∨ a = sk1 ∨ (sP0 sk1 c a) ∨ (sP1 sk1 c a) := resolve eq272 p4XZ -- subsumption resolution 272,53
  have eq275 : (sP1 sk1 c a) ∨ a = sk1 ∨ (old sk1 sk3 sk4) := resolve eq274 rule_def_0_0 -- subsumption resolution 274,62
  have eq320 : (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (sF0 sk1 sk3 sk4) = (sF0 sk1 c a) ∨ a = sk1 ∨ (old sk1 sk3 sk4) := resolve eq250 eq275 -- resolution 250,275
  have eq321 : (old sk1 sk3 sk4) ∨ (sP0 sk1 sk3 sk4) ∨ (sF0 sk1 sk3 sk4) = (sF0 sk1 c a) ∨ a = sk1 := resolve eq320 rfl -- duplicate literal removal 320
  have eq323 : (old sk1 sk3 sk4) ∨ (sF0 sk1 sk3 sk4) = (sF0 sk1 c a) ∨ a = sk1 := resolve eq321 rule_def_0_0 -- subsumption resolution 321,62
  have eq657 (X0 : G) : a = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old sk1 sk3 X0) ∨ a = sk3 ∨ a = sk2 ∨ c = sk2 := resolve eq238 eq129 -- resolution 238,129
  have eq666 (X0 : G) : ¬(old sk1 sk3 X0) ∨ (old sk0 X0 sk1) ∨ a = sk2 ∨ a = sk3 ∨ c = sk2 := resolve eq657 rfl -- duplicate literal removal 657
  have eq684 (X0 : G) : ¬(old sk1 sk3 X0) ∨ (old sk0 X0 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq242 eq154 -- resolution 242,154
  have eq693 : (old sk0 sk4 sk1) ∨ a = sk2 ∨ a = sk3 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 := resolve eq666 eq186 -- resolution 666,186
  have eq702 (X0 : G) : a = sk2 ∨ (old sk0 X0 sk1) ∨ ¬(old sk1 sk3 X0) ∨ c = sk0 ∨ a = sk2 ∨ c = sk2 := resolve eq252 eq129 -- resolution 252,129
  have eq711 (X0 : G) : ¬(old sk1 sk3 X0) ∨ (old sk0 X0 sk1) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 := resolve eq702 rfl -- duplicate literal removal 702
  have eq729 : (old sk0 sk4 sk1) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ c = sk4 := resolve eq711 eq184 -- resolution 711,184
  have eq730 : (old sk0 sk4 sk1) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ b = sk3 := resolve eq711 eq185 -- resolution 711,185
  have eq731 : (old sk0 sk4 sk1) ∨ a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 := resolve eq711 eq186 -- resolution 711,186
  have eq1161 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk4 := resolve eq684 eq184 -- resolution 684,184
  have eq1162 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ b = sk3 := resolve eq684 eq185 -- resolution 684,185
  have eq1163 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 := resolve eq684 eq186 -- resolution 684,186
  have eq1167 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq1163 rfl -- duplicate literal removal 1163
  have eq1168 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ b = sk3 := resolve eq1162 rfl -- duplicate literal removal 1162
  have eq1169 : (old sk0 sk4 sk1) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk4 := resolve eq1161 rfl -- duplicate literal removal 1161
  have eq2605 : a = sk2 ∨ a = sk3 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 ∨ (new sk0 sk4 sk1) := resolve eq693 imp_new_0 -- resolution 693,60
  have eq2624 : c = sk3 ∨ a = sk3 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq2605 preserve_3 -- subsumption resolution 2605,76
  have eq3039 : (sP0 sk2 sk0 c) ∨ (old sk2 sk0 c) ∨ a = c ∨ a = sk3 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq2624.imp_left (fun h : c = sk3 ↦ superpose h eq133)) -- superposition 133,2624, 2624 into 133, unify on (0).2 in 2624 and (0).3 in 133
  have eq3134 : (sP0 sk2 sk0 c) ∨ a = c ∨ a = sk3 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq3039 p4XY -- subsumption resolution 3039,52
  have eq3135 : (sP0 sk2 sk0 c) ∨ a = sk3 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq3134 ac -- subsumption resolution 3134,49
  have eq3136 : a = sk3 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq3135 rule_def_0_0 -- subsumption resolution 3135,62
  have eq4257 : a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ c = sk4 ∨ (new sk0 sk4 sk1) := resolve eq729 imp_new_0 -- resolution 729,60
  have eq4274 : c = sk4 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := resolve eq4257 preserve_3 -- subsumption resolution 4257,76
  have eq4281 : a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ b = sk3 ∨ (new sk0 sk4 sk1) := resolve eq730 imp_new_0 -- resolution 730,60
  have eq4314 : b = sk3 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := resolve eq4281 preserve_3 -- subsumption resolution 4281,76
  have eq4340 : a = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk1 ∨ (new sk0 sk4 sk1) := resolve eq731 imp_new_0 -- resolution 731,60
  have eq4373 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq4340 preserve_3 -- subsumption resolution 4340,76
  have eq5608 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ (new sk0 sk4 sk1) := resolve eq1167 imp_new_0 -- resolution 1167,60
  have eq5647 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq5608 preserve_3 -- subsumption resolution 5608,76
  have eq5773 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ b = sk3 ∨ (new sk0 sk4 sk1) := resolve eq1168 imp_new_0 -- resolution 1168,60
  have eq5814 : b = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq5773 preserve_3 -- subsumption resolution 5773,76
  have eq5941 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk4 ∨ (new sk0 sk4 sk1) := resolve eq1169 imp_new_0 -- resolution 1169,60
  have eq5962 : c = sk4 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq5941 preserve_3 -- subsumption resolution 5941,76
  have eq5976 : ¬(new sk0 c sk1) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := eq4274.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 76,4274, 4274 into 76, unify on (0).2 in 4274 and (0).2 in 76
  have eq6172 : (sP1 sk2 sk0 b) ∨ (old sk2 sk0 b) ∨ (sP0 sk2 sk0 b) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := Or.assoc3 (eq4314.imp_left (fun h : b = sk3 ↦ superpose h eq109)) -- superposition 109,4314, 4314 into 109, unify on (0).2 in 4314 and (0).3 in 109
  have eq6314 : (sP1 sk2 sk0 b) ∨ (old sk2 sk0 b) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := resolve eq6172 rule_def_0_0 -- subsumption resolution 6172,62
  have eq6315 : (old sk2 sk0 b) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := resolve eq6314 rule_def_1_0 -- subsumption resolution 6314,66
  have eq6375 : a = c ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := Or.assoc5 (eq3136.imp_left (fun h : a = sk3 ↦ superpose h eq4373)) -- superposition 4373,3136, 3136 into 4373, unify on (0).2 in 3136 and (0).2 in 4373
  have eq6484 : a = c ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq6375 rfl -- duplicate literal removal 6375
  have eq6490 : c = sk2 ∨ c = sk0 ∨ a = sk2 ∨ a = sk1 := resolve eq6484 ac -- subsumption resolution 6484,49
  have eq6540 : (old c sk0 sk3) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq6490.imp_left (fun h : c = sk2 ↦ superpose h eq199)) -- superposition 199,6490, 6490 into 199, unify on (0).2 in 6490 and (0).1 in 199
  have eq6541 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ c = sk0 ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq6490.imp_left (fun h : c = sk2 ↦ superpose h eq200)) -- superposition 200,6490, 6490 into 200, unify on (0).2 in 6490 and (0).1 in 200
  have eq6601 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ a = sk2 ∨ a = sk1 := resolve eq6541 rfl -- duplicate literal removal 6541
  have eq6602 : (old c sk0 sk3) ∨ c = sk0 ∨ b = sk0 ∨ a = sk2 ∨ a = sk1 := resolve eq6540 rfl -- duplicate literal removal 6540
  have eq6616 : a = sk2 ∨ b = sk0 ∨ c = sk0 ∨ a = sk1 := resolve eq6602 p4YZ -- subsumption resolution 6602,54
  have eq6617 : c = sk0 ∨ a = c ∨ a = sk2 ∨ a = sk1 := resolve eq6601 p4YZ -- subsumption resolution 6601,54
  have eq6618 : a = sk2 ∨ c = sk0 ∨ a = sk1 := resolve eq6617 ac -- subsumption resolution 6617,49
  have eq6671 (X0 : G) : ¬(new a sk0 X0) ∨ sk3 = X0 ∨ c = sk0 ∨ a = sk1 := Or.assoc2 (eq6618.imp_left (fun h : a = sk2 ↦ superpose h eq91)) -- superposition 91,6618, 6618 into 91, unify on (0).2 in 6618 and (0).1 in 91
  have eq6683 (X0 : G) : ¬(old sk1 a X0) ∨ a = c ∨ (old sk0 a sk1) ∨ c = sk1 ∨ ¬(old X0 sk1 sk0) ∨ c = sk0 ∨ a = sk1 := Or.assoc5 (eq6618.imp_left (fun h : a = sk2 ↦ superpose h eq159)) -- superposition 159,6618, 6618 into 159, unify on (0).2 in 6618 and (0).2 in 159
  have eq6688 : (old a sk0 sk3) ∨ c = sk0 ∨ c = sk3 ∨ c = sk0 ∨ a = sk1 := Or.assoc3 (eq6618.imp_left (fun h : a = sk2 ↦ superpose h eq198)) -- superposition 198,6618, 6618 into 198, unify on (0).2 in 6618 and (0).1 in 198
  have eq6722 : (old a sk0 sk3) ∨ c = sk0 ∨ c = sk3 ∨ a = sk1 := resolve eq6688 rfl -- duplicate literal removal 6688
  have eq6727 (X0 : G) : ¬(old sk1 a X0) ∨ (old sk0 a sk1) ∨ c = sk1 ∨ ¬(old X0 sk1 sk0) ∨ c = sk0 ∨ a = sk1 := resolve eq6683 ac -- subsumption resolution 6683,49
  have eq9059 : (new sk2 sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := eq5647.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 75,5647, 5647 into 75, unify on (0).2 in 5647 and (0).3 in 75
  have eq9077 : (old sk2 sk0 c) ∨ a = c ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := Or.assoc3 (eq5647.imp_left (fun h : c = sk3 ↦ superpose h eq192)) -- superposition 192,5647, 5647 into 192, unify on (0).2 in 5647 and (0).3 in 192
  have eq9183 : a = c ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq9077 p4XY -- subsumption resolution 9077,52
  have eq9184 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ a = sk1 := resolve eq9183 ac -- subsumption resolution 9183,49
  have eq9223 : (new sk1 b sk4) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := eq5814.imp_left (fun h : b = sk3 ↦ superpose h preserve_1) -- superposition 74,5814, 5814 into 74, unify on (0).2 in 5814 and (0).2 in 74
  have eq9404 : ¬(new sk0 c sk1) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := eq5962.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 76,5962, 5962 into 76, unify on (0).2 in 5962 and (0).2 in 76
  have eq12288 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ a = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk1 := Or.assoc5 (eq6616.imp_left (fun h : a = sk2 ↦ superpose h eq9184)) -- superposition 9184,6616, 6616 into 9184, unify on (0).2 in 6616 and (0).2 in 9184
  have eq12404 : a = c ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 ∨ a = sk1 := resolve eq12288 rfl -- duplicate literal removal 12288
  have eq12405 : c = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq12404 ac -- subsumption resolution 12404,49
  have eq12508 : (sP1 c c a) ∨ a = c ∨ (old c sk3 sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := Or.assoc3 (eq12405.imp_left (fun h : c = sk1 ↦ superpose h eq275)) -- superposition 275,12405, 12405 into 275, unify on (0).2 in 12405 and (0).1 in 275
  have eq12673 : a = c ∨ (old c sk3 sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq12508 eq84 -- subsumption resolution 12508,84
  have eq12674 : (old c sk3 sk4) ∨ c = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq12673 ac -- subsumption resolution 12673,49
  have eq12675 : a = sk1 ∨ b = sk0 ∨ c = sk0 := resolve eq12674 p4YZ -- subsumption resolution 12674,54
  have eq12717 : (old sk0 a sk2) ∨ a = c ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq12675.imp_left (fun h : a = sk1 ↦ superpose h eq154)) -- superposition 154,12675, 12675 into 154, unify on (0).2 in 12675 and (0).2 in 154
  have eq12923 : (old sk0 a sk2) ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := resolve eq12717 ac -- subsumption resolution 12717,49
  have eq34950 : ¬(old sk0 a sk2) ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 ∨ (new sk0 c a) ∨ c = sk0 := resolve eq6315 eq81 -- resolution 6315,81
  have eq41698 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ a = c ∨ a = sk1 ∨ c = sk0 ∨ a = sk1 := Or.assoc5 (eq6618.imp_left (fun h : a = sk2 ↦ superpose h eq9059)) -- superposition 9059,6618, 6618 into 9059, unify on (0).2 in 6618 and (0).1 in 9059
  have eq41699 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ a = c ∨ a = sk1 := resolve eq41698 rfl -- duplicate literal removal 41698
  have eq41705 : (new a sk0 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 := resolve eq41699 ac -- subsumption resolution 41699,49
  have eq41919 : c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 ∨ c = sk0 ∨ a = sk1 := resolve eq41705 eq6671 -- resolution 41705,6671
  have eq41922 : c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq41919 rfl -- duplicate literal removal 41919
  have eq42166 : (sP0 sk1 c sk4) ∨ (old sk1 c sk4) ∨ a = sk4 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := Or.assoc3 (eq41922.imp_left (fun h : c = sk3 ↦ superpose h eq127)) -- superposition 127,41922, 41922 into 127, unify on (0).2 in 41922 and (0).2 in 127
  have eq42353 : (sP0 sk1 c sk4) ∨ a = sk4 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq42166 p4XZ -- subsumption resolution 42166,53
  have eq42354 : a = sk4 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq42353 rule_def_0_0 -- subsumption resolution 42353,62
  have eq42545 : ¬(new sk0 a sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := eq42354.imp_left (fun h : a = sk4 ↦ superpose h preserve_3) -- superposition 76,42354, 42354 into 76, unify on (0).2 in 42354 and (0).2 in 76
  have eq44392 : (new a b sk4) ∨ c = sk0 ∨ a = c ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := Or.assoc5 (eq12675.imp_left (fun h : a = sk1 ↦ superpose h eq9223)) -- superposition 9223,12675, 12675 into 9223, unify on (0).2 in 12675 and (0).1 in 9223
  have eq44493 : (new a b sk4) ∨ c = sk0 ∨ a = c ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 := resolve eq44392 rfl -- duplicate literal removal 44392
  have eq44495 : (new a b sk4) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 := resolve eq44493 ac -- subsumption resolution 44493,49
  have eq44691 : ¬(new sk0 c a) ∨ c = sk0 ∨ a = c ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := Or.assoc5 (eq12675.imp_left (fun h : a = sk1 ↦ superpose h eq9404)) -- superposition 9404,12675, 12675 into 9404, unify on (0).2 in 12675 and (0).3 in 9404
  have eq44692 : ¬(new sk0 c a) ∨ c = sk0 ∨ a = c ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 := resolve eq44691 rfl -- duplicate literal removal 44691
  have eq44694 : ¬(new sk0 c a) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 := resolve eq44692 ac -- subsumption resolution 44692,49
  have eq61328 : c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := resolve eq44495 eq88 -- resolution 44495,88
  have eq61508 : (old sk1 sk3 c) ∨ a = c ∨ b = sk3 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq61328.imp_left (fun h : c = sk4 ↦ superpose h eq176)) -- superposition 176,61328, 61328 into 176, unify on (0).2 in 61328 and (0).3 in 176
  have eq62084 : a = c ∨ b = sk3 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := resolve eq61508 p4XY -- subsumption resolution 61508,52
  have eq62085 : b = sk3 ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := resolve eq62084 ac -- subsumption resolution 62084,49
  have eq62148 : (sP1 sk2 sk0 b) ∨ (old sk2 sk0 b) ∨ (sP0 sk2 sk0 b) ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq62085.imp_left (fun h : b = sk3 ↦ superpose h eq109)) -- superposition 109,62085, 62085 into 109, unify on (0).2 in 62085 and (0).3 in 109
  have eq62461 : (sP1 sk2 sk0 b) ∨ (old sk2 sk0 b) ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := resolve eq62148 rule_def_0_1 -- subsumption resolution 62148,63
  have eq62462 : (old sk2 sk0 b) ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 := resolve eq62461 rule_def_1_0 -- subsumption resolution 62461,66
  have eq72610 : c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 ∨ (new sk0 c a) ∨ ¬(old sk0 a sk2) := resolve eq62462 eq81 -- resolution 62462,81
  have eq72634 : c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 ∨ ¬(old sk0 a sk2) := resolve eq72610 eq44694 -- subsumption resolution 72610,44694
  have eq72635 : c = sk3 ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := resolve eq72634 eq12923 -- subsumption resolution 72634,12923
  have eq72755 : (sP1 sk2 sk0 c) ∨ (old sk2 sk0 c) ∨ (sP0 sk2 sk0 c) ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq72635.imp_left (fun h : c = sk3 ↦ superpose h eq109)) -- superposition 109,72635, 72635 into 109, unify on (0).2 in 72635 and (0).3 in 109
  have eq73051 : (sP1 sk2 sk0 c) ∨ (sP0 sk2 sk0 c) ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := resolve eq72755 p4XY -- subsumption resolution 72755,52
  have eq73052 : (sP1 sk2 sk0 c) ∨ c = sk2 ∨ b = sk0 ∨ c = sk0 := resolve eq73051 rule_def_0_1 -- subsumption resolution 73051,63
  have eq73053 : c = sk2 ∨ b = sk0 ∨ c = sk0 := resolve eq73052 rule_def_1_0 -- subsumption resolution 73052,66
  have eq73151 : (sP1 c sk0 sk3) ∨ (old c sk0 sk3) ∨ (sP0 c sk0 sk3) ∨ b = sk0 ∨ c = sk0 := Or.assoc3 (eq73053.imp_left (fun h : c = sk2 ↦ superpose h eq109)) -- superposition 109,73053, 73053 into 109, unify on (0).2 in 73053 and (0).1 in 109
  have eq73346 : (old c sk0 sk3) ∨ (sP0 c sk0 sk3) ∨ b = sk0 ∨ c = sk0 := resolve eq73151 eq84 -- subsumption resolution 73151,84
  have eq73347 : (sP0 c sk0 sk3) ∨ b = sk0 ∨ c = sk0 := resolve eq73346 p4YZ -- subsumption resolution 73346,54
  have eq73348 : b = sk0 ∨ c = sk0 := resolve eq73347 rule_def_0_1 -- subsumption resolution 73347,63
  have eq73448 : (old sk2 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk0 := Or.assoc3 (eq73348.imp_left (fun h : b = sk0 ↦ superpose h eq198)) -- superposition 198,73348, 73348 into 198, unify on (0).2 in 73348 and (0).2 in 198
  have eq73752 : (old a b sk3) ∨ c = b ∨ c = sk3 ∨ a = sk1 ∨ c = sk0 := Or.assoc4 (eq73348.imp_left (fun h : b = sk0 ↦ superpose h eq6722)) -- superposition 6722,73348, 73348 into 6722, unify on (0).2 in 73348 and (0).2 in 6722
  have eq73828 : ¬(new b a sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = b ∨ c = sk0 := Or.assoc4 (eq73348.imp_left (fun h : b = sk0 ↦ superpose h eq42545)) -- superposition 42545,73348, 73348 into 42545, unify on (0).2 in 73348 and (0).1 in 42545
  have eq73834 : (old sk2 b sk3) ∨ c = sk3 ∨ c = sk0 := resolve eq73448 bc -- subsumption resolution 73448,50
  have eq73895 : c = b ∨ c = sk3 ∨ a = sk1 ∨ c = sk0 := resolve eq73752 p3 -- subsumption resolution 73752,51
  have eq73896 : c = sk3 ∨ a = sk1 ∨ c = sk0 := resolve eq73895 bc -- subsumption resolution 73895,50
  have eq73934 : ¬(new b a sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq73828 bc -- subsumption resolution 73828,50
  have eq74473 : (sP1 sk1 c sk4) ∨ (old sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := Or.assoc3 (eq73896.imp_left (fun h : c = sk3 ↦ superpose h eq108)) -- superposition 108,73896, 73896 into 108, unify on (0).2 in 73896 and (0).2 in 108
  have eq74500 : (old sk1 c sk4) ∨ (sF0 sk1 c a) = (sF0 sk1 c sk4) ∨ a = sk1 ∨ a = sk1 ∨ c = sk0 := Or.assoc3 (eq73896.imp_left (fun h : c = sk3 ↦ superpose h eq323)) -- superposition 323,73896, 73896 into 323, unify on (0).2 in 73896 and (0).2 in 323
  have eq74733 : (old sk1 c sk4) ∨ (sF0 sk1 c a) = (sF0 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq74500 rfl -- duplicate literal removal 74500
  have eq74761 : (sP1 sk1 c sk4) ∨ (sP0 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq74473 p4XZ -- subsumption resolution 74473,53
  have eq74762 : (sP1 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq74761 rule_def_0_0 -- subsumption resolution 74761,62
  have eq74769 : (sF0 sk1 c a) = (sF0 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq74733 p4XZ -- subsumption resolution 74733,53
  have eq84233 : (old sk1 a (sF0 sk1 c a)) ∨ ¬(sP1 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := Or.assoc2 (eq74769.imp_left (fun h : (sF0 sk1 c a) = (sF0 sk1 c sk4) ↦ superpose h rule_def_1_2)) -- superposition 68,74769, 74769 into 68, unify on (0).2 in 74769 and (0).3 in 68
  have eq84234 : (old (sF0 sk1 c a) sk1 b) ∨ ¬(sP1 sk1 c sk4) ∨ a = sk1 ∨ c = sk0 := Or.assoc2 (eq74769.imp_left (fun h : (sF0 sk1 c a) = (sF0 sk1 c sk4) ↦ superpose h rule_def_1_3)) -- superposition 69,74769, 74769 into 69, unify on (0).2 in 74769 and (0).1 in 69
  have eq84267 : (old sk1 a (sF0 sk1 c a)) ∨ a = sk1 ∨ c = sk0 := resolve eq84233 eq74762 -- subsumption resolution 84233,74762
  have eq84268 : (old (sF0 sk1 c a) sk1 b) ∨ a = sk1 ∨ c = sk0 := resolve eq84234 eq74762 -- subsumption resolution 84234,74762
  have eq209024 : (old sk0 a sk1) ∨ c = sk1 ∨ ¬(old (sF0 sk1 c a) sk1 sk0) ∨ c = sk0 ∨ a = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq6727 eq84267 -- resolution 6727,84267
  have eq209040 : ¬(old (sF0 sk1 c a) sk1 sk0) ∨ c = sk1 ∨ (old sk0 a sk1) ∨ c = sk0 ∨ a = sk1 := resolve eq209024 rfl -- duplicate literal removal 209024
  have eq209072 : ¬(old (sF0 sk1 c a) sk1 b) ∨ c = sk1 ∨ (old b a sk1) ∨ c = b ∨ a = sk1 ∨ c = sk0 := Or.assoc5 (eq73348.imp_left (fun h : b = sk0 ↦ superpose h eq209040)) -- superposition 209040,73348, 73348 into 209040, unify on (0).2 in 73348 and (0).3 in 209040
  have eq209074 : ¬(old (sF0 sk1 c a) sk1 b) ∨ c = sk1 ∨ (old b a sk1) ∨ a = sk1 ∨ c = sk0 := resolve eq209072 bc -- subsumption resolution 209072,50
  have eq209075 : (old b a sk1) ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq209074 eq84268 -- subsumption resolution 209074,84268
  have eq209202 : c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ (new b a sk1) := resolve eq209075 imp_new_0 -- resolution 209075,60
  have eq209206 : c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq209202 eq73934 -- subsumption resolution 209202,73934
  have eq209261 : (sP1 c c a) ∨ a = c ∨ (old c sk3 sk4) ∨ a = sk1 ∨ c = sk0 := Or.assoc3 (eq209206.imp_left (fun h : c = sk1 ↦ superpose h eq275)) -- superposition 275,209206, 209206 into 275, unify on (0).2 in 209206 and (0).1 in 275
  have eq210755 : a = c ∨ (old c sk3 sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq209261 eq84 -- subsumption resolution 209261,84
  have eq210756 : (old c sk3 sk4) ∨ a = sk1 ∨ c = sk0 := resolve eq210755 ac -- subsumption resolution 210755,49
  have eq210757 : a = sk1 ∨ c = sk0 := resolve eq210756 p4YZ -- subsumption resolution 210756,54
  have eq210764 : (new sk0 a sk2) ∨ c = sk0 := eq210757.imp_left (fun h : a = sk1 ↦ superpose h preserve_0) -- superposition 73,210757, 210757 into 73, unify on (0).2 in 210757 and (0).2 in 73
  have eq210766 : ¬(new sk0 sk4 a) ∨ c = sk0 := eq210757.imp_left (fun h : a = sk1 ↦ superpose h preserve_3) -- superposition 76,210757, 210757 into 76, unify on (0).2 in 210757 and (0).3 in 76
  have eq210790 : (old sk0 a sk2) ∨ a = c ∨ c = sk2 ∨ c = sk0 := Or.assoc3 (eq210757.imp_left (fun h : a = sk1 ↦ superpose h eq154)) -- superposition 154,210757, 210757 into 154, unify on (0).2 in 210757 and (0).2 in 154
  have eq211128 : ¬(new sk0 c a) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 ∨ c = sk0 := Or.assoc5 (eq210757.imp_left (fun h : a = sk1 ↦ superpose h eq5976)) -- superposition 5976,210757, 210757 into 5976, unify on (0).2 in 210757 and (0).3 in 5976
  have eq212351 : ¬(new sk0 c a) ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 := resolve eq211128 rfl -- duplicate literal removal 211128
  have eq212498 : (old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq210790 ac -- subsumption resolution 210790,49
  have eq214352 : c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 ∨ (new sk0 c a) ∨ c = sk0 := resolve eq212498 eq34950 -- resolution 212498,34950
  have eq214437 : c = sk2 ∨ c = sk0 ∨ c = sk3 ∨ a = sk2 ∨ (new sk0 c a) := resolve eq214352 rfl -- duplicate literal removal 214352
  have eq214442 : c = sk3 ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 := resolve eq214437 eq212351 -- subsumption resolution 214437,212351
  have eq216187 : (sP1 sk2 sk0 c) ∨ (old sk2 sk0 c) ∨ (sP0 sk2 sk0 c) ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 := Or.assoc3 (eq214442.imp_left (fun h : c = sk3 ↦ superpose h eq109)) -- superposition 109,214442, 214442 into 109, unify on (0).2 in 214442 and (0).3 in 109
  have eq216918 : (sP1 sk2 sk0 c) ∨ (sP0 sk2 sk0 c) ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 := resolve eq216187 p4XY -- subsumption resolution 216187,52
  have eq216919 : (sP1 sk2 sk0 c) ∨ c = sk0 ∨ c = sk2 ∨ a = sk2 := resolve eq216918 rule_def_0_0 -- subsumption resolution 216918,62
  have eq216920 : c = sk2 ∨ c = sk0 ∨ a = sk2 := resolve eq216919 rule_def_1_0 -- subsumption resolution 216919,66
  have eq217009 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ c = sk0 ∨ a = sk2 := Or.assoc3 (eq216920.imp_left (fun h : c = sk2 ↦ superpose h eq200)) -- superposition 200,216920, 216920 into 200, unify on (0).2 in 216920 and (0).1 in 200
  have eq217565 : (old c sk0 sk3) ∨ c = sk0 ∨ a = c ∨ a = sk2 := resolve eq217009 rfl -- duplicate literal removal 217009
  have eq217583 : c = sk0 ∨ a = c ∨ a = sk2 := resolve eq217565 p4YZ -- subsumption resolution 217565,54
  have eq217584 : a = sk2 ∨ c = sk0 := resolve eq217583 ac -- subsumption resolution 217583,49
  have eq217927 : (old a b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk0 := Or.assoc3 (eq217584.imp_left (fun h : a = sk2 ↦ superpose h eq73834)) -- superposition 73834,217584, 217584 into 73834, unify on (0).2 in 217584 and (0).1 in 73834
  have eq218011 : (new sk0 a a) ∨ c = sk0 ∨ c = sk0 := Or.assoc2 (eq217584.imp_left (fun h : a = sk2 ↦ superpose h eq210764)) -- superposition 210764,217584, 217584 into 210764, unify on (0).2 in 217584 and (0).3 in 210764
  have eq218028 : (new sk0 a a) ∨ c = sk0 := resolve eq218011 rfl -- duplicate literal removal 218011
  have eq218088 : (old a b sk3) ∨ c = sk3 ∨ c = sk0 := resolve eq217927 rfl -- duplicate literal removal 217927
  have eq218232 : c = sk3 ∨ c = sk0 := resolve eq218088 p3 -- subsumption resolution 218088,51
  have eq218364 : (old sk1 c sk4) ∨ a = sk4 ∨ c = b ∨ c = sk0 := Or.assoc3 (eq218232.imp_left (fun h : c = sk3 ↦ superpose h eq176)) -- superposition 176,218232, 218232 into 176, unify on (0).2 in 218232 and (0).2 in 176
  have eq219000 : a = sk4 ∨ c = b ∨ c = sk0 := resolve eq218364 p4XZ -- subsumption resolution 218364,53
  have eq219001 : a = sk4 ∨ c = sk0 := resolve eq219000 bc -- subsumption resolution 219000,50
  have eq219681 : ¬(new sk0 a a) ∨ c = sk0 ∨ c = sk0 := Or.assoc2 (eq219001.imp_left (fun h : a = sk4 ↦ superpose h eq210766)) -- superposition 210766,219001, 219001 into 210766, unify on (0).2 in 219001 and (0).2 in 210766
  have eq219686 : ¬(new sk0 a a) ∨ c = sk0 := resolve eq219681 rfl -- duplicate literal removal 219681
  have eq219989 : c = sk0 := resolve eq219686 eq218028 -- subsumption resolution 219686,218028
  have eq220002 : (old c sk1 sk2) ∨ a = sk2 ∨ a = sk0 := Eq.mp (by simp only [eq219989, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq131 -- backward demodulation 131,219989
  have eq220017 : (old c sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq219989, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq154 -- backward demodulation 154,219989
  have eq222879 : a = sk2 ∨ a = sk0 := resolve eq220002 p4YZ -- subsumption resolution 220002,54
  have eq222880 : a = c ∨ a = sk2 := Eq.mp (by simp only [eq219989, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq222879 -- forward demodulation 222879,219989
  have eq222881 : a = sk2 := resolve eq222880 ac -- subsumption resolution 222880,49
  have eq223011 : c = sk1 ∨ c = sk2 := resolve eq220017 p4YZ -- subsumption resolution 220017,54
  have eq223012 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq222881, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq223011 -- forward demodulation 223011,222881
  have eq223013 : c = sk1 := resolve eq223012 ac -- subsumption resolution 223012,49
  have eq223055 : (old c sk3 sk4) ∨ (sP1 sk1 c a) ∨ a = sk1 := Eq.mp (by simp only [eq223013, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq275 -- backward demodulation 275,223013
  have eq223149 : (sP1 sk1 c a) ∨ a = sk1 := resolve eq223055 p4YZ -- subsumption resolution 223055,54
  have eq223150 : (sP1 c c a) ∨ a = sk1 := Eq.mp (by simp only [eq223013, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq223149 -- forward demodulation 223149,223013
  have eq223151 : a = sk1 := resolve eq223150 eq84 -- subsumption resolution 223150,84
  have eq223152 : a = c := Eq.mp (by simp only [eq223151, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq223013 -- backward demodulation 223013,223151
  subsumption ac eq223152 -- subsumption resolution 223152,49

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1, ¬ old X0 X1 X0 ∨ ¬ old X1 X0 X0 ∨ old X0 X0 X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X0 ∨ ¬ new X1 X0 X0 ∨ new X0 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq104 : (sP1 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) := resolve new_imp preserve_0 -- resolution 72,75
  have eq105 : (sP1 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ (sP0 sk1 sk0 sk0) := resolve new_imp preserve_1 -- resolution 72,76
  have eq127 : (old sk0 sk1 sk0) ∨ (sP0 sk0 sk1 sk0) ∨ a = sk0 := resolve eq104 rule_def_1_1 -- resolution 104,68
  have eq128 : (sP0 sk0 sk1 sk0) ∨ (old sk0 sk1 sk0) ∨ c = sk1 := resolve eq104 rule_def_1_0 -- resolution 104,67
  have eq129 : (old sk0 sk1 sk0) ∨ a = sk0 := resolve eq127 rule_def_0_0 -- subsumption resolution 127,63
  have eq135 : (sP0 sk1 sk0 sk0) ∨ (old sk1 sk0 sk0) ∨ a = sk0 := resolve eq105 rule_def_1_1 -- resolution 105,68
  have eq136 : (old sk1 sk0 sk0) ∨ (sP0 sk1 sk0 sk0) ∨ c = sk0 := resolve eq105 rule_def_1_0 -- resolution 105,67
  have eq137 : (old sk1 sk0 sk0) ∨ c = sk0 := resolve eq136 rule_def_0_2 -- subsumption resolution 136,65
  have eq139 : c = sk0 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq137 old_2 -- resolution 137,58
  have eq152 : (old sk0 sk1 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq128 rule_def_0_2 -- resolution 128,65
  have eq171 : (old sk1 sk0 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq135 rule_def_0_1 -- resolution 135,64
  have eq172 : (old sk1 sk0 sk0) ∨ a = sk0 ∨ a = sk1 := resolve eq135 rule_def_0_0 -- resolution 135,63
  have eq177 : a = sk0 ∨ b = sk0 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq171 old_2 -- resolution 171,58
  have eq182 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = sk0 := resolve eq177 eq129 -- subsumption resolution 177,129
  have eq187 : a = sk0 ∨ a = sk1 ∨ (old sk0 sk0 sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq172 old_2 -- resolution 172,58
  have eq192 : (old sk0 sk0 sk1) ∨ a = sk1 ∨ a = sk0 := resolve eq187 eq129 -- subsumption resolution 187,129
  have eq196 : b = sk0 ∨ a = sk0 ∨ (new sk0 sk0 sk1) := resolve eq182 imp_new_0 -- resolution 182,61
  have eq197 : b = sk0 ∨ a = sk0 := resolve eq196 preserve_2 -- subsumption resolution 196,77
  have eq213 : (old sk1 b b) ∨ c = b ∨ a = sk0 := Or.assoc2 (eq197.imp_left (fun h : b = sk0 ↦ superpose h eq137)) -- superposition 137,197, 197 into 137, unify on (0).2 in 197 and (0).2 in 137
  have eq220 : (old sk1 b b) ∨ a = sk0 := resolve eq213 bc -- subsumption resolution 213,51
  have eq255 : a = sk1 ∨ a = sk0 ∨ (new sk0 sk0 sk1) := resolve eq192 imp_new_0 -- resolution 192,61
  have eq257 : a = sk1 ∨ a = sk0 := resolve eq255 preserve_2 -- subsumption resolution 255,77
  have eq284 : (old a b b) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq257.imp_left (fun h : a = sk1 ↦ superpose h eq220)) -- superposition 220,257, 257 into 220, unify on (0).2 in 257 and (0).1 in 220
  have eq285 : (old a b b) ∨ a = sk0 := resolve eq284 rfl -- duplicate literal removal 284
  have eq297 : a = sk0 := resolve eq285 p3 -- subsumption resolution 285,52
  have eq300 : ¬(new a a sk1) := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 77,297
  have eq313 : (old sk1 a a) ∨ c = sk0 := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq137 -- backward demodulation 137,297
  have eq315 : (old a a sk1) ∨ c = sk0 ∨ ¬(old sk0 sk1 sk0) := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq139 -- backward demodulation 139,297
  have eq321 : (old a sk1 a) ∨ c = sk1 ∨ c = sk0 := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq152 -- backward demodulation 152,297
  have eq358 : a = c ∨ (old sk1 a a) := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq313 -- forward demodulation 313,297
  have eq359 : (old sk1 a a) := resolve eq358 ac -- subsumption resolution 358,50
  have eq364 : a = c ∨ (old a a sk1) ∨ ¬(old sk0 sk1 sk0) := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq315 -- forward demodulation 315,297
  have eq365 : (old a a sk1) ∨ ¬(old sk0 sk1 sk0) := resolve eq364 ac -- subsumption resolution 364,50
  have eq366 : ¬(old a sk1 a) ∨ (old a a sk1) := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq365 -- forward demodulation 365,297
  have eq380 : a = c ∨ (old a sk1 a) ∨ c = sk1 := Eq.mp (by simp only [eq297, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq321 -- forward demodulation 321,297
  have eq381 : (old a sk1 a) ∨ c = sk1 := resolve eq380 ac -- subsumption resolution 380,50
  have eq443 : (old a a sk1) ∨ c = sk1 := resolve eq366 eq381 -- resolution 366,381
  have eq447 : c = sk1 ∨ (new a a sk1) := resolve eq443 imp_new_0 -- resolution 443,61
  have eq448 : c = sk1 := resolve eq447 eq300 -- subsumption resolution 447,300
  have eq460 : (old c a a) := Eq.mp (by simp only [eq448, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq359 -- backward demodulation 359,448
  subsumption p4YZ eq460 -- subsumption resolution 460,55

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ ¬ old X2 X0 X0 ∨ X2 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ ¬ new X2 X0 X0 ∨ X2 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq90 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 72,58
  have eq114 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 75,79
  have eq115 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 75,80
  have eq116 : (sP1 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) := resolve new_imp preserve_2 -- resolution 75,81
  have eq138 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk1 := resolve eq114 rule_def_1_1 -- resolution 114,71
  have eq139 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq114 rule_def_1_0 -- resolution 114,70
  have eq142 : (old sk0 sk0 sk1) ∨ a = sk1 ∨ a = sk0 := resolve eq138 rule_def_0_0 -- resolution 138,66
  have eq144 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq115 rule_def_1_1 -- resolution 115,71
  have eq145 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq115 rule_def_1_0 -- resolution 115,70
  have eq151 : (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ a = sk0 := resolve eq116 rule_def_1_1 -- resolution 116,71
  have eq152 : (old sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ c = sk0 := resolve eq116 rule_def_1_0 -- resolution 116,70
  have eq153 : (old sk2 sk0 sk0) ∨ c = sk0 := resolve eq152 rule_def_0_2 -- subsumption resolution 152,68
  have eq154 (X0 : G) : c = sk0 ∨ sk0 = sk2 ∨ ¬(old sk0 X0 sk2) ∨ ¬(old sk0 sk0 X0) := resolve eq153 old_3 -- resolution 153,62
  have eq160 (X0 : G) : ¬(old sk0 sk0 X0) ∨ ¬(old sk0 X0 sk2) ∨ c = sk0 := resolve eq154 preserve_3 -- subsumption resolution 154,82
  have eq176 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq139 rule_def_0_2 -- resolution 139,68
  have eq198 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := resolve eq144 rule_def_0_2 -- resolution 144,68
  have eq217 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq145 rule_def_0_2 -- resolution 145,68
  have eq225 : (old sk2 sk0 sk0) ∨ a = sk0 ∨ b = sk0 := resolve eq151 rule_def_0_1 -- resolution 151,67
  have eq269 : ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq160 eq176 -- resolution 160,176
  have eq273 : ¬(old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq269 rfl -- duplicate literal removal 269
  have eq278 : c = sk0 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq273 eq217 -- resolution 273,217
  have eq282 : c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq278 rfl -- duplicate literal removal 278
  have eq292 : (sP1 c sk0 sk0) ∨ (old c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ c = sk1 ∨ c = sk0 := Or.assoc3 (eq282.imp_left (fun h : c = sk2 ↦ superpose h eq116)) -- superposition 116,282, 282 into 116, unify on (0).2 in 282 and (0).1 in 116
  have eq319 : (old c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq292 eq90 -- subsumption resolution 292,90
  have eq320 : (sP0 c sk0 sk0) ∨ c = sk1 ∨ c = sk0 := resolve eq319 p4YZ -- subsumption resolution 319,58
  have eq321 : c = sk1 ∨ c = sk0 := resolve eq320 rule_def_0_2 -- subsumption resolution 320,68
  have eq333 : (old sk0 sk0 c) ∨ a = c ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq321.imp_left (fun h : c = sk1 ↦ superpose h eq142)) -- superposition 142,321, 321 into 142, unify on (0).2 in 321 and (0).3 in 142
  have eq350 : a = c ∨ a = sk0 ∨ c = sk0 := resolve eq333 p4XY -- subsumption resolution 333,56
  have eq351 : c = sk0 ∨ a = sk0 := resolve eq350 ac -- subsumption resolution 350,53
  have eq439 : (old sk2 c c) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq351.imp_left (fun h : c = sk0 ↦ superpose h eq225)) -- superposition 225,351, 351 into 225, unify on (0).2 in 351 and (0).2 in 225
  have eq462 : a = c ∨ c = b ∨ a = sk0 := resolve eq439 p4XZ -- subsumption resolution 439,57
  have eq463 : c = b ∨ a = sk0 := resolve eq462 ac -- subsumption resolution 462,53
  have eq464 : a = sk0 := resolve eq463 bc -- subsumption resolution 463,54
  have eq468 : a ≠ sk2 := Eq.mp (by simp only [eq464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 82,464
  have eq493 : (old sk2 a a) ∨ c = sk0 := Eq.mp (by simp only [eq464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq153 -- backward demodulation 153,464
  have eq517 : (old a sk1 sk2) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq198 -- backward demodulation 198,464
  have eq565 : a = c ∨ c = sk1 := Eq.mp (by simp only [eq464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq321 -- backward demodulation 321,464
  have eq636 : a = c ∨ (old sk2 a a) := Eq.mp (by simp only [eq464, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq493 -- forward demodulation 493,464
  have eq637 : (old sk2 a a) := resolve eq636 ac -- subsumption resolution 636,53
  have eq692 : (old a sk1 sk2) ∨ c = sk2 := resolve eq517 eq468 -- subsumption resolution 517,468
  have eq734 : c = sk1 := resolve eq565 ac -- subsumption resolution 565,53
  have eq762 : (old a c sk2) ∨ c = sk2 := Eq.mp (by simp only [eq734, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq692 -- backward demodulation 692,734
  have eq825 : c = sk2 := resolve eq762 p4XZ -- subsumption resolution 762,57
  have eq832 : (old c a a) := Eq.mp (by simp only [eq825, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq637 -- backward demodulation 637,825
  subsumption p4YZ eq832 -- subsumption resolution 832,58

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_4 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X1 X3 X0 ∨ ¬ old X2 X1 X3 ∨ old X2 X3 X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, c ≠ Y ∨ a ≠ Z ∨ ¬ old X a X2 ∨ ¬ old X2 X b ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old (sF0 X Y Z) X b ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X1 X3 X0 ∨ ¬ new X2 X1 X3 ∨ new X2 X3 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq89 (X0 X1 X3 : G) : (new X0 X1 a) ∨ ¬(old X3 X0 b) ∨ ¬(old X0 a X3) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 71
  have eq90 (X0 X3 : G) : ¬(old X3 X0 b) ∨ (new X0 c a) ∨ ¬(old X0 a X3) := resolve eq89 rfl -- equality resolution 89
  have eq93 (X0 X1 : G) : ¬(sP1 c X0 X1) := resolve rule_def_1_2 p4YZ -- resolution 74,60
  have eq105 (X0 X1 X2 : G) : (new X0 c a) ∨ ¬(old X0 a (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve eq90 rule_def_1_3 -- resolution 90,75
  have eq106 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ (new X0 c a) := resolve eq105 rule_def_1_2 -- subsumption resolution 105,74
  have eq120 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 77,82
  have eq121 : (sP1 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (sP0 sk1 sk3 sk0) := resolve new_imp preserve_1 -- resolution 77,83
  have eq122 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) := resolve new_imp preserve_2 -- resolution 77,84
  have eq139 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (new sk0 c a) := resolve eq120 eq106 -- resolution 120,106
  have eq141 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq120 rule_def_1_0 -- resolution 120,72
  have eq146 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ (new sk1 c a) := resolve eq121 eq106 -- resolution 121,106
  have eq147 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ a = sk0 := resolve eq121 rule_def_1_1 -- resolution 121,73
  have eq148 : (sP0 sk1 sk3 sk0) ∨ (old sk1 sk3 sk0) ∨ c = sk3 := resolve eq121 rule_def_1_0 -- resolution 121,72
  have eq154 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk3 := resolve eq122 rule_def_1_1 -- resolution 122,73
  have eq155 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq122 rule_def_1_0 -- resolution 122,72
  have eq169 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq141 rule_def_0_2 -- resolution 141,70
  have eq171 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq141 rule_def_0_0 -- resolution 141,68
  have eq191 : (old sk1 sk3 sk0) ∨ a = sk0 ∨ c = sk0 := resolve eq147 rule_def_0_2 -- resolution 147,70
  have eq210 : (old sk1 sk3 sk0) ∨ c = sk3 ∨ c = sk0 := resolve eq148 rule_def_0_2 -- resolution 148,70
  have eq218 : (old sk2 sk1 sk3) ∨ a = sk3 ∨ b = sk1 := resolve eq154 rule_def_0_1 -- resolution 154,69
  have eq224 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq155 rule_def_0_2 -- resolution 155,70
  have eq226 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ a = sk2 := resolve eq155 rule_def_0_0 -- resolution 155,68
  have eq233 : (new sk0 c a) ∨ (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq139 rule_def_0_0 -- resolution 139,68
  have eq240 : (new sk1 c a) ∨ (old sk1 sk3 sk0) ∨ a = sk1 := resolve eq146 rule_def_0_0 -- resolution 146,68
  have eq256 (X0 : G) : ¬(old sk1 sk3 X0) ∨ c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old X0 sk1 sk2) := resolve eq224 old_4 -- resolution 224,65
  have eq283 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (sP0 sk0 c a) ∨ (old sk0 c a) ∨ (sP1 sk0 c a) := resolve eq233 new_imp -- resolution 233,77
  have eq285 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (sP0 sk0 c a) ∨ (sP1 sk0 c a) := resolve eq283 p4XZ -- subsumption resolution 283,59
  have eq286 : (sP1 sk0 c a) ∨ a = sk0 ∨ (old sk0 sk1 sk2) := resolve eq285 rule_def_0_0 -- subsumption resolution 285,68
  have eq298 : (old sk1 sk3 sk0) ∨ a = sk1 ∨ (sP0 sk1 c a) ∨ (old sk1 c a) ∨ (sP1 sk1 c a) := resolve eq240 new_imp -- resolution 240,77
  have eq300 : (old sk1 sk3 sk0) ∨ a = sk1 ∨ (sP0 sk1 c a) ∨ (sP1 sk1 c a) := resolve eq298 p4XZ -- subsumption resolution 298,59
  have eq301 : (sP1 sk1 c a) ∨ a = sk1 ∨ (old sk1 sk3 sk0) := resolve eq300 rule_def_0_0 -- subsumption resolution 300,68
  have eq874 : c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old sk0 sk1 sk2) ∨ a = sk0 ∨ c = sk0 := resolve eq256 eq191 -- resolution 256,191
  have eq877 : c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk3 ∨ c = sk0 := resolve eq256 eq210 -- resolution 256,210
  have eq884 : c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old sk0 sk1 sk2) ∨ c = sk0 := resolve eq877 rfl -- duplicate literal removal 877
  have eq885 : (old sk2 sk3 sk1) ∨ c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq874 eq171 -- subsumption resolution 874,171
  have eq1137 : c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ (new sk2 sk3 sk1) := resolve eq885 imp_new_0 -- resolution 885,66
  have eq1144 : c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1137 preserve_3 -- subsumption resolution 1137,85
  have eq1154 : (sP1 sk1 c sk0) ∨ (old sk1 c sk0) ∨ (sP0 sk1 c sk0) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq1144.imp_left (fun h : c = sk3 ↦ superpose h eq121)) -- superposition 121,1144, 1144 into 121, unify on (0).2 in 1144 and (0).2 in 121
  have eq1232 : (sP1 sk1 c sk0) ∨ (sP0 sk1 c sk0) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1154 p4XZ -- subsumption resolution 1154,59
  have eq1233 : (sP0 sk1 c sk0) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1232 rule_def_1_1 -- subsumption resolution 1232,73
  have eq1234 : c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1233 rule_def_0_2 -- subsumption resolution 1233,70
  have eq1253 : (sP1 c sk3 sk0) ∨ (old c sk3 sk0) ∨ (sP0 c sk3 sk0) ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq1234.imp_left (fun h : c = sk1 ↦ superpose h eq121)) -- superposition 121,1234, 1234 into 121, unify on (0).2 in 1234 and (0).1 in 121
  have eq1381 : (old c sk3 sk0) ∨ (sP0 c sk3 sk0) ∨ a = sk0 ∨ c = sk0 := resolve eq1253 eq93 -- subsumption resolution 1253,93
  have eq1382 : (sP0 c sk3 sk0) ∨ a = sk0 ∨ c = sk0 := resolve eq1381 p4YZ -- subsumption resolution 1381,60
  have eq1383 : c = sk0 ∨ a = sk0 := resolve eq1382 rule_def_0_2 -- subsumption resolution 1382,70
  have eq1448 : (sP1 c c a) ∨ a = c ∨ (old c sk1 sk2) ∨ a = sk0 := Or.assoc3 (eq1383.imp_left (fun h : c = sk0 ↦ superpose h eq286)) -- superposition 286,1383, 1383 into 286, unify on (0).2 in 1383 and (0).1 in 286
  have eq1492 : a = c ∨ (old c sk1 sk2) ∨ a = sk0 := resolve eq1448 eq93 -- subsumption resolution 1448,93
  have eq1493 : (old c sk1 sk2) ∨ a = sk0 := resolve eq1492 ac -- subsumption resolution 1492,55
  have eq1494 : a = sk0 := resolve eq1493 p4YZ -- subsumption resolution 1493,60
  have eq1520 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq1494, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq169 -- backward demodulation 169,1494
  have eq1574 : (sP1 sk1 c a) ∨ (old sk1 sk3 a) ∨ a = sk1 := Eq.mp (by simp only [eq1494, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq301 -- backward demodulation 301,1494
  have eq1627 : a = c ∨ c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old sk0 sk1 sk2) := Eq.mp (by simp only [eq1494, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq884 -- backward demodulation 884,1494
  have eq1745 : c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ ¬(old sk0 sk1 sk2) := resolve eq1627 ac -- subsumption resolution 1627,55
  have eq1746 : ¬(old a sk1 sk2) ∨ c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 := Eq.mp (by simp only [eq1494, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1745 -- forward demodulation 1745,1494
  have eq1893 : c = sk3 ∨ (old sk2 sk3 sk1) ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1746 eq1520 -- resolution 1746,1520
  have eq1896 : (old sk2 sk3 sk1) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1893 rfl -- duplicate literal removal 1893
  have eq1901 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ (new sk2 sk3 sk1) := resolve eq1896 imp_new_0 -- resolution 1896,66
  have eq1902 : c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq1901 preserve_3 -- subsumption resolution 1901,85
  have eq1918 : (old sk2 sk1 c) ∨ a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq1902.imp_left (fun h : c = sk3 ↦ superpose h eq218)) -- superposition 218,1902, 1902 into 218, unify on (0).2 in 1902 and (0).3 in 218
  have eq1939 : a = c ∨ b = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq1918 p4XY -- subsumption resolution 1918,58
  have eq1940 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq1939 ac -- subsumption resolution 1939,55
  have eq1955 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ (sP0 c sk1 sk3) ∨ c = sk1 ∨ b = sk1 := Or.assoc3 (eq1940.imp_left (fun h : c = sk2 ↦ superpose h eq122)) -- superposition 122,1940, 1940 into 122, unify on (0).2 in 1940 and (0).1 in 122
  have eq2028 : (old c sk1 sk3) ∨ (sP0 c sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq1955 eq93 -- subsumption resolution 1955,93
  have eq2029 : (sP0 c sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq2028 p4YZ -- subsumption resolution 2028,60
  have eq2030 : b = sk1 ∨ c = sk1 := resolve eq2029 rule_def_0_1 -- subsumption resolution 2029,69
  have eq2064 : (old a b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq2030.imp_left (fun h : b = sk1 ↦ superpose h eq1520)) -- superposition 1520,2030, 2030 into 1520, unify on (0).2 in 2030 and (0).2 in 1520
  have eq2097 : c = b ∨ c = sk2 ∨ c = sk1 := resolve eq2064 p3 -- subsumption resolution 2064,57
  have eq2098 : c = sk2 ∨ c = sk1 := resolve eq2097 bc -- subsumption resolution 2097,56
  have eq2120 : (old c sk1 sk3) ∨ c = sk1 ∨ a = c ∨ c = sk1 := Or.assoc3 (eq2098.imp_left (fun h : c = sk2 ↦ superpose h eq226)) -- superposition 226,2098, 2098 into 226, unify on (0).2 in 2098 and (0).1 in 226
  have eq2169 : (old c sk1 sk3) ∨ c = sk1 ∨ a = c := resolve eq2120 rfl -- duplicate literal removal 2120
  have eq2179 : c = sk1 ∨ a = c := resolve eq2169 p4YZ -- subsumption resolution 2169,60
  have eq2180 : c = sk1 := resolve eq2179 ac -- subsumption resolution 2179,55
  have eq2192 : (old sk2 c sk3) ∨ a = sk3 ∨ b = sk1 := Eq.mp (by simp only [eq2180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq218 -- backward demodulation 218,2180
  have eq2257 : a = c ∨ (sP1 sk1 c a) ∨ (old sk1 sk3 a) := Eq.mp (by simp only [eq2180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1574 -- backward demodulation 1574,2180
  have eq2335 : a = sk3 ∨ b = sk1 := resolve eq2192 p4XZ -- subsumption resolution 2192,59
  have eq2336 : c = b ∨ a = sk3 := Eq.mp (by simp only [eq2180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2335 -- forward demodulation 2335,2180
  have eq2337 : a = sk3 := resolve eq2336 bc -- subsumption resolution 2336,56
  have eq2439 : (sP1 sk1 c a) ∨ (old sk1 sk3 a) := resolve eq2257 ac -- subsumption resolution 2257,55
  have eq2440 : (sP1 c c a) ∨ (old sk1 sk3 a) := Eq.mp (by simp only [eq2180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2439 -- forward demodulation 2439,2180
  have eq2441 : (old sk1 sk3 a) := resolve eq2440 eq93 -- subsumption resolution 2440,93
  have eq2442 : (old sk1 a a) := Eq.mp (by simp only [eq2337, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2441 -- forward demodulation 2441,2337
  have eq2443 : (old c a a) := Eq.mp (by simp only [eq2180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2442 -- forward demodulation 2442,2180
  subsumption p4YZ eq2443 -- subsumption resolution 2443,60

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X a (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq94 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X0 := resolve rule_def_1_2 old_mem1 -- resolution 73,77
  have eq110 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq130 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk0 := resolve eq110 eq94 -- resolution 110,94
  have eq134 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq130 preserve_3 -- subsumption resolution 130,83
  have eq142 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq134 rule_def_0_0 -- resolution 134,67
  have eq143 : (old sk0 sk1 sk2) := resolve eq142 preserve_1 -- subsumption resolution 142,81
  have eq151 : memold sk0 := resolve eq143 old_mem1 -- resolution 143,77
  subsumption preserve_3 eq151 -- subsumption resolution 151,83

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq110 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq133 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq110 rule_def_1_0 -- resolution 110,71
  have eq135 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq133 preserve_4 -- subsumption resolution 133,84
  have eq151 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq135 rule_def_0_1 -- resolution 135,68
  have eq153 : (old sk0 sk1 sk2) := resolve eq151 preserve_2 -- subsumption resolution 151,82
  have eq161 : memold sk1 := resolve eq153 old_mem2 -- resolution 153,78
  subsumption preserve_3 eq161 -- subsumption resolution 161,83

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), a = Z ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq110 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 76,80
  have eq132 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk2 := resolve eq110 rule_def_1_1 -- resolution 110,72
  have eq135 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq132 preserve_1 -- subsumption resolution 132,81
  have eq148 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq135 rule_def_0_2 -- resolution 135,69
  have eq151 : (old sk0 sk1 sk2) := resolve eq148 preserve_4 -- subsumption resolution 148,84
  have eq160 : memold sk2 := resolve eq151 old_mem3 -- resolution 151,79
  subsumption preserve_3 eq160 -- subsumption resolution 160,83

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X3 X4 ∨ ¬ R X2 X0 X3 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1, ¬ R X0 X1 X0 ∨ ¬ R X1 X0 X0 ∨ R X0 X0 X1)
  rule_3 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ ¬ R X2 X0 X0 ∨ X2 = X0)
  rule_4 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X1 X3 X0 ∨ ¬ R X2 X1 X3 ∨ R X2 X3 X1)
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
  let sP1 (X Y Z) := ∃ sF0, c = Y ∧ a = Z ∧ ps.R X a sF0 ∧ ps.R sF0 X b
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 bc p3 p4XY p4XZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 ps.rule_1 ps.rule_4 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4YZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p4XY p4XZ p4YZ ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 new_imp
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ ps.rule_4 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_0 rule_def_1_2 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_1 rule_def_1_0 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sF0 sP1 (· ∈ ps.finsupp) rule_def_0_2 rule_def_1_1 new_imp ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X3 X4 ∨ ¬ ps.compl X2 X0 X3 ∨ ps.compl X0 X4 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X3) (max (Nat.pair X2 X0) (max (Nat.pair X0 X4) 0)))
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

theorem PartialSolution.toMagma_equation677 :
    letI := ps.toMagma
    Equation677 ℕ := by
  simp only [Equation677, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun (ps.complFun X1 X0) X1) (ps.complFun X0 (ps.complFun (ps.complFun X1 X0) X1))


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter255 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 2), (2, 1, 2)} : Finset _)
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
theorem _root_.Equation677_not_implies_Equation255 : ∃ (G : Type) (_ : Magma G), Equation677 G ∧ ¬Equation255 G := by
  use ℕ, PartialSolution.counter255.toMagma, PartialSolution.counter255.toMagma_equation677
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter255.of_R 1 1 2] | rw [PartialSolution.counter255.of_R 2 1 2])
  all_goals simp [PartialSolution.counter255]

end Eq677