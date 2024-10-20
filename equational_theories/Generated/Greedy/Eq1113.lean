import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Pairing

namespace Eq1113

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_3 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X1 X4 X3 ∨ ¬ old X5 X1 X4 ∨ X5 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b X2 ∨ ¬ old b X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old b (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq72 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 59
  have eq73 (X2 X3 : G) : ¬(old b X3 a) ∨ (new b c X2) ∨ ¬(old X2 b X3) := resolve eq72 rfl -- equality resolution 72
  have eq78 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 62,49
  have eq82 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF0 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq73 rule_def_1_3 -- resolution 73,63
  have eq85 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 65,66
  have eq86 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 65,67
  have eq94 (X0 X1 X2 X3 X4 X5 : G) : ¬(old b (sF0 X2 X3 X1) X4) ∨ X0 = X1 ∨ ¬(old b X5 X4) ∨ ¬(old X0 b X5) ∨ ¬(sP1 X2 X3 X1) := resolve old_3 rule_def_1_2 -- resolution 53,62
  have eq97 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq85 rule_def_1_1 -- resolution 85,61
  have eq98 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 := resolve eq85 rule_def_1_0 -- resolution 85,60
  have eq99 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq97 rule_def_0_2 -- resolution 97,58
  have eq100 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq97 rule_def_0_1 -- resolution 97,57
  have eq102 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq86 rule_def_1_1 -- resolution 86,61
  have eq103 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk0 := resolve eq86 rule_def_1_0 -- resolution 86,60
  have eq107 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq99 old_0 -- resolution 99,50
  have eq114 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ c = sk1 := resolve eq100 old_0 -- resolution 100,50
  have eq126 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq98 rule_def_0_1 -- resolution 98,57
  have eq135 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq82 rule_def_1_2 -- resolution 82,62
  have eq136 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new b c X0) := resolve eq135 rfl -- duplicate literal removal 135
  have eq138 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (new b c sk3) := resolve eq136 eq86 -- resolution 136,86
  have eq144 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk0 := resolve eq126 old_0 -- resolution 126,50
  have eq146 (X0 X1 X2 X3 X4 : G) : X0 = X1 ∨ ¬(old b X2 a) ∨ ¬(old X0 b X2) ∨ ¬(sP1 X3 X4 X1) ∨ ¬(sP1 X3 X4 X1) := resolve eq94 rule_def_1_3 -- resolution 94,63
  have eq147 (X0 X1 X2 X3 X4 : G) : ¬(sP1 X3 X4 X1) ∨ ¬(old b X2 a) ∨ ¬(old X0 b X2) ∨ X0 = X1 := resolve eq146 rfl -- duplicate literal removal 146
  have eq153 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq102 rule_def_0_2 -- resolution 102,58
  have eq154 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq102 rule_def_0_1 -- resolution 102,57
  have eq155 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ a = sk0 := resolve eq102 rule_def_0_0 -- resolution 102,56
  have eq162 : (old sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 := resolve eq103 rule_def_0_1 -- resolution 103,57
  have eq169 (X0 X1 : G) : ¬(old b X0 a) ∨ ¬(old X1 b X0) ∨ sk2 = X1 ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq147 eq85 -- resolution 147,85
  have eq197 : (new b c sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk1 := resolve eq138 rule_def_0_1 -- resolution 138,57
  have eq202 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF0 X1 X2 X3)) ∨ sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ ¬(sP1 X1 X2 X3) := resolve eq169 rule_def_1_3 -- resolution 169,63
  have eq215 : (old sk0 sk1 sk3) ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old b c sk3) ∨ (sP1 b c sk3) := resolve eq197 new_imp -- resolution 197,65
  have eq216 : (sP1 b c sk3) ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old sk0 sk1 sk3) := resolve eq215 p4XZ -- subsumption resolution 215,48
  have eq256 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq107 eq155 -- resolution 107,155
  have eq261 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ a = sk0 := resolve eq256 rfl -- duplicate literal removal 256
  have eq269 : c = sk2 ∨ c = sk1 ∨ a = sk0 := resolve eq261 preserve_2 -- subsumption resolution 261,68
  have eq273 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := Or.assoc3 (eq269.imp_left (fun h : c = sk2 ↦ superpose h eq85)) -- superposition 85,269, 269 into 85, unify on (0).2 in 269 and (0).3 in 85
  have eq291 : (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq273 eq78 -- subsumption resolution 273,78
  have eq292 : (sP0 sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq291 p4XY -- subsumption resolution 291,47
  have eq293 : c = sk1 ∨ a = sk0 := resolve eq292 rule_def_0_0 -- subsumption resolution 292,56
  have eq309 : (sP1 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ a = sk0 := Or.assoc3 (eq293.imp_left (fun h : c = sk1 ↦ superpose h eq86)) -- superposition 86,293, 293 into 86, unify on (0).2 in 293 and (0).2 in 86
  have eq324 : (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ a = sk0 := resolve eq309 p4XZ -- subsumption resolution 309,48
  have eq325 : (sP1 sk0 c sk3) ∨ a = sk0 := resolve eq324 rule_def_0_0 -- subsumption resolution 324,56
  have eq342 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq114 eq154 -- resolution 114,154
  have eq345 : b = sk1 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq342 rfl -- duplicate literal removal 342
  have eq353 : b = sk1 ∨ c = sk1 := resolve eq345 preserve_2 -- subsumption resolution 345,68
  have eq360 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq353.imp_left (fun h : b = sk1 ↦ superpose h eq99)) -- superposition 99,353, 353 into 99, unify on (0).2 in 353 and (0).2 in 99
  have eq370 : (old sk0 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq353.imp_left (fun h : b = sk1 ↦ superpose h eq153)) -- superposition 153,353, 353 into 153, unify on (0).2 in 353 and (0).2 in 153
  have eq377 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq360 bc -- subsumption resolution 360,45
  have eq381 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq370 bc -- subsumption resolution 370,45
  have eq498 : b = sk1 ∨ sk2 = sk3 ∨ b = sk0 ∨ b = sk0 ∨ b = sk1 := resolve eq144 eq162 -- resolution 144,162
  have eq506 : b = sk1 ∨ sk2 = sk3 ∨ b = sk0 := resolve eq498 rfl -- duplicate literal removal 498
  have eq512 : b = sk1 ∨ b = sk0 := resolve eq506 preserve_2 -- subsumption resolution 506,68
  have eq1445 (X0 X1 X2 : G) : sk2 = X0 ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq202 rule_def_1_2 -- resolution 202,62
  have eq1446 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ sk2 = X0 := resolve eq1445 rfl -- duplicate literal removal 1445
  have eq1544 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ sk2 = sk3 ∨ a = sk0 := resolve eq1446 eq325 -- resolution 1446,325
  have eq1550 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ sk2 = sk3 ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old sk0 sk1 sk3) := resolve eq1446 eq216 -- resolution 1446,216
  have eq1558 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = sk0 := resolve eq1544 preserve_2 -- subsumption resolution 1544,68
  have eq1559 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq1558 rule_def_0_0 -- subsumption resolution 1558,56
  have eq1560 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old sk0 sk1 sk3) := resolve eq1550 preserve_2 -- subsumption resolution 1550,68
  have eq1561 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old sk0 sk1 sk3) := resolve eq1560 rule_def_0_1 -- subsumption resolution 1560,57
  have eq1590 : (old sk0 c sk2) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq293.imp_left (fun h : c = sk1 ↦ superpose h eq1559)) -- superposition 1559,293, 293 into 1559, unify on (0).2 in 293 and (0).2 in 1559
  have eq1598 : (old sk0 c sk2) ∨ a = sk0 := resolve eq1590 rfl -- duplicate literal removal 1590
  have eq1606 : a = sk0 := resolve eq1598 p4XZ -- subsumption resolution 1598,48
  have eq1709 : (old a b sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq1606, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq377 -- backward demodulation 377,1606
  have eq1713 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq1606, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq381 -- backward demodulation 381,1606
  have eq1716 : b = sk1 ∨ a = b := Eq.mp (by simp only [eq1606, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq512 -- backward demodulation 512,1606
  have eq1767 : (old a sk1 sk2) ∨ b = sk1 ∨ (sP0 b c sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq1606, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1561 -- backward demodulation 1561,1606
  have eq1827 : c = sk2 ∨ c = sk1 := resolve eq1709 p3 -- subsumption resolution 1709,46
  have eq1830 : c = sk3 ∨ c = sk1 := resolve eq1713 p3 -- subsumption resolution 1713,46
  have eq1850 : (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ b = sk1 ∨ (sP0 b c sk3) := Eq.mp (by simp only [eq1606, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1767 -- forward demodulation 1767,1606
  have eq1883 : c ≠ sk2 ∨ c = sk1 := eq1830.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 68,1830, 1830 into 68, unify on (0).2 in 1830 and (0).2 in 68
  have eq1886 : c = sk1 := resolve eq1883 eq1827 -- subsumption resolution 1883,1827
  have eq1904 : c = b ∨ a = b := Eq.mp (by simp only [eq1886, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1716 -- backward demodulation 1716,1886
  have eq1954 : c = b ∨ (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ (sP0 b c sk3) := Eq.mp (by simp only [eq1886, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1850 -- backward demodulation 1850,1886
  have eq1978 : a = b := resolve eq1904 bc -- subsumption resolution 1904,45
  have eq1981 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq1978, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 57,1978
  have eq2146 : a = c ∨ (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ (sP0 b c sk3) := Eq.mp (by simp only [eq1978, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1954 -- forward demodulation 1954,1978
  have eq2147 : (old a sk1 sk3) ∨ (old a sk1 sk2) ∨ (sP0 b c sk3) := resolve eq2146 ac -- subsumption resolution 2146,44
  have eq2148 : (old a c sk3) ∨ (old a sk1 sk2) ∨ (sP0 b c sk3) := Eq.mp (by simp only [eq1886, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2147 -- forward demodulation 2147,1886
  have eq2149 : (old a sk1 sk2) ∨ (sP0 b c sk3) := resolve eq2148 p4XZ -- subsumption resolution 2148,48
  have eq2150 : (old a c sk2) ∨ (sP0 b c sk3) := Eq.mp (by simp only [eq1886, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2149 -- forward demodulation 2149,1886
  have eq2151 : (sP0 b c sk3) := resolve eq2150 p4XZ -- subsumption resolution 2150,48
  have eq2152 : (sP0 a c sk3) := Eq.mp (by simp only [eq1978, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2151 -- forward demodulation 2151,1978
  have eq2163 : a = c := resolve eq2152 eq1981 -- resolution 2152,1981
  subsumption ac eq2163 -- subsumption resolution 2163,44

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3 X4, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X3 X1 X4 ∨ old X1 X4 X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b X2 ∨ ¬ old b X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old b (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X1 X4 ∨ new X1 X4 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq77 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 62
  have eq78 (X2 X3 : G) : ¬(old b X3 a) ∨ (new b c X2) ∨ ¬(old X2 b X3) := resolve eq77 rfl -- equality resolution 77
  have eq82 (X0 X1 X2 : G) : (new X2 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_2 imp_new_0 -- resolution 65,57
  have eq86 (X0 X1 X2 : G) : (new b (sF0 X0 X1 X2) a) ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_3 imp_new_0 -- resolution 66,57
  have eq90 (X0 : G) : ¬(new sk3 sk1 X0) ∨ sk4 = X0 := resolve prev_0 preserve_2 -- resolution 69,72
  have eq98 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 68,70
  have eq99 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) := resolve new_imp preserve_1 -- resolution 68,71
  have eq100 : (sP1 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ (sP0 sk3 sk1 sk4) := resolve new_imp preserve_2 -- resolution 68,72
  have eq114 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq98 rule_def_1_1 -- resolution 98,64
  have eq116 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq114 rule_def_0_2 -- resolution 114,61
  have eq117 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq114 rule_def_0_1 -- resolution 114,60
  have eq118 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq114 rule_def_0_0 -- resolution 114,59
  have eq119 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq99 rule_def_1_1 -- resolution 99,64
  have eq120 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk1 := resolve eq99 rule_def_1_0 -- resolution 99,63
  have eq126 : (sP0 sk3 sk1 sk4) ∨ (old sk3 sk1 sk4) ∨ c = sk1 := resolve eq100 rule_def_1_1 -- resolution 100,64
  have eq175 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq119 rule_def_0_2 -- resolution 119,61
  have eq177 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk1 := resolve eq119 rule_def_0_0 -- resolution 119,59
  have eq188 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ c = sk3 := resolve eq120 rule_def_0_2 -- resolution 120,61
  have eq189 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ b = sk2 := resolve eq120 rule_def_0_1 -- resolution 120,60
  have eq190 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ a = sk1 := resolve eq120 rule_def_0_0 -- resolution 120,59
  have eq196 : (old sk3 sk1 sk4) ∨ c = sk1 ∨ c = sk4 := resolve eq126 rule_def_0_2 -- resolution 126,61
  have eq197 : (old sk3 sk1 sk4) ∨ c = sk1 ∨ b = sk1 := resolve eq126 rule_def_0_1 -- resolution 126,60
  have eq198 : (old sk3 sk1 sk4) ∨ c = sk1 ∨ a = sk3 := resolve eq126 rule_def_0_0 -- resolution 126,59
  have eq223 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ c = sk4 ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ ¬(old X0 sk1 X1) := resolve eq196 old_1 -- resolution 196,54
  have eq231 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ b = sk1 ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ ¬(old X0 sk1 X1) := resolve eq197 old_1 -- resolution 197,54
  have eq855 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 := resolve eq223 eq175 -- resolution 223,175
  have eq868 (X0 : G) : b = sk1 ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ c = sk3 := resolve eq231 eq188 -- resolution 231,188
  have eq872 (X0 : G) : ¬(old X0 sk1 sk2) ∨ (old sk1 sk4 X0) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 := resolve eq868 rfl -- duplicate literal removal 868
  have eq1022 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq872 eq117 -- resolution 872,117
  have eq1030 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 := resolve eq1022 rfl -- duplicate literal removal 1022
  have eq1049 : c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ (new sk1 sk4 sk0) := resolve eq1030 imp_new_0 -- resolution 1030,57
  have eq1054 : c = sk3 ∨ b = sk1 ∨ c = sk1 := resolve eq1049 preserve_3 -- subsumption resolution 1049,73
  have eq1069 : (sP1 c sk1 sk4) ∨ (old c sk1 sk4) ∨ (sP0 c sk1 sk4) ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq1054.imp_left (fun h : c = sk3 ↦ superpose h eq100)) -- superposition 100,1054, 1054 into 100, unify on (0).2 in 1054 and (0).1 in 100
  have eq1133 : (sP1 c sk1 sk4) ∨ (sP0 c sk1 sk4) ∨ b = sk1 ∨ c = sk1 := resolve eq1069 p4YZ -- subsumption resolution 1069,52
  have eq1134 : (sP0 c sk1 sk4) ∨ b = sk1 ∨ c = sk1 := resolve eq1133 rule_def_1_1 -- subsumption resolution 1133,64
  have eq1135 : b = sk1 ∨ c = sk1 := resolve eq1134 rule_def_0_1 -- subsumption resolution 1134,60
  have eq1149 : ¬(new b sk4 sk0) ∨ c = sk1 := eq1135.imp_left (fun h : b = sk1 ↦ superpose h preserve_3) -- superposition 73,1135, 1135 into 73, unify on (0).2 in 1135 and (0).1 in 73
  have eq1152 (X0 : G) : ¬(new sk3 b X0) ∨ sk4 = X0 ∨ c = sk1 := Or.assoc2 (eq1135.imp_left (fun h : b = sk1 ↦ superpose h eq90)) -- superposition 90,1135, 1135 into 90, unify on (0).2 in 1135 and (0).2 in 90
  have eq1158 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq1135.imp_left (fun h : b = sk1 ↦ superpose h eq116)) -- superposition 116,1135, 1135 into 116, unify on (0).2 in 1135 and (0).2 in 116
  have eq1183 : (old b sk2 sk3) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq1135.imp_left (fun h : b = sk1 ↦ superpose h eq175)) -- superposition 175,1135, 1135 into 175, unify on (0).2 in 1135 and (0).1 in 175
  have eq1192 : (old sk3 b sk4) ∨ c = b ∨ c = sk4 ∨ c = sk1 := Or.assoc3 (eq1135.imp_left (fun h : b = sk1 ↦ superpose h eq196)) -- superposition 196,1135, 1135 into 196, unify on (0).2 in 1135 and (0).2 in 196
  have eq1213 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq1158 bc -- subsumption resolution 1158,48
  have eq1224 : (old sk3 b sk4) ∨ c = sk4 ∨ c = sk1 := resolve eq1192 bc -- subsumption resolution 1192,48
  have eq1281 (X0 X1 : G) : ¬(sP1 X0 X1 sk3) ∨ c = sk1 ∨ sk4 = (sF0 X0 X1 sk3) := resolve eq1152 eq82 -- resolution 1152,82
  have eq1589 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq855 eq116 -- resolution 855,116
  have eq1601 : (old sk1 sk4 sk0) ∨ c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 := resolve eq1589 rfl -- duplicate literal removal 1589
  have eq2759 : c = sk1 ∨ c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk4 sk0) := resolve eq1601 imp_new_0 -- resolution 1601,57
  have eq2769 : c = sk4 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq2759 preserve_3 -- subsumption resolution 2759,73
  have eq2779 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := Or.assoc3 (eq2769.imp_left (fun h : c = sk4 ↦ superpose h eq198)) -- superposition 198,2769, 2769 into 198, unify on (0).2 in 2769 and (0).3 in 198
  have eq2827 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 ∨ c = sk2 ∨ c = sk3 := resolve eq2779 rfl -- duplicate literal removal 2779
  have eq2832 : c = sk3 ∨ a = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq2827 p4XY -- subsumption resolution 2827,50
  have eq3272 : (old c sk1 sk4) ∨ c = sk1 ∨ a = c ∨ a = sk3 ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq2832.imp_left (fun h : c = sk3 ↦ superpose h eq198)) -- superposition 198,2832, 2832 into 198, unify on (0).2 in 2832 and (0).1 in 198
  have eq3363 : (old c sk1 sk4) ∨ c = sk1 ∨ a = c ∨ a = sk3 ∨ c = sk2 := resolve eq3272 rfl -- duplicate literal removal 3272
  have eq3379 : c = sk1 ∨ a = c ∨ a = sk3 ∨ c = sk2 := resolve eq3363 p4YZ -- subsumption resolution 3363,52
  have eq3380 : a = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq3379 ac -- subsumption resolution 3379,47
  have eq3461 : (old b sk2 a) ∨ c = sk2 ∨ a = c ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc4 (eq3380.imp_left (fun h : a = sk3 ↦ superpose h eq1183)) -- superposition 1183,3380, 3380 into 1183, unify on (0).2 in 3380 and (0).3 in 1183
  have eq3465 : (old a b sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc3 (eq3380.imp_left (fun h : a = sk3 ↦ superpose h eq1224)) -- superposition 1224,3380, 3380 into 1224, unify on (0).2 in 3380 and (0).1 in 1224
  have eq3483 : (old a b sk4) ∨ c = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq3465 rfl -- duplicate literal removal 3465
  have eq3487 : (old b sk2 a) ∨ c = sk2 ∨ a = c ∨ c = sk1 := resolve eq3461 rfl -- duplicate literal removal 3461
  have eq3532 : (old b sk2 a) ∨ c = sk2 ∨ c = sk1 := resolve eq3487 ac -- subsumption resolution 3487,47
  have eq3534 : c = sk4 ∨ c = sk1 ∨ c = sk2 := resolve eq3483 p3 -- subsumption resolution 3483,49
  have eq3567 : ¬(new b c sk0) ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := Or.assoc2 (eq3534.imp_left (fun h : c = sk4 ↦ superpose h eq1149)) -- superposition 1149,3534, 3534 into 1149, unify on (0).2 in 3534 and (0).2 in 1149
  have eq3587 : ¬(new b c sk0) ∨ c = sk1 ∨ c = sk2 := resolve eq3567 rfl -- duplicate literal removal 3567
  have eq3762 (X0 : G) : ¬(old X0 b sk2) ∨ c = sk1 ∨ (new b c X0) ∨ c = sk2 := resolve eq3532 eq78 -- resolution 3532,78
  have eq5827 : c = sk1 ∨ (new b c sk0) ∨ c = sk2 ∨ c = sk2 ∨ c = sk1 := resolve eq3762 eq1213 -- resolution 3762,1213
  have eq5828 : c = sk1 ∨ (new b c sk0) ∨ c = sk2 := resolve eq5827 rfl -- duplicate literal removal 5827
  have eq5831 : c = sk2 ∨ c = sk1 := resolve eq5828 eq3587 -- subsumption resolution 5828,3587
  have eq5857 : (sP1 sk1 c sk3) ∨ (old sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ c = sk1 := Or.assoc3 (eq5831.imp_left (fun h : c = sk2 ↦ superpose h eq99)) -- superposition 99,5831, 5831 into 99, unify on (0).2 in 5831 and (0).2 in 99
  have eq5861 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 := Or.assoc3 (eq5831.imp_left (fun h : c = sk2 ↦ superpose h eq118)) -- superposition 118,5831, 5831 into 118, unify on (0).2 in 5831 and (0).3 in 118
  have eq5970 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq5861 rfl -- duplicate literal removal 5861
  have eq5975 : (sP1 sk1 c sk3) ∨ (sP0 sk1 c sk3) ∨ c = sk1 := resolve eq5857 p4XZ -- subsumption resolution 5857,51
  have eq5976 : c = sk1 ∨ a = sk0 := resolve eq5970 p4XY -- subsumption resolution 5970,50
  have eq6025 : (old c sk2 sk3) ∨ c = b ∨ a = c ∨ a = sk0 := Or.assoc3 (eq5976.imp_left (fun h : c = sk1 ↦ superpose h eq190)) -- superposition 190,5976, 5976 into 190, unify on (0).2 in 5976 and (0).1 in 190
  have eq6156 : c = b ∨ a = c ∨ a = sk0 := resolve eq6025 p4YZ -- subsumption resolution 6025,52
  have eq6157 : a = c ∨ a = sk0 := resolve eq6156 bc -- subsumption resolution 6156,48
  have eq6158 : a = sk0 := resolve eq6157 ac -- subsumption resolution 6157,47
  have eq6261 : ¬(new b sk4 a) ∨ c = sk1 := Eq.mp (by simp only [eq6158, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1149 -- backward demodulation 1149,6158
  have eq6977 : (sP0 sk1 c sk3) ∨ c = sk1 ∨ c = sk1 ∨ sk4 = (sF0 sk1 c sk3) := resolve eq5975 eq1281 -- resolution 5975,1281
  have eq6999 : (sP0 sk1 c sk3) ∨ c = sk1 ∨ sk4 = (sF0 sk1 c sk3) := resolve eq6977 rfl -- duplicate literal removal 6977
  have eq7886 : c = sk1 ∨ sk4 = (sF0 sk1 c sk3) ∨ c = b := resolve eq6999 rule_def_0_1 -- resolution 6999,60
  have eq7902 : sk4 = (sF0 sk1 c sk3) ∨ c = sk1 := resolve eq7886 bc -- subsumption resolution 7886,48
  have eq7939 : (new b sk4 a) ∨ ¬(sP1 sk1 c sk3) ∨ c = sk1 := Or.assoc2 (eq7902.imp_left (fun h : sk4 = (sF0 sk1 c sk3) ↦ superpose h eq86)) -- superposition 86,7902, 7902 into 86, unify on (0).2 in 7902 and (0).2 in 86
  have eq7954 : ¬(sP1 sk1 c sk3) ∨ c = sk1 := resolve eq7939 eq6261 -- subsumption resolution 7939,6261
  have eq7998 : c = sk1 ∨ (sP0 sk1 c sk3) ∨ c = sk1 := resolve eq7954 eq5975 -- resolution 7954,5975
  have eq8013 : (sP0 sk1 c sk3) ∨ c = sk1 := resolve eq7998 rfl -- duplicate literal removal 7998
  have eq8064 : c = sk1 ∨ c = b := resolve eq8013 rule_def_0_1 -- resolution 8013,60
  have eq8080 : c = sk1 := resolve eq8064 bc -- subsumption resolution 8064,48
  have eq8099 : (old c sk2 sk3) ∨ c = sk2 ∨ a = sk1 := Eq.mp (by simp only [eq8080, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq177 -- backward demodulation 177,8080
  have eq8109 : (old c sk2 sk3) ∨ b = sk1 ∨ b = sk2 := Eq.mp (by simp only [eq8080, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq189 -- backward demodulation 189,8080
  have eq8523 : c = sk2 ∨ a = sk1 := resolve eq8099 p4YZ -- subsumption resolution 8099,52
  have eq8524 : a = c ∨ c = sk2 := Eq.mp (by simp only [eq8080, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8523 -- forward demodulation 8523,8080
  have eq8525 : c = sk2 := resolve eq8524 ac -- subsumption resolution 8524,47
  have eq8550 : b = sk1 ∨ b = sk2 := resolve eq8109 p4YZ -- subsumption resolution 8109,52
  have eq8551 : c = b ∨ b = sk2 := Eq.mp (by simp only [eq8080, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8550 -- forward demodulation 8550,8080
  have eq8552 : b = sk2 := resolve eq8551 bc -- subsumption resolution 8551,48
  have eq8553 : c = b := Eq.mp (by simp only [eq8525, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8552 -- forward demodulation 8552,8525
  subsumption bc eq8553 -- subsumption resolution 8553,48

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (old_2 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X0 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X0 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq96 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 69,72
  have eq97 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 69,73
  have eq117 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq96 rule_def_1_1 -- resolution 96,65
  have eq118 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 := resolve eq96 rule_def_1_0 -- resolution 96,64
  have eq119 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk1 := resolve eq97 rule_def_1_1 -- resolution 97,65
  have eq120 : (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ b = sk3 := resolve eq97 rule_def_1_0 -- resolution 97,64
  have eq121 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq117 rule_def_0_2 -- resolution 117,62
  have eq123 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq117 rule_def_0_0 -- resolution 117,60
  have eq126 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 := resolve eq121 old_2 -- resolution 121,56
  have eq143 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq118 rule_def_0_1 -- resolution 118,61
  have eq172 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq119 rule_def_0_2 -- resolution 119,62
  have eq174 : (old sk3 sk1 sk2) ∨ c = sk1 ∨ a = sk3 := resolve eq119 rule_def_0_0 -- resolution 119,60
  have eq193 : (old sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 := resolve eq120 rule_def_0_1 -- resolution 120,61
  have eq284 : c = sk2 ∨ sk0 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq126 eq172 -- resolution 126,172
  have eq285 : c = sk2 ∨ sk0 = sk3 ∨ c = sk1 := resolve eq284 rfl -- duplicate literal removal 284
  have eq298 : c = sk2 ∨ c = sk1 := resolve eq285 preserve_2 -- subsumption resolution 285,74
  have eq309 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 := Or.assoc3 (eq298.imp_left (fun h : c = sk2 ↦ superpose h eq123)) -- superposition 123,298, 298 into 123, unify on (0).2 in 298 and (0).3 in 123
  have eq319 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 ∨ c = sk1 := Or.assoc3 (eq298.imp_left (fun h : c = sk2 ↦ superpose h eq174)) -- superposition 174,298, 298 into 174, unify on (0).2 in 298 and (0).3 in 174
  have eq328 : (old sk3 sk1 c) ∨ c = sk1 ∨ a = sk3 := resolve eq319 rfl -- duplicate literal removal 319
  have eq330 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 := resolve eq309 rfl -- duplicate literal removal 309
  have eq339 : c = sk1 ∨ a = sk0 := resolve eq330 p4XY -- subsumption resolution 330,51
  have eq340 : a = sk3 ∨ c = sk1 := resolve eq328 p4XY -- subsumption resolution 328,51
  have eq401 : (old sk3 c sk2) ∨ b = sk3 ∨ c = b ∨ a = sk0 := Or.assoc3 (eq339.imp_left (fun h : c = sk1 ↦ superpose h eq193)) -- superposition 193,339, 339 into 193, unify on (0).2 in 339 and (0).2 in 193
  have eq413 : b = sk3 ∨ c = b ∨ a = sk0 := resolve eq401 p4XZ -- subsumption resolution 401,52
  have eq414 : b = sk3 ∨ a = sk0 := resolve eq413 bc -- subsumption resolution 413,49
  have eq431 : a ≠ sk0 ∨ c = sk1 := eq340.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 74,340, 340 into 74, unify on (0).2 in 340 and (0).2 in 74
  have eq445 : c = sk1 := resolve eq431 eq339 -- subsumption resolution 431,339
  have eq457 : (sP0 sk3 c sk2) ∨ (old sk3 sk1 sk2) ∨ b = sk3 := Eq.mp (by simp only [eq445, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120 -- backward demodulation 120,445
  have eq462 : (old sk0 c sk2) ∨ b = sk0 ∨ b = sk1 := Eq.mp (by simp only [eq445, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq143 -- backward demodulation 143,445
  have eq566 : (old sk3 c sk2) ∨ (sP0 sk3 c sk2) ∨ b = sk3 := Eq.mp (by simp only [eq445, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq457 -- forward demodulation 457,445
  have eq567 : (sP0 sk3 c sk2) ∨ b = sk3 := resolve eq566 p4XZ -- subsumption resolution 566,52
  have eq569 : b = sk0 ∨ b = sk1 := resolve eq462 p4XZ -- subsumption resolution 462,52
  have eq570 : c = b ∨ b = sk0 := Eq.mp (by simp only [eq445, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq569 -- forward demodulation 569,445
  have eq571 : b = sk0 := resolve eq570 bc -- subsumption resolution 570,49
  have eq572 : b ≠ sk3 := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 74,571
  have eq585 : a = b ∨ b = sk3 := Eq.mp (by simp only [eq571, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq414 -- backward demodulation 414,571
  have eq595 : a = b := resolve eq585 eq572 -- subsumption resolution 585,572
  have eq626 : a = sk3 ∨ (sP0 sk3 c sk2) := Eq.mp (by simp only [eq595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq567 -- backward demodulation 567,595
  have eq628 : a ≠ sk3 := Eq.mp (by simp only [eq595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq572 -- backward demodulation 572,595
  have eq646 : a = sk3 := resolve eq626 rule_def_0_0 -- subsumption resolution 626,60
  subsumption eq646 eq628 -- subsumption resolution 628,646

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_1 : (∀ X0 X1 X2 X3 X4, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X3 X1 X4 ∨ new X1 X4 X0)) (prev_2 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X0 = X3)) (old_3 : (∀ X0 X1 X2 X3 X4 X5, ¬ old X0 X1 X2 ∨ ¬ old X1 X2 X3 ∨ ¬ old X1 X4 X3 ∨ ¬ old X5 X1 X4 ∨ X5 = X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z X2, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b X2 ∨ ¬ old b X2 a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (rule_def_1_3 : ∀ (X Y Z : G), old b (sF0 X Y Z) a ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3 X4 X5, ¬ new X0 X1 X2 ∨ ¬ new X1 X2 X3 ∨ ¬ new X1 X4 X3 ∨ ¬ new X5 X1 X4 ∨ X5 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq82 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 63
  have eq83 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq82 rfl -- equality resolution 82
  have eq84 : (new a b c) := resolve eq83 rfl -- equality resolution 83
  have eq85 (X0 X2 X3 : G) : (new X0 c X2) ∨ ¬(old b X3 a) ∨ ¬(old X2 b X3) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 67
  have eq86 (X2 X3 : G) : ¬(old b X3 a) ∨ (new b c X2) ∨ ¬(old X2 b X3) := resolve eq85 rfl -- equality resolution 85
  have eq87 (X0 X1 : G) : ¬(sP1 X0 X1 a) := resolve rule_def_1_2 p3 -- resolution 70,54
  have eq90 (X0 X1 X2 : G) : (new X2 b (sF0 X0 X1 X2)) ∨ ¬(sP1 X0 X1 X2) := resolve rule_def_1_2 imp_new_0 -- resolution 70,62
  have eq91 (X0 X1 : G) : ¬(sP1 X0 X1 c) := resolve rule_def_1_2 p4YZ -- resolution 70,57
  have eq99 (X0 : G) : ¬(new sk5 sk1 X0) ∨ sk4 = X0 := resolve prev_0 preserve_3 -- resolution 74,80
  have eq100 (X0 : G) : ¬(new X0 b c) ∨ a = X0 := resolve prev_2 eq84 -- resolution 76,84
  have eq101 (X0 : G) : ¬(new X0 sk1 sk2) ∨ sk0 = X0 := resolve prev_2 preserve_0 -- resolution 76,77
  have eq106 (X0 X1 X2 X3 : G) : ¬(old X0 b (sF0 X1 X2 X3)) ∨ (new b c X0) ∨ ¬(sP1 X1 X2 X3) := resolve eq86 rule_def_1_3 -- resolution 86,71
  have eq112 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq113 : (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) := resolve new_imp preserve_1 -- resolution 73,78
  have eq114 : (sP1 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ (sP0 sk1 sk4 sk3) := resolve new_imp preserve_2 -- resolution 73,79
  have eq115 : (sP1 sk5 sk1 sk4) ∨ (old sk5 sk1 sk4) ∨ (sP0 sk5 sk1 sk4) := resolve new_imp preserve_3 -- resolution 73,80
  have eq135 (X0 X1 X2 X3 X4 : G) : ¬(sP1 X0 X1 X2) ∨ (new b (sF0 X0 X1 X2) X3) ∨ ¬(new b X4 X2) ∨ ¬(new X3 b X4) := resolve eq90 prev_1 -- resolution 90,75
  have eq144 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq112 rule_def_1_1 -- resolution 112,69
  have eq146 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk2 := resolve eq113 rule_def_1_1 -- resolution 113,69
  have eq147 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ b = sk1 := resolve eq113 rule_def_1_0 -- resolution 113,68
  have eq148 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq144 rule_def_0_2 -- resolution 144,66
  have eq149 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq144 rule_def_0_1 -- resolution 144,65
  have eq150 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ a = sk0 := resolve eq144 rule_def_0_0 -- resolution 144,64
  have eq151 : (sP0 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ c = sk4 := resolve eq114 rule_def_1_1 -- resolution 114,69
  have eq152 : (sP0 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ b = sk1 := resolve eq114 rule_def_1_0 -- resolution 114,68
  have eq153 (X0 X1 X2 : G) : ¬(old sk1 sk2 X1) ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk1 ∨ ¬(old sk1 X2 X1) ∨ ¬(old X0 sk1 X2) := resolve eq148 old_3 -- resolution 148,61
  have eq158 : (sP0 sk5 sk1 sk4) ∨ (old sk5 sk1 sk4) ∨ c = sk1 := resolve eq115 rule_def_1_1 -- resolution 115,69
  have eq160 (X0 X1 X2 : G) : ¬(old sk1 sk2 X1) ∨ b = sk1 ∨ sk0 = X0 ∨ c = sk1 ∨ ¬(old sk1 X2 X1) ∨ ¬(old X0 sk1 X2) := resolve eq149 old_3 -- resolution 149,61
  have eq191 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ c = sk3 := resolve eq146 rule_def_0_2 -- resolution 146,66
  have eq192 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ b = sk2 := resolve eq146 rule_def_0_1 -- resolution 146,65
  have eq193 : (old sk1 sk2 sk3) ∨ c = sk2 ∨ a = sk1 := resolve eq146 rule_def_0_0 -- resolution 146,64
  have eq217 (X0 X1 X2 : G) : (new b c X0) ∨ ¬(sP1 X1 X2 X0) ∨ ¬(sP1 X1 X2 X0) := resolve eq106 rule_def_1_2 -- resolution 106,70
  have eq218 (X0 X1 X2 : G) : ¬(sP1 X1 X2 X0) ∨ (new b c X0) := resolve eq217 rfl -- duplicate literal removal 217
  have eq220 : (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ (new b c sk3) := resolve eq218 eq113 -- resolution 218,113
  have eq221 : (sP0 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ (new b c sk3) := resolve eq218 eq114 -- resolution 218,114
  have eq227 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ c = sk3 := resolve eq147 rule_def_0_2 -- resolution 147,66
  have eq228 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ b = sk2 := resolve eq147 rule_def_0_1 -- resolution 147,65
  have eq229 : (old sk1 sk2 sk3) ∨ b = sk1 ∨ a = sk1 := resolve eq147 rule_def_0_0 -- resolution 147,64
  have eq247 : (old sk1 sk4 sk3) ∨ c = sk4 ∨ c = sk3 := resolve eq151 rule_def_0_2 -- resolution 151,66
  have eq249 : (old sk1 sk4 sk3) ∨ c = sk4 ∨ a = sk1 := resolve eq151 rule_def_0_0 -- resolution 151,64
  have eq255 : (old sk1 sk4 sk3) ∨ b = sk1 ∨ c = sk3 := resolve eq152 rule_def_0_2 -- resolution 152,66
  have eq256 : (old sk1 sk4 sk3) ∨ b = sk1 ∨ b = sk4 := resolve eq152 rule_def_0_1 -- resolution 152,65
  have eq263 : (old sk5 sk1 sk4) ∨ c = sk1 ∨ c = sk4 := resolve eq158 rule_def_0_2 -- resolution 158,66
  have eq264 : (old sk5 sk1 sk4) ∨ c = sk1 ∨ b = sk1 := resolve eq158 rule_def_0_1 -- resolution 158,65
  have eq265 : (old sk5 sk1 sk4) ∨ c = sk1 ∨ a = sk5 := resolve eq158 rule_def_0_0 -- resolution 158,64
  have eq349 (X0 X1 : G) : ¬(new b X1 sk3) ∨ (new b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b X1) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) := resolve eq135 eq113 -- resolution 135,113
  have eq350 (X0 X1 : G) : ¬(new b X1 sk3) ∨ (new b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b X1) ∨ (old sk1 sk4 sk3) ∨ (sP0 sk1 sk4 sk3) := resolve eq135 eq114 -- resolution 135,114
  have eq370 : (new b c sk3) ∨ (old sk1 sk2 sk3) ∨ c = sk3 := resolve eq220 rule_def_0_2 -- resolution 220,66
  have eq372 : (new b c sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq220 rule_def_0_0 -- resolution 220,64
  have eq374 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ (sP0 b c sk3) ∨ (old b c sk3) ∨ (sP1 b c sk3) := resolve eq370 new_imp -- resolution 370,73
  have eq377 : (old sk1 sk2 sk3) ∨ c = sk3 ∨ (sP0 b c sk3) ∨ (sP1 b c sk3) := resolve eq374 p4XZ -- subsumption resolution 374,56
  have eq378 : (sP1 b c sk3) ∨ c = sk3 ∨ (old sk1 sk2 sk3) := resolve eq377 rule_def_0_2 -- subsumption resolution 377,66
  have eq384 : (new b c sk3) ∨ (old sk1 sk4 sk3) ∨ c = sk3 := resolve eq221 rule_def_0_2 -- resolution 221,66
  have eq386 : (new b c sk3) ∨ (old sk1 sk4 sk3) ∨ a = sk1 := resolve eq221 rule_def_0_0 -- resolution 221,64
  have eq396 : (old sk1 sk4 sk3) ∨ c = sk3 ∨ (sP0 b c sk3) ∨ (old b c sk3) ∨ (sP1 b c sk3) := resolve eq384 new_imp -- resolution 384,73
  have eq399 : (old sk1 sk4 sk3) ∨ c = sk3 ∨ (sP0 b c sk3) ∨ (sP1 b c sk3) := resolve eq396 p4XZ -- subsumption resolution 396,56
  have eq400 : (sP1 b c sk3) ∨ c = sk3 ∨ (old sk1 sk4 sk3) := resolve eq399 rule_def_0_2 -- subsumption resolution 399,66
  have eq437 (X0 X1 : G) : ¬(new b X1 sk3) ∨ (old sk1 sk2 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b X1) := resolve eq378 eq135 -- resolution 378,135
  have eq446 (X0 X1 : G) : ¬(new b X1 sk3) ∨ (old sk1 sk4 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b X1) := resolve eq400 eq135 -- resolution 400,135
  have eq546 (X0 : G) : (new b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq349 eq372 -- resolution 349,372
  have eq551 (X0 : G) : (new b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) ∨ a = sk1 := resolve eq546 rfl -- duplicate literal removal 546
  have eq554 (X0 : G) : (new b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq551 rule_def_0_0 -- subsumption resolution 551,64
  have eq567 (X0 : G) : (new b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk4 sk3) ∨ (sP0 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ a = sk1 := resolve eq350 eq386 -- resolution 350,386
  have eq575 (X0 : G) : (new b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk4 sk3) ∨ (sP0 sk1 sk4 sk3) ∨ a = sk1 := resolve eq567 rfl -- duplicate literal removal 567
  have eq576 (X0 : G) : (new b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b c) ∨ (old sk1 sk4 sk3) ∨ a = sk1 := resolve eq575 rule_def_0_0 -- subsumption resolution 575,64
  have eq1291 (X0 X1 : G) : c = sk2 ∨ sk0 = X0 ∨ c = sk1 ∨ ¬(old sk1 X1 sk3) ∨ ¬(old X0 sk1 X1) ∨ c = sk2 ∨ a = sk1 := resolve eq153 eq193 -- resolution 153,193
  have eq1293 (X0 X1 : G) : c = sk2 ∨ sk0 = X0 ∨ c = sk1 ∨ ¬(old sk1 X1 sk3) ∨ ¬(old X0 sk1 X1) ∨ c = sk2 ∨ c = sk3 := resolve eq153 eq191 -- resolution 153,191
  have eq1294 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ sk0 = X0 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old X0 sk1 X1) ∨ c = sk3 := resolve eq1293 rfl -- duplicate literal removal 1293
  have eq1296 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ sk0 = X0 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old X0 sk1 X1) ∨ a = sk1 := resolve eq1291 rfl -- duplicate literal removal 1291
  have eq1320 (X0 X1 : G) : b = sk1 ∨ sk0 = X0 ∨ c = sk1 ∨ ¬(old sk1 X1 sk3) ∨ ¬(old X0 sk1 X1) ∨ b = sk1 ∨ c = sk3 := resolve eq160 eq227 -- resolution 160,227
  have eq1324 (X0 X1 : G) : ¬(old sk1 X1 sk3) ∨ sk0 = X0 ∨ c = sk1 ∨ b = sk1 ∨ ¬(old X0 sk1 X1) ∨ c = sk3 := resolve eq1320 rfl -- duplicate literal removal 1320
  have eq1915 (X0 : G) : (sP1 b (sF0 sk1 sk2 sk3) X0) ∨ (old sk1 sk2 sk3) ∨ a = sk1 ∨ (sP0 b (sF0 sk1 sk2 sk3) X0) ∨ (old b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b c) := resolve eq554 new_imp -- resolution 554,73
  have eq2040 (X0 : G) : (sP1 b (sF0 sk1 sk4 sk3) X0) ∨ (old sk1 sk4 sk3) ∨ a = sk1 ∨ (sP0 b (sF0 sk1 sk4 sk3) X0) ∨ (old b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b c) := resolve eq576 new_imp -- resolution 576,73
  have eq2513 (X0 : G) : sk0 = X0 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old X0 sk1 sk4) ∨ c = sk3 ∨ c = sk4 ∨ c = sk3 := resolve eq1294 eq247 -- resolution 1294,247
  have eq2532 (X0 : G) : ¬(old X0 sk1 sk4) ∨ c = sk1 ∨ c = sk2 ∨ sk0 = X0 ∨ c = sk3 ∨ c = sk4 := resolve eq2513 rfl -- duplicate literal removal 2513
  have eq2584 (X0 : G) : sk0 = X0 ∨ c = sk1 ∨ c = sk2 ∨ ¬(old X0 sk1 sk4) ∨ a = sk1 ∨ c = sk4 ∨ a = sk1 := resolve eq1296 eq249 -- resolution 1296,249
  have eq2600 (X0 : G) : ¬(old X0 sk1 sk4) ∨ c = sk1 ∨ c = sk2 ∨ sk0 = X0 ∨ a = sk1 ∨ c = sk4 := resolve eq2584 rfl -- duplicate literal removal 2584
  have eq2622 (X0 : G) : sk0 = X0 ∨ c = sk1 ∨ b = sk1 ∨ ¬(old X0 sk1 sk4) ∨ c = sk3 ∨ b = sk1 ∨ c = sk3 := resolve eq1324 eq255 -- resolution 1324,255
  have eq2637 (X0 : G) : ¬(old X0 sk1 sk4) ∨ c = sk1 ∨ b = sk1 ∨ sk0 = X0 ∨ c = sk3 := resolve eq2622 rfl -- duplicate literal removal 2622
  have eq2646 : c = sk1 ∨ b = sk1 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq2637 eq264 -- resolution 2637,264
  have eq2676 : c = sk1 ∨ b = sk1 ∨ sk0 = sk5 ∨ c = sk3 := resolve eq2646 rfl -- duplicate literal removal 2646
  have eq2679 : c = sk3 ∨ b = sk1 ∨ c = sk1 := resolve eq2676 preserve_4 -- subsumption resolution 2676,81
  have eq2733 : (old sk1 sk2 c) ∨ b = sk1 ∨ b = sk2 ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq2679.imp_left (fun h : c = sk3 ↦ superpose h eq228)) -- superposition 228,2679, 2679 into 228, unify on (0).2 in 2679 and (0).3 in 228
  have eq2734 : (old sk1 sk2 c) ∨ b = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq2679.imp_left (fun h : c = sk3 ↦ superpose h eq229)) -- superposition 229,2679, 2679 into 229, unify on (0).2 in 2679 and (0).3 in 229
  have eq2741 : (old sk1 sk4 c) ∨ b = sk1 ∨ b = sk4 ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq2679.imp_left (fun h : c = sk3 ↦ superpose h eq256)) -- superposition 256,2679, 2679 into 256, unify on (0).2 in 2679 and (0).3 in 256
  have eq2793 : (old sk1 sk4 c) ∨ b = sk1 ∨ b = sk4 ∨ c = sk1 := resolve eq2741 rfl -- duplicate literal removal 2741
  have eq2798 : (old sk1 sk2 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 := resolve eq2734 rfl -- duplicate literal removal 2734
  have eq2799 : (old sk1 sk2 c) ∨ b = sk1 ∨ b = sk2 ∨ c = sk1 := resolve eq2733 rfl -- duplicate literal removal 2733
  have eq2808 : b = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq2799 p4XY -- subsumption resolution 2799,55
  have eq2809 : b = sk1 ∨ a = sk1 ∨ c = sk1 := resolve eq2798 p4XY -- subsumption resolution 2798,55
  have eq2811 : b = sk4 ∨ b = sk1 ∨ c = sk1 := resolve eq2793 p4XY -- subsumption resolution 2793,55
  have eq2851 (X0 : G) : ¬(new X0 sk1 b) ∨ sk0 = X0 ∨ b = sk1 ∨ c = sk1 := Or.assoc2 (eq2808.imp_left (fun h : b = sk2 ↦ superpose h eq101)) -- superposition 101,2808, 2808 into 101, unify on (0).2 in 2808 and (0).3 in 101
  have eq2996 : (new b sk2 sk3) ∨ a = sk1 ∨ c = sk1 := eq2809.imp_left (fun h : b = sk1 ↦ superpose h preserve_1) -- superposition 78,2809, 2809 into 78, unify on (0).2 in 2809 and (0).1 in 78
  have eq2997 : (new b sk4 sk3) ∨ a = sk1 ∨ c = sk1 := eq2809.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 79,2809, 2809 into 79, unify on (0).2 in 2809 and (0).1 in 79
  have eq3184 : (new sk5 sk1 b) ∨ b = sk1 ∨ c = sk1 := eq2811.imp_left (fun h : b = sk4 ↦ superpose h preserve_3) -- superposition 80,2811, 2811 into 80, unify on (0).2 in 2811 and (0).3 in 80
  have eq3724 (X0 : G) : a = sk1 ∨ c = sk1 ∨ (new b (sF0 sk1 sk4 sk3) X0) ∨ ¬(new X0 b sk2) ∨ (old sk1 sk4 sk3) ∨ (sP0 sk1 sk4 sk3) := resolve eq2996 eq350 -- resolution 2996,350
  have eq3735 (X0 : G) : (new b (sF0 sk1 sk4 sk3) X0) ∨ c = sk1 ∨ a = sk1 ∨ ¬(new X0 b sk2) ∨ (old sk1 sk4 sk3) := resolve eq3724 rule_def_0_0 -- subsumption resolution 3724,64
  have eq3772 (X0 : G) : a = sk1 ∨ c = sk1 ∨ (new b (sF0 sk1 sk2 sk3) X0) ∨ ¬(new X0 b sk4) ∨ (old sk1 sk2 sk3) ∨ (sP0 sk1 sk2 sk3) := resolve eq2997 eq349 -- resolution 2997,349
  have eq3783 (X0 : G) : (new b (sF0 sk1 sk2 sk3) X0) ∨ c = sk1 ∨ a = sk1 ∨ ¬(new X0 b sk4) ∨ (old sk1 sk2 sk3) := resolve eq3772 rule_def_0_0 -- subsumption resolution 3772,64
  have eq4848 : sk0 = sk5 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq2851 eq3184 -- resolution 2851,3184
  have eq4849 : sk0 = sk5 ∨ b = sk1 ∨ c = sk1 := resolve eq4848 rfl -- duplicate literal removal 4848
  have eq4851 : b = sk1 ∨ c = sk1 := resolve eq4849 preserve_4 -- subsumption resolution 4849,81
  have eq4892 : (new sk0 b sk2) ∨ c = sk1 := eq4851.imp_left (fun h : b = sk1 ↦ superpose h preserve_0) -- superposition 77,4851, 4851 into 77, unify on (0).2 in 4851 and (0).2 in 77
  have eq4893 : (new b sk2 sk3) ∨ c = sk1 := eq4851.imp_left (fun h : b = sk1 ↦ superpose h preserve_1) -- superposition 78,4851, 4851 into 78, unify on (0).2 in 4851 and (0).1 in 78
  have eq4894 : (new b sk4 sk3) ∨ c = sk1 := eq4851.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 79,4851, 4851 into 79, unify on (0).2 in 4851 and (0).1 in 79
  have eq4895 : (new sk5 b sk4) ∨ c = sk1 := eq4851.imp_left (fun h : b = sk1 ↦ superpose h preserve_3) -- superposition 80,4851, 4851 into 80, unify on (0).2 in 4851 and (0).2 in 80
  have eq6013 : c = sk1 ∨ c = sk2 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk4 ∨ c = sk1 ∨ c = sk4 := resolve eq2532 eq263 -- resolution 2532,263
  have eq6055 : c = sk1 ∨ c = sk2 ∨ sk0 = sk5 ∨ c = sk3 ∨ c = sk4 := resolve eq6013 rfl -- duplicate literal removal 6013
  have eq6056 : c = sk4 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq6055 preserve_4 -- subsumption resolution 6055,81
  have eq6060 : (new sk5 sk1 c) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := eq6056.imp_left (fun h : c = sk4 ↦ superpose h preserve_3) -- superposition 80,6056, 6056 into 80, unify on (0).2 in 6056 and (0).3 in 80
  have eq6078 : (old sk5 sk1 c) ∨ c = sk1 ∨ a = sk5 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq6056.imp_left (fun h : c = sk4 ↦ superpose h eq265)) -- superposition 265,6056, 6056 into 265, unify on (0).2 in 6056 and (0).3 in 265
  have eq6230 : (old sk5 sk1 c) ∨ c = sk1 ∨ a = sk5 ∨ c = sk2 ∨ c = sk3 := resolve eq6078 rfl -- duplicate literal removal 6078
  have eq6242 : a = sk5 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq6230 p4XY -- subsumption resolution 6230,55
  have eq6297 : a ≠ sk0 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := eq6242.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 81,6242, 6242 into 81, unify on (0).2 in 6242 and (0).2 in 81
  have eq6370 : c = sk1 ∨ c = sk2 ∨ sk0 = sk5 ∨ a = sk1 ∨ c = sk4 ∨ c = sk1 ∨ c = sk4 := resolve eq2600 eq263 -- resolution 2600,263
  have eq6412 : c = sk1 ∨ c = sk2 ∨ sk0 = sk5 ∨ a = sk1 ∨ c = sk4 := resolve eq6370 rfl -- duplicate literal removal 6370
  have eq6413 : c = sk4 ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq6412 preserve_4 -- subsumption resolution 6412,81
  have eq6436 : (old sk5 sk1 c) ∨ c = sk1 ∨ a = sk5 ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq6413.imp_left (fun h : c = sk4 ↦ superpose h eq265)) -- superposition 265,6413, 6413 into 265, unify on (0).2 in 6413 and (0).3 in 265
  have eq6585 : (old sk5 sk1 c) ∨ c = sk1 ∨ a = sk5 ∨ c = sk2 ∨ a = sk1 := resolve eq6436 rfl -- duplicate literal removal 6436
  have eq6597 : a = sk5 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq6585 p4XY -- subsumption resolution 6585,55
  have eq6647 : a ≠ sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := eq6597.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 81,6597, 6597 into 81, unify on (0).2 in 6597 and (0).2 in 81
  have eq9342 (X0 : G) : (old sk1 sk2 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b c) ∨ (old sk1 sk2 sk3) ∨ c = sk3 := resolve eq437 eq370 -- resolution 437,370
  have eq9369 (X0 : G) : (old sk1 sk2 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b sk4) ∨ c = sk1 := resolve eq437 eq4894 -- resolution 437,4894
  have eq9383 (X0 : G) : (new b (sF0 b c sk3) X0) ∨ (old sk1 sk2 sk3) ∨ c = sk3 ∨ ¬(new X0 b c) := resolve eq9342 rfl -- duplicate literal removal 9342
  have eq9411 (X0 : G) : (old sk1 sk4 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b c) ∨ (old sk1 sk4 sk3) ∨ c = sk3 := resolve eq446 eq384 -- resolution 446,384
  have eq9433 (X0 : G) : (old sk1 sk4 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b sk2) ∨ c = sk1 := resolve eq446 eq4893 -- resolution 446,4893
  have eq9448 (X0 : G) : (new b (sF0 b c sk3) X0) ∨ (old sk1 sk4 sk3) ∨ c = sk3 ∨ ¬(new X0 b c) := resolve eq9411 rfl -- duplicate literal removal 9411
  have eq15739 : (old sk1 sk2 sk3) ∨ a = sk1 ∨ (sP0 b (sF0 sk1 sk2 sk3) a) ∨ (old b (sF0 sk1 sk2 sk3) a) ∨ ¬(new a b c) := resolve eq1915 eq87 -- resolution 1915,87
  have eq15758 : (sP0 b (sF0 sk1 sk2 sk3) a) ∨ a = sk1 ∨ (old sk1 sk2 sk3) ∨ (old b (sF0 sk1 sk2 sk3) a) := resolve eq15739 eq84 -- subsumption resolution 15739,84
  have eq16027 : (old sk1 sk4 sk3) ∨ a = sk1 ∨ (sP0 b (sF0 sk1 sk4 sk3) a) ∨ (old b (sF0 sk1 sk4 sk3) a) ∨ ¬(new a b c) := resolve eq2040 eq87 -- resolution 2040,87
  have eq16051 : (sP0 b (sF0 sk1 sk4 sk3) a) ∨ a = sk1 ∨ (old sk1 sk4 sk3) ∨ (old b (sF0 sk1 sk4 sk3) a) := resolve eq16027 eq84 -- subsumption resolution 16027,84
  have eq18001 (X0 : G) : (sP1 b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b c) ∨ (sP0 b (sF0 b c sk3) X0) ∨ (old b (sF0 b c sk3) X0) ∨ (old sk1 sk2 sk3) := resolve eq9383 new_imp -- resolution 9383,73
  have eq18040 (X0 : G) : (sP1 b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b c) ∨ (sP0 b (sF0 b c sk3) X0) ∨ (old b (sF0 b c sk3) X0) ∨ (old sk1 sk4 sk3) := resolve eq9448 new_imp -- resolution 9448,73
  have eq23851 : a = sk1 ∨ (old sk1 sk2 sk3) ∨ (old b (sF0 sk1 sk2 sk3) a) ∨ a = c := resolve eq15758 rule_def_0_2 -- resolution 15758,66
  have eq23861 : (old b (sF0 sk1 sk2 sk3) a) ∨ (old sk1 sk2 sk3) ∨ a = sk1 := resolve eq23851 ac -- subsumption resolution 23851,52
  have eq23887 : (new b (sF0 sk1 sk2 sk3) a) ∨ a = sk1 ∨ (old sk1 sk2 sk3) := resolve eq23861 imp_new_0 -- resolution 23861,62
  have eq23988 : a = sk1 ∨ (old sk1 sk4 sk3) ∨ (old b (sF0 sk1 sk4 sk3) a) ∨ a = c := resolve eq16051 rule_def_0_2 -- resolution 16051,66
  have eq24002 : (old b (sF0 sk1 sk4 sk3) a) ∨ (old sk1 sk4 sk3) ∨ a = sk1 := resolve eq23988 ac -- subsumption resolution 23988,52
  have eq24030 : (new b (sF0 sk1 sk4 sk3) a) ∨ a = sk1 ∨ (old sk1 sk4 sk3) := resolve eq24002 imp_new_0 -- resolution 24002,62
  have eq24745 (X0 : G) : ¬(new b (sF0 sk1 sk2 sk3) X0) ∨ (old sk1 sk2 sk3) ∨ a = X0 ∨ a = sk1 := resolve eq23887 prev_0 -- resolution 23887,74
  have eq24949 (X0 : G) : ¬(new b (sF0 sk1 sk4 sk3) X0) ∨ (old sk1 sk4 sk3) ∨ a = X0 ∨ a = sk1 := resolve eq24030 prev_0 -- resolution 24030,74
  have eq51360 (X0 : G) : c = sk1 ∨ a = sk1 ∨ ¬(new X0 b sk2) ∨ (old sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) ∨ a = X0 ∨ a = sk1 := resolve eq3735 eq24949 -- resolution 3735,24949
  have eq51456 (X0 : G) : ¬(new X0 b sk2) ∨ a = sk1 ∨ c = sk1 ∨ (old sk1 sk4 sk3) ∨ a = X0 := resolve eq51360 rfl -- duplicate literal removal 51360
  have eq51564 : a = sk1 ∨ c = sk1 ∨ (old sk1 sk4 sk3) ∨ a = sk0 ∨ c = sk1 := resolve eq51456 eq4892 -- resolution 51456,4892
  have eq51573 : (old sk1 sk4 sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq51564 rfl -- duplicate literal removal 51564
  have eq51790 : (old sk1 c sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 ∨ c = sk2 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq6413.imp_left (fun h : c = sk4 ↦ superpose h eq51573)) -- superposition 51573,6413, 6413 into 51573, unify on (0).2 in 6413 and (0).2 in 51573
  have eq51797 : (old sk1 c sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 ∨ c = sk2 := resolve eq51790 rfl -- duplicate literal removal 51790
  have eq51866 : c = sk1 ∨ a = sk1 ∨ a = sk0 ∨ c = sk2 := resolve eq51797 p4XZ -- subsumption resolution 51797,56
  have eq51867 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq51866 eq6647 -- subsumption resolution 51866,6647
  have eq51909 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq51867.imp_left (fun h : c = sk2 ↦ superpose h eq150)) -- superposition 150,51867, 51867 into 150, unify on (0).2 in 51867 and (0).3 in 150
  have eq52484 : (old sk0 sk1 c) ∨ c = sk1 ∨ a = sk0 ∨ a = sk1 := resolve eq51909 rfl -- duplicate literal removal 51909
  have eq52493 : c = sk1 ∨ a = sk0 ∨ a = sk1 := resolve eq52484 p4XY -- subsumption resolution 52484,55
  have eq52634 : (old c sk2 sk3) ∨ c = b ∨ a = c ∨ a = sk0 ∨ a = sk1 := Or.assoc3 (eq52493.imp_left (fun h : c = sk1 ↦ superpose h eq229)) -- superposition 229,52493, 52493 into 229, unify on (0).2 in 52493 and (0).1 in 229
  have eq53660 : c = b ∨ a = c ∨ a = sk0 ∨ a = sk1 := resolve eq52634 p4YZ -- subsumption resolution 52634,57
  have eq53661 : a = c ∨ a = sk0 ∨ a = sk1 := resolve eq53660 bc -- subsumption resolution 53660,53
  have eq53662 : a = sk1 ∨ a = sk0 := resolve eq53661 ac -- subsumption resolution 53661,52
  have eq53754 : (new sk0 a sk2) ∨ a = sk0 := eq53662.imp_left (fun h : a = sk1 ↦ superpose h preserve_0) -- superposition 77,53662, 53662 into 77, unify on (0).2 in 53662 and (0).2 in 77
  have eq53761 (X0 : G) : ¬(new sk5 a X0) ∨ sk4 = X0 ∨ a = sk0 := Or.assoc2 (eq53662.imp_left (fun h : a = sk1 ↦ superpose h eq99)) -- superposition 99,53662, 53662 into 99, unify on (0).2 in 53662 and (0).2 in 99
  have eq54231 : (new sk5 a c) ∨ c = sk2 ∨ c = sk3 ∨ a = c ∨ a = sk0 := Or.assoc4 (eq53662.imp_left (fun h : a = sk1 ↦ superpose h eq6060)) -- superposition 6060,53662, 53662 into 6060, unify on (0).2 in 53662 and (0).2 in 6060
  have eq54858 : (new sk5 a c) ∨ c = sk2 ∨ c = sk3 ∨ a = sk0 := resolve eq54231 ac -- subsumption resolution 54231,52
  have eq73856 : c = sk2 ∨ c = sk3 ∨ a = sk0 ∨ c = sk4 ∨ a = sk0 := resolve eq54858 eq53761 -- resolution 54858,53761
  have eq73881 : c = sk4 ∨ c = sk3 ∨ a = sk0 ∨ c = sk2 := resolve eq73856 rfl -- duplicate literal removal 73856
  have eq138742 : c = sk3 ∨ ¬(new a b c) ∨ (sP0 b (sF0 b c sk3) a) ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk2 sk3) := resolve eq18001 eq87 -- resolution 18001,87
  have eq138789 : (sP0 b (sF0 b c sk3) a) ∨ c = sk3 ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk2 sk3) := resolve eq138742 eq84 -- subsumption resolution 138742,84
  have eq138873 : c = sk3 ∨ ¬(new a b c) ∨ (sP0 b (sF0 b c sk3) a) ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk4 sk3) := resolve eq18040 eq87 -- resolution 18040,87
  have eq138920 : (sP0 b (sF0 b c sk3) a) ∨ c = sk3 ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk4 sk3) := resolve eq138873 eq84 -- subsumption resolution 138873,84
  have eq178383 : c = sk3 ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk2 sk3) ∨ a = c := resolve eq138789 rule_def_0_2 -- resolution 138789,66
  have eq178392 : (old b (sF0 b c sk3) a) ∨ c = sk3 ∨ (old sk1 sk2 sk3) := resolve eq178383 ac -- subsumption resolution 178383,52
  have eq178580 : (new b (sF0 b c sk3) a) ∨ (old sk1 sk2 sk3) ∨ c = sk3 := resolve eq178392 imp_new_0 -- resolution 178392,62
  have eq178780 (X0 : G) : ¬(new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ a = X0 ∨ (old sk1 sk2 sk3) := resolve eq178580 prev_0 -- resolution 178580,74
  have eq180527 : c = sk3 ∨ (old b (sF0 b c sk3) a) ∨ (old sk1 sk4 sk3) ∨ a = c := resolve eq138920 rule_def_0_2 -- resolution 138920,66
  have eq180536 : (old b (sF0 b c sk3) a) ∨ c = sk3 ∨ (old sk1 sk4 sk3) := resolve eq180527 ac -- subsumption resolution 180527,52
  have eq180720 : (new b (sF0 b c sk3) a) ∨ (old sk1 sk4 sk3) ∨ c = sk3 := resolve eq180536 imp_new_0 -- resolution 180536,62
  have eq180864 (X0 : G) : ¬(new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ a = X0 ∨ (old sk1 sk4 sk3) := resolve eq180720 prev_0 -- resolution 180720,74
  have eq185566 (X0 : G) : c = sk1 ∨ a = sk1 ∨ ¬(new X0 b sk4) ∨ (old sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) ∨ a = X0 ∨ a = sk1 := resolve eq3783 eq24745 -- resolution 3783,24745
  have eq185703 (X0 : G) : ¬(new X0 b sk4) ∨ a = sk1 ∨ c = sk1 ∨ (old sk1 sk2 sk3) ∨ a = X0 := resolve eq185566 rfl -- duplicate literal removal 185566
  have eq185736 : a = sk1 ∨ c = sk1 ∨ (old sk1 sk2 sk3) ∨ a = sk5 ∨ c = sk1 := resolve eq185703 eq4895 -- resolution 185703,4895
  have eq185759 : (old sk1 sk2 sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk5 := resolve eq185736 rfl -- duplicate literal removal 185736
  have eq186007 : (old sk1 c sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk5 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq51867.imp_left (fun h : c = sk2 ↦ superpose h eq185759)) -- superposition 185759,51867, 51867 into 185759, unify on (0).2 in 51867 and (0).2 in 185759
  have eq186027 : (old sk1 c sk3) ∨ c = sk1 ∨ a = sk1 ∨ a = sk5 := resolve eq186007 rfl -- duplicate literal removal 186007
  have eq186123 : a = sk5 ∨ a = sk1 ∨ c = sk1 := resolve eq186027 p4XZ -- subsumption resolution 186027,56
  have eq186162 : a ≠ sk0 ∨ a = sk1 ∨ c = sk1 := eq186123.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 81,186123, 186123 into 81, unify on (0).2 in 186123 and (0).2 in 81
  have eq186612 : c = sk1 ∨ a = sk1 := resolve eq186162 eq53662 -- subsumption resolution 186162,53662
  have eq186678 : (old c sk2 sk3) ∨ c = b ∨ a = c ∨ a = sk1 := Or.assoc3 (eq186612.imp_left (fun h : c = sk1 ↦ superpose h eq229)) -- superposition 229,186612, 186612 into 229, unify on (0).2 in 186612 and (0).1 in 229
  have eq188338 : c = b ∨ a = c ∨ a = sk1 := resolve eq186678 p4YZ -- subsumption resolution 186678,57
  have eq188339 : a = c ∨ a = sk1 := resolve eq188338 bc -- subsumption resolution 188338,53
  have eq188340 : a = sk1 := resolve eq188339 ac -- subsumption resolution 188339,52
  have eq188341 : (new sk0 a sk2) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_0 -- backward demodulation 77,188340
  have eq188344 : (new sk5 a sk4) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_3 -- backward demodulation 80,188340
  have eq188349 : ∀ (X0 : G) , ¬(new X0 a sk2) ∨ sk0 = X0 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq101 -- backward demodulation 101,188340
  have eq188354 : (sP0 a sk2 sk3) ∨ (sP1 sk1 sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq113 -- backward demodulation 113,188340
  have eq188355 : (sP0 a sk4 sk3) ∨ (sP1 sk1 sk4 sk3) ∨ (old sk1 sk4 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq114 -- backward demodulation 114,188340
  have eq188400 : (old a sk2 sk3) ∨ c = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq192 -- backward demodulation 192,188340
  have eq189207 : a = c ∨ b = sk1 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4851 -- backward demodulation 4851,188340
  have eq189408 : a = c ∨ a ≠ sk0 ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6297 -- backward demodulation 6297,188340
  have eq189621 : ∀ (X0 : G) , (old a sk2 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b sk4) ∨ c = sk1 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9369 -- backward demodulation 9369,188340
  have eq189634 : ∀ (X0 : G) , (old a sk4 sk3) ∨ (new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ ¬(new X0 b sk2) ∨ c = sk1 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq9433 -- backward demodulation 9433,188340
  have eq198582 : ∀ (X0 : G) , (old a sk2 sk3) ∨ ¬(new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ a = X0 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq178780 -- backward demodulation 178780,188340
  have eq198678 : ∀ (X0 : G) , (old a sk4 sk3) ∨ ¬(new b (sF0 b c sk3) X0) ∨ c = sk3 ∨ a = X0 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq180864 -- backward demodulation 180864,188340
  have eq199314 : (sP1 a sk2 sk3) ∨ (sP0 a sk2 sk3) ∨ (old sk1 sk2 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188354 -- forward demodulation 188354,188340
  have eq199315 : (sP1 a sk2 sk3) ∨ (old a sk2 sk3) ∨ (sP0 a sk2 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq199314 -- forward demodulation 199314,188340
  have eq199316 : (sP1 a sk4 sk3) ∨ (sP0 a sk4 sk3) ∨ (old sk1 sk4 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188355 -- forward demodulation 188355,188340
  have eq199317 : (sP1 a sk4 sk3) ∨ (old a sk4 sk3) ∨ (sP0 a sk4 sk3) := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq199316 -- forward demodulation 199316,188340
  have eq200105 : b = sk1 := resolve eq189207 ac -- subsumption resolution 189207,52
  have eq200106 : a = b := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq200105 -- forward demodulation 200105,188340
  have eq200109 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 65,200106
  have eq200122 : ∀ (X0 : G) , ¬(new X0 a c) ∨ a = X0 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq100 -- backward demodulation 100,200106
  have eq201190 : (old a sk2 sk3) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188400 -- backward demodulation 188400,200106
  have eq204170 : a ≠ sk0 ∨ c = sk2 ∨ c = sk3 := resolve eq189408 ac -- subsumption resolution 189408,52
  have eq204392 : ∀ (X0 : G) , (new a (sF0 a c sk3) X0) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ ¬(new X0 b sk4) ∨ c = sk1 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq189621 -- forward demodulation 189621,200106
  have eq204393 : ∀ (X0 : G) , ¬(new X0 a sk4) ∨ (new a (sF0 a c sk3) X0) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq204392 -- forward demodulation 204392,200106
  have eq204394 : ∀ (X0 : G) , a = c ∨ ¬(new X0 a sk4) ∨ (new a (sF0 a c sk3) X0) ∨ (old a sk2 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq204393 -- forward demodulation 204393,188340
  have eq204395 (X0 : G) : (new a (sF0 a c sk3) X0) ∨ ¬(new X0 a sk4) ∨ (old a sk2 sk3) ∨ c = sk3 := resolve eq204394 ac -- subsumption resolution 204394,52
  have eq204434 : ∀ (X0 : G) , (new a (sF0 a c sk3) X0) ∨ (old a sk4 sk3) ∨ c = sk3 ∨ ¬(new X0 b sk2) ∨ c = sk1 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq189634 -- forward demodulation 189634,200106
  have eq204435 : ∀ (X0 : G) , ¬(new X0 a sk2) ∨ (new a (sF0 a c sk3) X0) ∨ (old a sk4 sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq204434 -- forward demodulation 204434,200106
  have eq204436 : ∀ (X0 : G) , a = c ∨ ¬(new X0 a sk2) ∨ (new a (sF0 a c sk3) X0) ∨ (old a sk4 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq188340, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq204435 -- forward demodulation 204435,188340
  have eq204437 (X0 : G) : (new a (sF0 a c sk3) X0) ∨ ¬(new X0 a sk2) ∨ (old a sk4 sk3) ∨ c = sk3 := resolve eq204436 ac -- subsumption resolution 204436,52
  have eq218376 : ∀ (X0 : G) , ¬(new a (sF0 a c sk3) X0) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ a = X0 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq198582 -- forward demodulation 198582,200106
  have eq218598 : ∀ (X0 : G) , ¬(new a (sF0 a c sk3) X0) ∨ (old a sk4 sk3) ∨ c = sk3 ∨ a = X0 := Eq.mp (by simp only [eq200106, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq198678 -- forward demodulation 198678,200106
  have eq225434 (X0 : G) : ¬(new X0 a sk4) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ (old a sk2 sk3) ∨ c = sk3 ∨ a = X0 := resolve eq204395 eq218376 -- resolution 204395,218376
  have eq225470 (X0 : G) : ¬(new X0 a sk4) ∨ (old a sk2 sk3) ∨ c = sk3 ∨ a = X0 := resolve eq225434 rfl -- duplicate literal removal 225434
  have eq225490 : (old a sk2 sk3) ∨ c = sk3 ∨ a = sk5 := resolve eq225470 eq188344 -- resolution 225470,188344
  have eq225622 (X0 : G) : ¬(new X0 a sk2) ∨ (old a sk4 sk3) ∨ c = sk3 ∨ (old a sk4 sk3) ∨ c = sk3 ∨ a = X0 := resolve eq204437 eq218598 -- resolution 204437,218598
  have eq225660 (X0 : G) : ¬(new X0 a sk2) ∨ (old a sk4 sk3) ∨ c = sk3 ∨ a = X0 := resolve eq225622 rfl -- duplicate literal removal 225622
  have eq225668 : (old a sk4 sk3) ∨ c = sk3 ∨ a = sk0 := resolve eq225660 eq188341 -- resolution 225660,188341
  have eq225719 : (old a c sk3) ∨ c = sk3 ∨ a = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk2 := Or.assoc3 (eq73881.imp_left (fun h : c = sk4 ↦ superpose h eq225668)) -- superposition 225668,73881, 73881 into 225668, unify on (0).2 in 73881 and (0).2 in 225668
  have eq225727 : (old a c sk3) ∨ c = sk3 ∨ a = sk0 ∨ c = sk2 := resolve eq225719 rfl -- duplicate literal removal 225719
  have eq225748 : c = sk3 ∨ a = sk0 ∨ c = sk2 := resolve eq225727 p4XZ -- subsumption resolution 225727,56
  have eq225749 : c = sk3 ∨ c = sk2 := resolve eq225748 eq204170 -- subsumption resolution 225748,204170
  have eq225767 : (sP1 a sk4 c) ∨ (old a sk4 c) ∨ (sP0 a sk4 c) ∨ c = sk2 := Or.assoc3 (eq225749.imp_left (fun h : c = sk3 ↦ superpose h eq199317)) -- superposition 199317,225749, 225749 into 199317, unify on (0).2 in 225749 and (0).3 in 199317
  have eq225779 : (old a sk2 c) ∨ a = sk2 ∨ c = sk2 ∨ c = sk2 := Or.assoc3 (eq225749.imp_left (fun h : c = sk3 ↦ superpose h eq201190)) -- superposition 201190,225749, 225749 into 201190, unify on (0).2 in 225749 and (0).3 in 201190
  have eq225936 : (old a sk2 c) ∨ a = sk2 ∨ c = sk2 := resolve eq225779 rfl -- duplicate literal removal 225779
  have eq225947 : (old a sk4 c) ∨ (sP0 a sk4 c) ∨ c = sk2 := resolve eq225767 eq91 -- subsumption resolution 225767,91
  have eq225948 : (sP0 a sk4 c) ∨ c = sk2 := resolve eq225947 p4XY -- subsumption resolution 225947,55
  have eq225951 : c = sk2 ∨ a = sk2 := resolve eq225936 p4XY -- subsumption resolution 225936,55
  have eq226253 : (new sk0 a c) ∨ a = sk0 ∨ a = sk2 := Or.assoc2 (eq225951.imp_left (fun h : c = sk2 ↦ superpose h eq53754)) -- superposition 53754,225951, 225951 into 53754, unify on (0).2 in 225951 and (0).3 in 53754
  have eq226359 : (old a c sk3) ∨ c = sk3 ∨ a = sk5 ∨ a = sk2 := Or.assoc3 (eq225951.imp_left (fun h : c = sk2 ↦ superpose h eq225490)) -- superposition 225490,225951, 225951 into 225490, unify on (0).2 in 225951 and (0).2 in 225490
  have eq226366 : a = sk2 ∨ a = sk0 := resolve eq226253 eq200122 -- subsumption resolution 226253,200122
  have eq226428 : a = sk5 ∨ c = sk3 ∨ a = sk2 := resolve eq226359 p4XZ -- subsumption resolution 226359,56
  have eq226643 : a = sk4 ∨ c = sk2 := resolve eq225948 eq200109 -- resolution 225948,200109
  have eq228311 : a ≠ sk0 ∨ c = sk3 ∨ a = sk2 := eq226428.imp_left (fun h : a = sk5 ↦ superpose h preserve_4) -- superposition 81,226428, 226428 into 81, unify on (0).2 in 226428 and (0).2 in 81
  have eq228386 : c = sk3 ∨ a = sk2 := resolve eq228311 eq226366 -- subsumption resolution 228311,226366
  have eq228409 : (sP1 a sk2 c) ∨ (old a sk2 c) ∨ (sP0 a sk2 c) ∨ a = sk2 := Or.assoc3 (eq228386.imp_left (fun h : c = sk3 ↦ superpose h eq199315)) -- superposition 199315,228386, 228386 into 199315, unify on (0).2 in 228386 and (0).3 in 199315
  have eq228660 : (old a sk2 c) ∨ (sP0 a sk2 c) ∨ a = sk2 := resolve eq228409 eq91 -- subsumption resolution 228409,91
  have eq228661 : (sP0 a sk2 c) ∨ a = sk2 := resolve eq228660 p4XY -- subsumption resolution 228660,55
  have eq228662 : a = sk2 := resolve eq228661 eq200109 -- subsumption resolution 228661,200109
  have eq228725 : ∀ (X0 : G) , ¬(new X0 a a) ∨ sk0 = X0 := Eq.mp (by simp only [eq228662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188349 -- backward demodulation 188349,228662
  have eq229658 : a = c ∨ a = sk4 := Eq.mp (by simp only [eq228662, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq226643 -- backward demodulation 226643,228662
  have eq231158 : a = sk4 := resolve eq229658 ac -- subsumption resolution 229658,52
  have eq231176 : (new sk5 a a) := Eq.mp (by simp only [eq231158, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188344 -- backward demodulation 188344,231158
  have eq231273 : sk0 = sk5 := resolve eq228725 eq231176 -- resolution 228725,231176
  subsumption preserve_4 eq231273 -- subsumption resolution 231273,81

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq104 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq119 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ b = sk0 := resolve eq104 rule_def_1_0 -- resolution 104,68
  have eq121 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq119 preserve_2 -- subsumption resolution 119,79
  have eq137 : (old sk0 sk1 sk2) ∨ a = sk0 := resolve eq121 rule_def_0_0 -- resolution 121,64
  have eq138 : (old sk0 sk1 sk2) := resolve eq137 preserve_1 -- subsumption resolution 137,78
  have eq145 : memold sk0 := resolve eq138 old_mem1 -- resolution 138,74
  subsumption preserve_3 eq145 -- subsumption resolution 145,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq104 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq118 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ c = sk1 := resolve eq104 rule_def_1_1 -- resolution 104,69
  have eq121 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq118 preserve_4 -- subsumption resolution 118,81
  have eq134 : (old sk0 sk1 sk2) ∨ b = sk1 := resolve eq121 rule_def_0_1 -- resolution 121,65
  have eq136 : (old sk0 sk1 sk2) := resolve eq134 preserve_2 -- subsumption resolution 134,79
  have eq145 : memold sk1 := resolve eq136 old_mem2 -- resolution 136,75
  subsumption preserve_3 eq145 -- subsumption resolution 145,80

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sF0 : G → G → G → G) (sP1 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b (sF0 X Y Z) ∨ ¬sP1 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq93 (X0 X1 X2 : G) : ¬(sP1 X0 X1 X2) ∨ memold X2 := resolve rule_def_1_2 old_mem1 -- resolution 70,74
  have eq104 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 73,77
  have eq116 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ memold sk2 := resolve eq104 eq93 -- resolution 104,93
  have eq120 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq116 preserve_3 -- subsumption resolution 116,80
  have eq123 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq120 rule_def_0_2 -- resolution 120,66
  have eq126 : (old sk0 sk1 sk2) := resolve eq123 preserve_4 -- subsumption resolution 123,81
  have eq135 : memold sk2 := resolve eq126 old_mem3 -- resolution 126,76
  subsumption preserve_3 eq135 -- subsumption resolution 135,80

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X3 ∨ ¬ R X3 X1 X4 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X0 = X3)
  rule_3 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X1 X2 ∨ ¬ R X1 X2 X3 ∨ ¬ R X1 X4 X3 ∨ ¬ R X5 X1 X4 ∨ X5 = X0)
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
  let sP1 (X Y Z) := ∃ sF0, b = X ∧ c = Y ∧ ps.R Z b sF0 ∧ ps.R b sF0 a
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_3 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sF0 sP1 bc p4XY p4XZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 new_imp
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sF0 sP1 ac bc p3 p4XY p4XZ p4YZ prev_0 prev_1 prev_2 ps.rule_3 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_1_3 new_imp imp_new_0

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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X2 X3 ∨ ¬ ps.compl X3 X1 X4 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X2) (max (Nat.pair X3 X1) (max (Nat.pair X1 X4) 0)))
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

theorem PartialSolution.toMagma_equation1113 :
    letI := ps.toMagma
    Equation1113 ℕ := by
  simp only [Equation1113, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun X1 (ps.complFun X0 X1)) (ps.complFun (ps.complFun X1 (ps.complFun X0 X1)) X1)


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2441 : PartialSolution ℕ where
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
theorem _root_.Equation1113_not_implies_Equation2441 : ∃ (G : Type) (_ : Magma G), Equation1113 G ∧ ¬Equation2441 G := by
  use ℕ, PartialSolution.counter2441.toMagma, PartialSolution.counter2441.toMagma_equation1113
  simp only [not_forall, PartialSolution.toMagma]
  use 1
  repeat (first | rw [PartialSolution.counter2441.of_R 1 1 2] | rw [PartialSolution.counter2441.of_R 1 2 2] | rw [PartialSolution.counter2441.of_R 1 3 1] | rw [PartialSolution.counter2441.of_R 2 1 3])
  all_goals simp [PartialSolution.counter2441]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter2534 : PartialSolution ℕ where
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
theorem _root_.Equation1113_not_implies_Equation2534 : ∃ (G : Type) (_ : Magma G), Equation1113 G ∧ ¬Equation2534 G := by
  use ℕ, PartialSolution.counter2534.toMagma, PartialSolution.counter2534.toMagma_equation1113
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter2534.of_R 1 1 1] | rw [PartialSolution.counter2534.of_R 1 2 1])
  all_goals simp [PartialSolution.counter2534]

end Eq1113