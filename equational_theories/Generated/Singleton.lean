import equational_theories.Magma
import equational_theories.Equations.All
import Mathlib.Tactic

namespace Singleton

/- Equational laws that imply the magma has a single element -/

@[equational_result]
theorem Equation89_implies_Equation2 (G: Type*) [Magma G] (h: Equation89 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation144_implies_Equation2 (G: Type*) [Magma G] (h: Equation144 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation147_implies_Equation2 (G: Type*) [Magma G] (h: Equation147 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation148_implies_Equation2 (G: Type*) [Magma G] (h: Equation148 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation149_implies_Equation2 (G: Type*) [Magma G] (h: Equation149 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation233_implies_Equation2 (G: Type*) [Magma G] (h: Equation233 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation515_implies_Equation2 (G: Type*) [Magma G] (h: Equation515 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation517_implies_Equation2 (G: Type*) [Magma G] (h: Equation517 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation518_implies_Equation2 (G: Type*) [Magma G] (h: Equation518 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation526_implies_Equation2 (G: Type*) [Magma G] (h: Equation526 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation529_implies_Equation2 (G: Type*) [Magma G] (h: Equation529 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation530_implies_Equation2 (G: Type*) [Magma G] (h: Equation530 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation612_implies_Equation2 (G: Type*) [Magma G] (h: Equation612 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

@[equational_result]
theorem Equation718_implies_Equation2 (G: Type*) [Magma G] (h: Equation718 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation720_implies_Equation2 (G: Type*) [Magma G] (h: Equation720 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation728_implies_Equation2 (G: Type*) [Magma G] (h: Equation728 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation729_implies_Equation2 (G: Type*) [Magma G] (h: Equation729 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation923_implies_Equation2 (G: Type*) [Magma G] (h: Equation923 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation924_implies_Equation2 (G: Type*) [Magma G] (h: Equation924 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation932_implies_Equation2 (G: Type*) [Magma G] (h: Equation932 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation935_implies_Equation2 (G: Type*) [Magma G] (h: Equation935 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation936_implies_Equation2 (G: Type*) [Magma G] (h: Equation936 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation939_implies_Equation2 (G: Type*) [Magma G] (h: Equation939 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation940_implies_Equation2 (G: Type*) [Magma G] (h: Equation940 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation941_implies_Equation2 (G: Type*) [Magma G] (h: Equation941 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation966_implies_Equation2 (G: Type*) [Magma G] (h: Equation966 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation971_implies_Equation2 (G: Type*) [Magma G] (h: Equation971 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation973_implies_Equation2 (G: Type*) [Magma G] (h: Equation973 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation974_implies_Equation2 (G: Type*) [Magma G] (h: Equation974 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation983_implies_Equation2 (G: Type*) [Magma G] (h: Equation983 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation987_implies_Equation2 (G: Type*) [Magma G] (h: Equation987 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation988_implies_Equation2 (G: Type*) [Magma G] (h: Equation988 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation990_implies_Equation2 (G: Type*) [Magma G] (h: Equation990 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1005_implies_Equation2 (G: Type*) [Magma G] (h: Equation1005 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1123_implies_Equation2 (G: Type*) [Magma G] (h: Equation1123 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

@[equational_result]
theorem Equation1124_implies_Equation2 (G: Type*) [Magma G] (h: Equation1124 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1126_implies_Equation2 (G: Type*) [Magma G] (h: Equation1126 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1127_implies_Equation2 (G: Type*) [Magma G] (h: Equation1127 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1134_implies_Equation2 (G: Type*) [Magma G] (h: Equation1134 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1135_implies_Equation2 (G: Type*) [Magma G] (h: Equation1135 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1138_implies_Equation2 (G: Type*) [Magma G] (h: Equation1138 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1139_implies_Equation2 (G: Type*) [Magma G] (h: Equation1139 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1142_implies_Equation2 (G: Type*) [Magma G] (h: Equation1142 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1143_implies_Equation2 (G: Type*) [Magma G] (h: Equation1143 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1144_implies_Equation2 (G: Type*) [Magma G] (h: Equation1144 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1168_implies_Equation2 (G: Type*) [Magma G] (h: Equation1168 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1169_implies_Equation2 (G: Type*) [Magma G] (h: Equation1169 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1330_implies_Equation2 (G: Type*) [Magma G] (h: Equation1330 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1337_implies_Equation2 (G: Type*) [Magma G] (h: Equation1337 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1338_implies_Equation2 (G: Type*) [Magma G] (h: Equation1338 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1341_implies_Equation2 (G: Type*) [Magma G] (h: Equation1341 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1342_implies_Equation2 (G: Type*) [Magma G] (h: Equation1342 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1345_implies_Equation2 (G: Type*) [Magma G] (h: Equation1345 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1346_implies_Equation2 (G: Type*) [Magma G] (h: Equation1346 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1347_implies_Equation2 (G: Type*) [Magma G] (h: Equation1347 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1372_implies_Equation2 (G: Type*) [Magma G] (h: Equation1372 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1375_implies_Equation2 (G: Type*) [Magma G] (h: Equation1375 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1376_implies_Equation2 (G: Type*) [Magma G] (h: Equation1376 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1379_implies_Equation2 (G: Type*) [Magma G] (h: Equation1379 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1380_implies_Equation2 (G: Type*) [Magma G] (h: Equation1380 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1381_implies_Equation2 (G: Type*) [Magma G] (h: Equation1381 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1390_implies_Equation2 (G: Type*) [Magma G] (h: Equation1390 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1392_implies_Equation2 (G: Type*) [Magma G] (h: Equation1392 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1393_implies_Equation2 (G: Type*) [Magma G] (h: Equation1393 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1396_implies_Equation2 (G: Type*) [Magma G] (h: Equation1396 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1397_implies_Equation2 (G: Type*) [Magma G] (h: Equation1397 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1398_implies_Equation2 (G: Type*) [Magma G] (h: Equation1398 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1406_implies_Equation2 (G: Type*) [Magma G] (h: Equation1406 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1407_implies_Equation2 (G: Type*) [Magma G] (h: Equation1407 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1408_implies_Equation2 (G: Type*) [Magma G] (h: Equation1408 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1411_implies_Equation2 (G: Type*) [Magma G] (h: Equation1411 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1412_implies_Equation2 (G: Type*) [Magma G] (h: Equation1412 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1413_implies_Equation2 (G: Type*) [Magma G] (h: Equation1413 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1416_implies_Equation2 (G: Type*) [Magma G] (h: Equation1416 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1417_implies_Equation2 (G: Type*) [Magma G] (h: Equation1417 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1418_implies_Equation2 (G: Type*) [Magma G] (h: Equation1418 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1421_implies_Equation2 (G: Type*) [Magma G] (h: Equation1421 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

@[equational_result]
theorem Equation1422_implies_Equation2 (G: Type*) [Magma G] (h: Equation1422 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

@[equational_result]
theorem Equation1423_implies_Equation2 (G: Type*) [Magma G] (h: Equation1423 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

@[equational_result]
theorem Equation1424_implies_Equation2 (G: Type*) [Magma G] (h: Equation1424 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

@[equational_result]
theorem Equation1530_implies_Equation2 (G: Type*) [Magma G] (h: Equation1530 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1532_implies_Equation2 (G: Type*) [Magma G] (h: Equation1532 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1533_implies_Equation2 (G: Type*) [Magma G] (h: Equation1533 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1540_implies_Equation2 (G: Type*) [Magma G] (h: Equation1540 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1541_implies_Equation2 (G: Type*) [Magma G] (h: Equation1541 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1544_implies_Equation2 (G: Type*) [Magma G] (h: Equation1544 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1545_implies_Equation2 (G: Type*) [Magma G] (h: Equation1545 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1732_implies_Equation2 (G: Type*) [Magma G] (h: Equation1732 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

@[equational_result]
theorem Equation1733_implies_Equation2 (G: Type*) [Magma G] (h: Equation1733 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1736_implies_Equation2 (G: Type*) [Magma G] (h: Equation1736 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1744_implies_Equation2 (G: Type*) [Magma G] (h: Equation1744 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1748_implies_Equation2 (G: Type*) [Magma G] (h: Equation1748 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1752_implies_Equation2 (G: Type*) [Magma G] (h: Equation1752 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1753_implies_Equation2 (G: Type*) [Magma G] (h: Equation1753 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

@[equational_result]
theorem Equation1778_implies_Equation2 (G: Type*) [Magma G] (h: Equation1778 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1936_implies_Equation2 (G: Type*) [Magma G] (h: Equation1936 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1938_implies_Equation2 (G: Type*) [Magma G] (h: Equation1938 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1939_implies_Equation2 (G: Type*) [Magma G] (h: Equation1939 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1946_implies_Equation2 (G: Type*) [Magma G] (h: Equation1946 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation1947_implies_Equation2 (G: Type*) [Magma G] (h: Equation1947 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation2341_implies_Equation2 (G: Type*) [Magma G] (h: Equation2341 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

@[equational_result]
theorem Equation2344_implies_Equation2 (G: Type*) [Magma G] (h: Equation2344 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation2345_implies_Equation2 (G: Type*) [Magma G] (h: Equation2345 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation3154_implies_Equation2 (G: Type*) [Magma G] (h: Equation3154 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation3156_implies_Equation2 (G: Type*) [Magma G] (h: Equation3156 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation3157_implies_Equation2 (G: Type*) [Magma G] (h: Equation3157 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

end Singleton
