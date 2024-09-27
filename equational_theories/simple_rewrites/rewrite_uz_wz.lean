import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation92 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ z))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation144 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ z)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation196 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ z)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation248 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ z
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation300 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ z
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation352 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ z)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation404 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ z
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation456 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation493 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ z)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation530 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation547 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ z)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation564 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ z)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation573 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ z)))
def Equation577 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ z)))
def Equation579 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ x)))
def Equation580 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ y)))
def Equation581 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ z)))
def Equation587 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (z ∘ (w ∘ u)))
def Equation592 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (x ∘ u)))
def Equation597 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (y ∘ u)))
def Equation602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (z ∘ u)))
def Equation607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (w ∘ u)))
def Equation608 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ x)))
def Equation609 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ y)))
def Equation610 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ z)))
def Equation611 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ w)))
def Equation612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ u)))
def Equation659 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation696 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ z))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation733 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation750 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ z))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation767 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ z))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation776 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ z))
def Equation780 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ z))
def Equation782 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ x))
def Equation783 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ y))
def Equation784 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ z))
def Equation790 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((z ∘ w) ∘ u))
def Equation795 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ x) ∘ u))
def Equation800 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ y) ∘ u))
def Equation805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ z) ∘ u))
def Equation810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ w) ∘ u))
def Equation811 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ x))
def Equation812 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ y))
def Equation813 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ z))
def Equation814 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ w))
def Equation815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ u))
def Equation862 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation899 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ z))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation936 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation953 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ z))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation970 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ z))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation979 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ z))
def Equation983 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ z))
def Equation985 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ x))
def Equation986 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ y))
def Equation987 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ z))
def Equation993 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ z) ∘ (w ∘ u))
def Equation998 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (x ∘ u))
def Equation1003 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (y ∘ u))
def Equation1008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (z ∘ u))
def Equation1013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (w ∘ u))
def Equation1014 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ x))
def Equation1015 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ y))
def Equation1016 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ z))
def Equation1017 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ w))
def Equation1018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ u))
def Equation1065 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1102 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ z)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1139 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1156 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ z)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1173 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ z)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1182 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ z)
def Equation1186 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ z)
def Equation1188 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ x)
def Equation1189 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ y)
def Equation1190 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ z)
def Equation1196 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ u)
def Equation1201 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ u)
def Equation1206 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ u)
def Equation1211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ u)
def Equation1216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ u)
def Equation1217 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ x)
def Equation1218 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ y)
def Equation1219 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ z)
def Equation1220 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ w)
def Equation1221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ u)
def Equation1268 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1305 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ z)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1342 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1359 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ z)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1376 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ z)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1385 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ z)
def Equation1389 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ z)
def Equation1391 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ x)
def Equation1392 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ y)
def Equation1393 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ z)
def Equation1399 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ z) ∘ w) ∘ u)
def Equation1404 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ x) ∘ u)
def Equation1409 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ y) ∘ u)
def Equation1414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ z) ∘ u)
def Equation1419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ w) ∘ u)
def Equation1420 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ x)
def Equation1421 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ y)
def Equation1422 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ z)
def Equation1423 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ w)
def Equation1424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ u)
def Equation1471 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1508 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ z))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1545 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1562 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ z))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1579 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ z))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ z))
def Equation1592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ z))
def Equation1594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ x))
def Equation1595 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ y))
def Equation1596 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ z))
def Equation1602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (z ∘ (w ∘ u))
def Equation1607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (x ∘ u))
def Equation1612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (y ∘ u))
def Equation1617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (z ∘ u))
def Equation1622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (w ∘ u))
def Equation1623 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ x))
def Equation1624 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ y))
def Equation1625 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ z))
def Equation1626 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ w))
def Equation1627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ u))
def Equation1674 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1711 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ z)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1748 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1765 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ z)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1782 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ z)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1791 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ z)
def Equation1795 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ z)
def Equation1797 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ x)
def Equation1798 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ y)
def Equation1799 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ z)
def Equation1805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ u)
def Equation1810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ u)
def Equation1815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ u)
def Equation1820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ u)
def Equation1825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ u)
def Equation1826 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ x)
def Equation1827 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ y)
def Equation1828 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ z)
def Equation1829 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ w)
def Equation1830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ u)
def Equation1877 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1914 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ z)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1951 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1968 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ z)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1985 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ z)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation1994 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ z)
def Equation1998 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ z)
def Equation2000 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ x)
def Equation2001 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ y)
def Equation2002 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ z)
def Equation2008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ u)
def Equation2013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ u)
def Equation2018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ u)
def Equation2023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ u)
def Equation2028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ u)
def Equation2029 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ x)
def Equation2030 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ y)
def Equation2031 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ z)
def Equation2032 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ w)
def Equation2033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ u)
def Equation2080 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2117 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ z)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2154 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2171 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ z)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2188 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ z)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2197 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ z)
def Equation2201 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ z)
def Equation2203 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ x)
def Equation2204 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ y)
def Equation2205 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ z)
def Equation2211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ u)
def Equation2216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ u)
def Equation2221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ u)
def Equation2226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ u)
def Equation2231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ u)
def Equation2232 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ x)
def Equation2233 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ y)
def Equation2234 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ z)
def Equation2235 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ w)
def Equation2236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ u)
def Equation2283 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2320 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ z
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2357 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2374 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ z
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2391 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ z
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2400 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ z
def Equation2404 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ z
def Equation2406 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ x
def Equation2407 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ y
def Equation2408 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ z
def Equation2414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ u
def Equation2419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ u
def Equation2424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ u
def Equation2429 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ u
def Equation2434 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ u
def Equation2435 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ x
def Equation2436 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ y
def Equation2437 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ z
def Equation2438 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ w
def Equation2439 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ u
def Equation2486 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2523 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ z
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2577 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ z
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ z
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2603 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ z
def Equation2607 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ z
def Equation2609 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ x
def Equation2610 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ y
def Equation2611 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ z
def Equation2617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ u
def Equation2622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ u
def Equation2627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ u
def Equation2632 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ u
def Equation2637 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ u
def Equation2638 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ x
def Equation2639 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ y
def Equation2640 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ z
def Equation2641 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ w
def Equation2642 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ u
def Equation2689 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2726 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ z
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2763 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2780 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ z
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2797 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ z
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2806 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ z
def Equation2810 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ z
def Equation2812 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ x
def Equation2813 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ y
def Equation2814 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ z
def Equation2820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ u
def Equation2825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ u
def Equation2830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ u
def Equation2835 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ u
def Equation2840 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ u
def Equation2841 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ x
def Equation2842 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ y
def Equation2843 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ z
def Equation2844 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ w
def Equation2845 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ u
def Equation2892 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ z
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2929 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ z
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2966 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ z
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2983 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ z
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3000 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ z
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3009 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ z
def Equation3013 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ z
def Equation3015 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ x
def Equation3016 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ y
def Equation3017 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ z
def Equation3023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ u
def Equation3028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ u
def Equation3033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ u
def Equation3038 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ u
def Equation3043 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ u
def Equation3044 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ x
def Equation3045 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ y
def Equation3046 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ z
def Equation3047 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ w
def Equation3048 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ u
def Equation3095 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ z
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3132 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ z
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3169 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ z
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3186 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ z
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3203 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ z
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3212 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ z
def Equation3216 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ z
def Equation3218 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ x
def Equation3219 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ y
def Equation3220 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ z
def Equation3226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ u
def Equation3231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ u
def Equation3236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ u
def Equation3241 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ u
def Equation3246 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ u
def Equation3247 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ x
def Equation3248 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ y
def Equation3249 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ z
def Equation3250 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ w
def Equation3251 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ u
def Equation3298 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ z))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3335 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ z))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3372 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ z))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3389 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ z))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3406 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ z))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3415 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ z))
def Equation3419 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ z))
def Equation3421 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ x))
def Equation3422 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ y))
def Equation3423 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ z))
def Equation3429 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (z ∘ (w ∘ u))
def Equation3434 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (x ∘ u))
def Equation3439 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (y ∘ u))
def Equation3444 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (z ∘ u))
def Equation3449 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (w ∘ u))
def Equation3450 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ x))
def Equation3451 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ y))
def Equation3452 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ z))
def Equation3453 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ w))
def Equation3454 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ u))
def Equation3501 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ z)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3538 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ z)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3575 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ z)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3592 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ z)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3609 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ z)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3618 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ z)
def Equation3622 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ z)
def Equation3624 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ x)
def Equation3625 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ y)
def Equation3626 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ z)
def Equation3632 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((z ∘ w) ∘ u)
def Equation3637 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ x) ∘ u)
def Equation3642 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ y) ∘ u)
def Equation3647 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ z) ∘ u)
def Equation3652 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ w) ∘ u)
def Equation3653 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ x)
def Equation3654 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ y)
def Equation3655 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ z)
def Equation3656 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ w)
def Equation3657 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ u)
def Equation3704 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ z)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3741 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ z)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3778 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ z)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3795 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ z)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3812 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ z)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3821 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ z)
def Equation3825 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ z)
def Equation3827 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ x)
def Equation3828 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ y)
def Equation3829 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ z)
def Equation3835 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ z) ∘ (w ∘ u)
def Equation3840 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (x ∘ u)
def Equation3845 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (y ∘ u)
def Equation3850 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (z ∘ u)
def Equation3855 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (w ∘ u)
def Equation3856 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ x)
def Equation3857 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ y)
def Equation3858 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ z)
def Equation3859 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ w)
def Equation3860 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ u)
def Equation3907 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ z
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3944 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ z
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3981 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ z
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation3998 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ z
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4015 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ z
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4024 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ z
def Equation4028 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ z
def Equation4030 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ x
def Equation4031 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ y
def Equation4032 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ z
def Equation4038 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (z ∘ w)) ∘ u
def Equation4043 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ x)) ∘ u
def Equation4048 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ y)) ∘ u
def Equation4053 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ z)) ∘ u
def Equation4058 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ w)) ∘ u
def Equation4059 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ x
def Equation4060 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ y
def Equation4061 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ z
def Equation4062 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ w
def Equation4063 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ u
def Equation4110 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ z
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4147 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ z
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4184 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ z
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4201 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ z
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4218 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ z
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4227 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ z
def Equation4231 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ z
def Equation4233 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ x
def Equation4234 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ y
def Equation4235 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ z
def Equation4241 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ z) ∘ w) ∘ u
def Equation4246 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ x) ∘ u
def Equation4251 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ y) ∘ u
def Equation4256 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ z) ∘ u
def Equation4261 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ w) ∘ u
def Equation4262 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ x
def Equation4263 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ y
def Equation4264 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ z
def Equation4265 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ w
def Equation4266 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ u
def Equation4425 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ z
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4462 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ z
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ z
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4516 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ z
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4533 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ z
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4542 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ z
def Equation4546 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ z
def Equation4548 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ x
def Equation4549 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ y
def Equation4550 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ z
def Equation4556 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (z ∘ w) ∘ u
def Equation4561 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ x) ∘ u
def Equation4566 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ y) ∘ u
def Equation4571 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ z) ∘ u
def Equation4576 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ w) ∘ u
def Equation4577 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ x
def Equation4578 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ y
def Equation4579 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ z
def Equation4580 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ w
def Equation4581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ u
theorem Equation98_implies_Equation92 (G : Type*) [Magma G] (h : Equation98 G) : Equation92 G := λ x y z => h x y z z z
theorem Equation150_implies_Equation144 (G : Type*) [Magma G] (h : Equation150 G) : Equation144 G := λ x y z => h x y z z z
theorem Equation202_implies_Equation196 (G : Type*) [Magma G] (h : Equation202 G) : Equation196 G := λ x y z => h x y z z z
theorem Equation254_implies_Equation248 (G : Type*) [Magma G] (h : Equation254 G) : Equation248 G := λ x y z => h x y z z z
theorem Equation306_implies_Equation300 (G : Type*) [Magma G] (h : Equation306 G) : Equation300 G := λ x y z => h x y z z z
theorem Equation358_implies_Equation352 (G : Type*) [Magma G] (h : Equation358 G) : Equation352 G := λ x y z => h x y z z z
theorem Equation410_implies_Equation404 (G : Type*) [Magma G] (h : Equation410 G) : Equation404 G := λ x y z => h x y z z z
theorem Equation462_implies_Equation456 (G : Type*) [Magma G] (h : Equation462 G) : Equation456 G := λ x y z => h x y z z z
theorem Equation499_implies_Equation493 (G : Type*) [Magma G] (h : Equation499 G) : Equation493 G := λ x y z => h x y z z z
theorem Equation536_implies_Equation530 (G : Type*) [Magma G] (h : Equation536 G) : Equation530 G := λ x y z => h x y z z z
theorem Equation553_implies_Equation547 (G : Type*) [Magma G] (h : Equation553 G) : Equation547 G := λ x y z => h x y z z z
theorem Equation570_implies_Equation564 (G : Type*) [Magma G] (h : Equation570 G) : Equation564 G := λ x y z => h x y z z z
theorem Equation587_implies_Equation581 (G : Type*) [Magma G] (h : Equation587 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation592_implies_Equation573 (G : Type*) [Magma G] (h : Equation592 G) : Equation573 G := λ x y z => h x y z z z
theorem Equation597_implies_Equation577 (G : Type*) [Magma G] (h : Equation597 G) : Equation577 G := λ x y z => h x y z z z
theorem Equation602_implies_Equation581 (G : Type*) [Magma G] (h : Equation602 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation607_implies_Equation581 (G : Type*) [Magma G] (h : Equation607 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation608_implies_Equation579 (G : Type*) [Magma G] (h : Equation608 G) : Equation579 G := λ x y z => h x y z z z
theorem Equation609_implies_Equation580 (G : Type*) [Magma G] (h : Equation609 G) : Equation580 G := λ x y z => h x y z z z
theorem Equation610_implies_Equation581 (G : Type*) [Magma G] (h : Equation610 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation611_implies_Equation581 (G : Type*) [Magma G] (h : Equation611 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation612_implies_Equation581 (G : Type*) [Magma G] (h : Equation612 G) : Equation581 G := λ x y z => h x y z z z
theorem Equation665_implies_Equation659 (G : Type*) [Magma G] (h : Equation665 G) : Equation659 G := λ x y z => h x y z z z
theorem Equation702_implies_Equation696 (G : Type*) [Magma G] (h : Equation702 G) : Equation696 G := λ x y z => h x y z z z
theorem Equation739_implies_Equation733 (G : Type*) [Magma G] (h : Equation739 G) : Equation733 G := λ x y z => h x y z z z
theorem Equation756_implies_Equation750 (G : Type*) [Magma G] (h : Equation756 G) : Equation750 G := λ x y z => h x y z z z
theorem Equation773_implies_Equation767 (G : Type*) [Magma G] (h : Equation773 G) : Equation767 G := λ x y z => h x y z z z
theorem Equation790_implies_Equation784 (G : Type*) [Magma G] (h : Equation790 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation795_implies_Equation776 (G : Type*) [Magma G] (h : Equation795 G) : Equation776 G := λ x y z => h x y z z z
theorem Equation800_implies_Equation780 (G : Type*) [Magma G] (h : Equation800 G) : Equation780 G := λ x y z => h x y z z z
theorem Equation805_implies_Equation784 (G : Type*) [Magma G] (h : Equation805 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation810_implies_Equation784 (G : Type*) [Magma G] (h : Equation810 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation811_implies_Equation782 (G : Type*) [Magma G] (h : Equation811 G) : Equation782 G := λ x y z => h x y z z z
theorem Equation812_implies_Equation783 (G : Type*) [Magma G] (h : Equation812 G) : Equation783 G := λ x y z => h x y z z z
theorem Equation813_implies_Equation784 (G : Type*) [Magma G] (h : Equation813 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation814_implies_Equation784 (G : Type*) [Magma G] (h : Equation814 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation815_implies_Equation784 (G : Type*) [Magma G] (h : Equation815 G) : Equation784 G := λ x y z => h x y z z z
theorem Equation868_implies_Equation862 (G : Type*) [Magma G] (h : Equation868 G) : Equation862 G := λ x y z => h x y z z z
theorem Equation905_implies_Equation899 (G : Type*) [Magma G] (h : Equation905 G) : Equation899 G := λ x y z => h x y z z z
theorem Equation942_implies_Equation936 (G : Type*) [Magma G] (h : Equation942 G) : Equation936 G := λ x y z => h x y z z z
theorem Equation959_implies_Equation953 (G : Type*) [Magma G] (h : Equation959 G) : Equation953 G := λ x y z => h x y z z z
theorem Equation976_implies_Equation970 (G : Type*) [Magma G] (h : Equation976 G) : Equation970 G := λ x y z => h x y z z z
theorem Equation993_implies_Equation987 (G : Type*) [Magma G] (h : Equation993 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation998_implies_Equation979 (G : Type*) [Magma G] (h : Equation998 G) : Equation979 G := λ x y z => h x y z z z
theorem Equation1003_implies_Equation983 (G : Type*) [Magma G] (h : Equation1003 G) : Equation983 G := λ x y z => h x y z z z
theorem Equation1008_implies_Equation987 (G : Type*) [Magma G] (h : Equation1008 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation1013_implies_Equation987 (G : Type*) [Magma G] (h : Equation1013 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation1014_implies_Equation985 (G : Type*) [Magma G] (h : Equation1014 G) : Equation985 G := λ x y z => h x y z z z
theorem Equation1015_implies_Equation986 (G : Type*) [Magma G] (h : Equation1015 G) : Equation986 G := λ x y z => h x y z z z
theorem Equation1016_implies_Equation987 (G : Type*) [Magma G] (h : Equation1016 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation1017_implies_Equation987 (G : Type*) [Magma G] (h : Equation1017 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation1018_implies_Equation987 (G : Type*) [Magma G] (h : Equation1018 G) : Equation987 G := λ x y z => h x y z z z
theorem Equation1071_implies_Equation1065 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1065 G := λ x y z => h x y z z z
theorem Equation1108_implies_Equation1102 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1102 G := λ x y z => h x y z z z
theorem Equation1145_implies_Equation1139 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1139 G := λ x y z => h x y z z z
theorem Equation1162_implies_Equation1156 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1156 G := λ x y z => h x y z z z
theorem Equation1179_implies_Equation1173 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1173 G := λ x y z => h x y z z z
theorem Equation1196_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1201_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1182 G := λ x y z => h x y z z z
theorem Equation1206_implies_Equation1186 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1186 G := λ x y z => h x y z z z
theorem Equation1211_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1216_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1217_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1188 G := λ x y z => h x y z z z
theorem Equation1218_implies_Equation1189 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1189 G := λ x y z => h x y z z z
theorem Equation1219_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1220_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1221_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1190 G := λ x y z => h x y z z z
theorem Equation1274_implies_Equation1268 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1268 G := λ x y z => h x y z z z
theorem Equation1311_implies_Equation1305 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1305 G := λ x y z => h x y z z z
theorem Equation1348_implies_Equation1342 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1342 G := λ x y z => h x y z z z
theorem Equation1365_implies_Equation1359 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1359 G := λ x y z => h x y z z z
theorem Equation1382_implies_Equation1376 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1376 G := λ x y z => h x y z z z
theorem Equation1399_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1404_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1385 G := λ x y z => h x y z z z
theorem Equation1409_implies_Equation1389 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1389 G := λ x y z => h x y z z z
theorem Equation1414_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1419_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1420_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1391 G := λ x y z => h x y z z z
theorem Equation1421_implies_Equation1392 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1392 G := λ x y z => h x y z z z
theorem Equation1422_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1423_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1424_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1393 G := λ x y z => h x y z z z
theorem Equation1477_implies_Equation1471 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1471 G := λ x y z => h x y z z z
theorem Equation1514_implies_Equation1508 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1508 G := λ x y z => h x y z z z
theorem Equation1551_implies_Equation1545 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1545 G := λ x y z => h x y z z z
theorem Equation1568_implies_Equation1562 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1562 G := λ x y z => h x y z z z
theorem Equation1585_implies_Equation1579 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1579 G := λ x y z => h x y z z z
theorem Equation1602_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1607_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1588 G := λ x y z => h x y z z z
theorem Equation1612_implies_Equation1592 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1592 G := λ x y z => h x y z z z
theorem Equation1617_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1622_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1623_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1594 G := λ x y z => h x y z z z
theorem Equation1624_implies_Equation1595 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1595 G := λ x y z => h x y z z z
theorem Equation1625_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1626_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1627_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1596 G := λ x y z => h x y z z z
theorem Equation1680_implies_Equation1674 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1674 G := λ x y z => h x y z z z
theorem Equation1717_implies_Equation1711 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1711 G := λ x y z => h x y z z z
theorem Equation1754_implies_Equation1748 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1748 G := λ x y z => h x y z z z
theorem Equation1771_implies_Equation1765 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1765 G := λ x y z => h x y z z z
theorem Equation1788_implies_Equation1782 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1782 G := λ x y z => h x y z z z
theorem Equation1805_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1810_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1791 G := λ x y z => h x y z z z
theorem Equation1815_implies_Equation1795 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1795 G := λ x y z => h x y z z z
theorem Equation1820_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1825_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1826_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1797 G := λ x y z => h x y z z z
theorem Equation1827_implies_Equation1798 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1798 G := λ x y z => h x y z z z
theorem Equation1828_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1829_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1830_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1799 G := λ x y z => h x y z z z
theorem Equation1883_implies_Equation1877 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1877 G := λ x y z => h x y z z z
theorem Equation1920_implies_Equation1914 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1914 G := λ x y z => h x y z z z
theorem Equation1957_implies_Equation1951 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1951 G := λ x y z => h x y z z z
theorem Equation1974_implies_Equation1968 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1968 G := λ x y z => h x y z z z
theorem Equation1991_implies_Equation1985 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1985 G := λ x y z => h x y z z z
theorem Equation2008_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2008 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2013_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1994 G := λ x y z => h x y z z z
theorem Equation2018_implies_Equation1998 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1998 G := λ x y z => h x y z z z
theorem Equation2023_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2023 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2028_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2028 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2029_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2029 G) : Equation2000 G := λ x y z => h x y z z z
theorem Equation2030_implies_Equation2001 (G : Type*) [Magma G] (h : Equation2030 G) : Equation2001 G := λ x y z => h x y z z z
theorem Equation2031_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2031 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2032_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2032 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2033_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2033 G) : Equation2002 G := λ x y z => h x y z z z
theorem Equation2086_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2080 G := λ x y z => h x y z z z
theorem Equation2123_implies_Equation2117 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2117 G := λ x y z => h x y z z z
theorem Equation2160_implies_Equation2154 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2154 G := λ x y z => h x y z z z
theorem Equation2177_implies_Equation2171 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2171 G := λ x y z => h x y z z z
theorem Equation2194_implies_Equation2188 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2188 G := λ x y z => h x y z z z
theorem Equation2211_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2216_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2197 G := λ x y z => h x y z z z
theorem Equation2221_implies_Equation2201 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2201 G := λ x y z => h x y z z z
theorem Equation2226_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2231_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2232_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2203 G := λ x y z => h x y z z z
theorem Equation2233_implies_Equation2204 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2204 G := λ x y z => h x y z z z
theorem Equation2234_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2235_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2236_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2205 G := λ x y z => h x y z z z
theorem Equation2289_implies_Equation2283 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2283 G := λ x y z => h x y z z z
theorem Equation2326_implies_Equation2320 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2320 G := λ x y z => h x y z z z
theorem Equation2363_implies_Equation2357 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2357 G := λ x y z => h x y z z z
theorem Equation2380_implies_Equation2374 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2374 G := λ x y z => h x y z z z
theorem Equation2397_implies_Equation2391 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2391 G := λ x y z => h x y z z z
theorem Equation2414_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2419_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2400 G := λ x y z => h x y z z z
theorem Equation2424_implies_Equation2404 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2404 G := λ x y z => h x y z z z
theorem Equation2429_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2434_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2435_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2406 G := λ x y z => h x y z z z
theorem Equation2436_implies_Equation2407 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2407 G := λ x y z => h x y z z z
theorem Equation2437_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2438_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2439_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2408 G := λ x y z => h x y z z z
theorem Equation2492_implies_Equation2486 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2486 G := λ x y z => h x y z z z
theorem Equation2529_implies_Equation2523 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2523 G := λ x y z => h x y z z z
theorem Equation2566_implies_Equation2560 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2560 G := λ x y z => h x y z z z
theorem Equation2583_implies_Equation2577 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2577 G := λ x y z => h x y z z z
theorem Equation2600_implies_Equation2594 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2594 G := λ x y z => h x y z z z
theorem Equation2617_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2622_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2603 G := λ x y z => h x y z z z
theorem Equation2627_implies_Equation2607 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2607 G := λ x y z => h x y z z z
theorem Equation2632_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2637_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2638_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2609 G := λ x y z => h x y z z z
theorem Equation2639_implies_Equation2610 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2610 G := λ x y z => h x y z z z
theorem Equation2640_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2641_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2642_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2611 G := λ x y z => h x y z z z
theorem Equation2695_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2689 G := λ x y z => h x y z z z
theorem Equation2732_implies_Equation2726 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2726 G := λ x y z => h x y z z z
theorem Equation2769_implies_Equation2763 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2763 G := λ x y z => h x y z z z
theorem Equation2786_implies_Equation2780 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2780 G := λ x y z => h x y z z z
theorem Equation2803_implies_Equation2797 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2797 G := λ x y z => h x y z z z
theorem Equation2820_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2825_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2806 G := λ x y z => h x y z z z
theorem Equation2830_implies_Equation2810 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2810 G := λ x y z => h x y z z z
theorem Equation2835_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2840_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2841_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2812 G := λ x y z => h x y z z z
theorem Equation2842_implies_Equation2813 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2813 G := λ x y z => h x y z z z
theorem Equation2843_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2844_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2845_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2814 G := λ x y z => h x y z z z
theorem Equation2898_implies_Equation2892 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2892 G := λ x y z => h x y z z z
theorem Equation2935_implies_Equation2929 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2929 G := λ x y z => h x y z z z
theorem Equation2972_implies_Equation2966 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2966 G := λ x y z => h x y z z z
theorem Equation2989_implies_Equation2983 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2983 G := λ x y z => h x y z z z
theorem Equation3006_implies_Equation3000 (G : Type*) [Magma G] (h : Equation3006 G) : Equation3000 G := λ x y z => h x y z z z
theorem Equation3023_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3028_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3028 G) : Equation3009 G := λ x y z => h x y z z z
theorem Equation3033_implies_Equation3013 (G : Type*) [Magma G] (h : Equation3033 G) : Equation3013 G := λ x y z => h x y z z z
theorem Equation3038_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3043_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3043 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3044_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3015 G := λ x y z => h x y z z z
theorem Equation3045_implies_Equation3016 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3016 G := λ x y z => h x y z z z
theorem Equation3046_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3047_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3048_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3017 G := λ x y z => h x y z z z
theorem Equation3101_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3095 G := λ x y z => h x y z z z
theorem Equation3138_implies_Equation3132 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3132 G := λ x y z => h x y z z z
theorem Equation3175_implies_Equation3169 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3169 G := λ x y z => h x y z z z
theorem Equation3192_implies_Equation3186 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3186 G := λ x y z => h x y z z z
theorem Equation3209_implies_Equation3203 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3203 G := λ x y z => h x y z z z
theorem Equation3226_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3231_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3212 G := λ x y z => h x y z z z
theorem Equation3236_implies_Equation3216 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3216 G := λ x y z => h x y z z z
theorem Equation3241_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3246_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3247_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3218 G := λ x y z => h x y z z z
theorem Equation3248_implies_Equation3219 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3219 G := λ x y z => h x y z z z
theorem Equation3249_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3250_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3251_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3220 G := λ x y z => h x y z z z
theorem Equation3304_implies_Equation3298 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3298 G := λ x y z => h x y z z z
theorem Equation3341_implies_Equation3335 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3335 G := λ x y z => h x y z z z
theorem Equation3378_implies_Equation3372 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3372 G := λ x y z => h x y z z z
theorem Equation3395_implies_Equation3389 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3389 G := λ x y z => h x y z z z
theorem Equation3412_implies_Equation3406 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3406 G := λ x y z => h x y z z z
theorem Equation3429_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3434_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3415 G := λ x y z => h x y z z z
theorem Equation3439_implies_Equation3419 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3419 G := λ x y z => h x y z z z
theorem Equation3444_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3449_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3450_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3421 G := λ x y z => h x y z z z
theorem Equation3451_implies_Equation3422 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3422 G := λ x y z => h x y z z z
theorem Equation3452_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3453_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3454_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3423 G := λ x y z => h x y z z z
theorem Equation3507_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3501 G := λ x y z => h x y z z z
theorem Equation3544_implies_Equation3538 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3538 G := λ x y z => h x y z z z
theorem Equation3581_implies_Equation3575 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3575 G := λ x y z => h x y z z z
theorem Equation3598_implies_Equation3592 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3592 G := λ x y z => h x y z z z
theorem Equation3615_implies_Equation3609 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3609 G := λ x y z => h x y z z z
theorem Equation3632_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3637_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3618 G := λ x y z => h x y z z z
theorem Equation3642_implies_Equation3622 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3622 G := λ x y z => h x y z z z
theorem Equation3647_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3652_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3653_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3624 G := λ x y z => h x y z z z
theorem Equation3654_implies_Equation3625 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3625 G := λ x y z => h x y z z z
theorem Equation3655_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3656_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3657_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3626 G := λ x y z => h x y z z z
theorem Equation3710_implies_Equation3704 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3704 G := λ x y z => h x y z z z
theorem Equation3747_implies_Equation3741 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3741 G := λ x y z => h x y z z z
theorem Equation3784_implies_Equation3778 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3778 G := λ x y z => h x y z z z
theorem Equation3801_implies_Equation3795 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3795 G := λ x y z => h x y z z z
theorem Equation3818_implies_Equation3812 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3812 G := λ x y z => h x y z z z
theorem Equation3835_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3840_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3821 G := λ x y z => h x y z z z
theorem Equation3845_implies_Equation3825 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3825 G := λ x y z => h x y z z z
theorem Equation3850_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3855_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3856_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3827 G := λ x y z => h x y z z z
theorem Equation3857_implies_Equation3828 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3828 G := λ x y z => h x y z z z
theorem Equation3858_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3859_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3860_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3829 G := λ x y z => h x y z z z
theorem Equation3913_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3907 G := λ x y z => h x y z z z
theorem Equation3950_implies_Equation3944 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3944 G := λ x y z => h x y z z z
theorem Equation3987_implies_Equation3981 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3981 G := λ x y z => h x y z z z
theorem Equation4004_implies_Equation3998 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3998 G := λ x y z => h x y z z z
theorem Equation4021_implies_Equation4015 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4015 G := λ x y z => h x y z z z
theorem Equation4038_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4043_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4024 G := λ x y z => h x y z z z
theorem Equation4048_implies_Equation4028 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4028 G := λ x y z => h x y z z z
theorem Equation4053_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4058_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4059_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4030 G := λ x y z => h x y z z z
theorem Equation4060_implies_Equation4031 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4031 G := λ x y z => h x y z z z
theorem Equation4061_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4062_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4063_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4032 G := λ x y z => h x y z z z
theorem Equation4116_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4110 G := λ x y z => h x y z z z
theorem Equation4153_implies_Equation4147 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4147 G := λ x y z => h x y z z z
theorem Equation4190_implies_Equation4184 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4184 G := λ x y z => h x y z z z
theorem Equation4207_implies_Equation4201 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4201 G := λ x y z => h x y z z z
theorem Equation4224_implies_Equation4218 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4218 G := λ x y z => h x y z z z
theorem Equation4241_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4246_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4227 G := λ x y z => h x y z z z
theorem Equation4251_implies_Equation4231 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4231 G := λ x y z => h x y z z z
theorem Equation4256_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4261_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4262_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4233 G := λ x y z => h x y z z z
theorem Equation4263_implies_Equation4234 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4234 G := λ x y z => h x y z z z
theorem Equation4264_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4265_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4266_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4235 G := λ x y z => h x y z z z
theorem Equation4431_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4425 G := λ x y z => h x y z z z
theorem Equation4468_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4462 G := λ x y z => h x y z z z
theorem Equation4505_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4499 G := λ x y z => h x y z z z
theorem Equation4522_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4516 G := λ x y z => h x y z z z
theorem Equation4539_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4533 G := λ x y z => h x y z z z
theorem Equation4556_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4550 G := λ x y z => h x y z z z
theorem Equation4561_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4542 G := λ x y z => h x y z z z
theorem Equation4566_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4546 G := λ x y z => h x y z z z
theorem Equation4571_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4550 G := λ x y z => h x y z z z
theorem Equation4576_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4550 G := λ x y z => h x y z z z
theorem Equation4577_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4548 G := λ x y z => h x y z z z
theorem Equation4578_implies_Equation4549 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4549 G := λ x y z => h x y z z z
theorem Equation4579_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4550 G := λ x y z => h x y z z z
theorem Equation4580_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4550 G := λ x y z => h x y z z z
theorem Equation4581_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4550 G := λ x y z => h x y z z z