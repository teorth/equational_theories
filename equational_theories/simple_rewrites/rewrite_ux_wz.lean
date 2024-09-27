import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation90 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ x))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation142 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ x)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation194 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ x)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation246 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ x
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation298 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ x
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation350 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ x)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation402 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ x
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation454 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ x)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation491 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ x)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation528 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ x)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation545 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ x)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation562 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ x)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation571 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ x)))
def Equation572 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ y)))
def Equation573 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ z)))
def Equation575 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ x)))
def Equation579 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ x)))
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
def Equation657 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ x))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation694 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ x))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation731 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ x))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation748 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ x))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation765 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ x))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation774 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ x))
def Equation775 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ y))
def Equation776 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ z))
def Equation778 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ x))
def Equation782 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ x))
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
def Equation860 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ x))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation897 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ x))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation934 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ x))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation951 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ x))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation968 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ x))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation977 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ x))
def Equation978 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ y))
def Equation979 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ z))
def Equation981 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ x))
def Equation985 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ x))
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
def Equation1063 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ x)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1100 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ x)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1137 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ x)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1154 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ x)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1171 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ x)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1180 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ x)
def Equation1181 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ y)
def Equation1182 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ z)
def Equation1184 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ x)
def Equation1188 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ x)
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
def Equation1266 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ x)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1303 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ x)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1340 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ x)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1357 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ x)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1374 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ x)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1383 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ x)
def Equation1384 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ y)
def Equation1385 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ z)
def Equation1387 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ x)
def Equation1391 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ x)
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
def Equation1469 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ x))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1506 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ x))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1543 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ x))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ x))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1577 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ x))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1586 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ x))
def Equation1587 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ y))
def Equation1588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ z))
def Equation1590 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ x))
def Equation1594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ x))
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
def Equation1672 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ x)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1709 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ x)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1746 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ x)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1763 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ x)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1780 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ x)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1789 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ x)
def Equation1790 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ y)
def Equation1791 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ z)
def Equation1793 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ x)
def Equation1797 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ x)
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
def Equation1875 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ x)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1912 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ x)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1949 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ x)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1966 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ x)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1983 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ x)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation1992 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ x)
def Equation1993 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ y)
def Equation1994 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ z)
def Equation1996 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ x)
def Equation2000 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ x)
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
def Equation2078 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ x)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2115 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ x)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2152 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ x)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2169 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ x)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2186 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ x)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2195 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ x)
def Equation2196 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ y)
def Equation2197 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ z)
def Equation2199 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ x)
def Equation2203 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ x)
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
def Equation2281 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ x
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2318 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ x
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2355 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ x
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2372 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ x
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2389 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ x
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2398 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ x
def Equation2399 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ y
def Equation2400 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ z
def Equation2402 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ x
def Equation2406 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ x
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
def Equation2484 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ x
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2521 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ x
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2558 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ x
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2575 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ x
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ x
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2601 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ x
def Equation2602 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ y
def Equation2603 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ z
def Equation2605 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ x
def Equation2609 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ x
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
def Equation2687 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ x
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2724 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ x
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2761 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ x
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2778 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ x
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2795 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ x
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2804 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ x
def Equation2805 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ y
def Equation2806 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ z
def Equation2808 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ x
def Equation2812 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ x
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
def Equation2890 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ x
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2927 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ x
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2964 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ x
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2981 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ x
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation2998 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ x
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3007 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ x
def Equation3008 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ y
def Equation3009 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ z
def Equation3011 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ x
def Equation3015 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ x
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
def Equation3093 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ x
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3130 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ x
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3167 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ x
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3184 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ x
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3201 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ x
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3210 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ x
def Equation3211 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ y
def Equation3212 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ z
def Equation3214 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ x
def Equation3218 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ x
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
def Equation3296 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ x))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3333 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ x))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3370 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ x))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3387 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ x))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3404 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ x))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3413 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ x))
def Equation3414 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ y))
def Equation3415 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ z))
def Equation3417 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ x))
def Equation3421 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ x))
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
def Equation3499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ x)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3536 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ x)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3573 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ x)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3590 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ x)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3607 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ x)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3616 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ x)
def Equation3617 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ y)
def Equation3618 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ z)
def Equation3620 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ x)
def Equation3624 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ x)
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
def Equation3702 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ x)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3739 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ x)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3776 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ x)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3793 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ x)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3810 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ x)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3819 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ x)
def Equation3820 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ y)
def Equation3821 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ z)
def Equation3823 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ x)
def Equation3827 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ x)
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
def Equation3905 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ x
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3942 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ x
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3979 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ x
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation3996 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ x
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4013 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ x
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4022 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ x
def Equation4023 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ y
def Equation4024 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ z
def Equation4026 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ x
def Equation4030 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ x
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
def Equation4108 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ x
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4145 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ x
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4182 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ x
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4199 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ x
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4216 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ x
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4225 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ x
def Equation4226 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ y
def Equation4227 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ z
def Equation4229 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ x
def Equation4233 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ x
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
def Equation4364 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (z ∘ x)
def Equation4368 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = y ∘ (w ∘ u)
def Equation4369 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = z ∘ (y ∘ x)
def Equation4375 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (y ∘ u)
def Equation4423 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ x
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4460 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ x
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4497 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ x
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4514 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ x
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4531 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ x
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4540 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ x
def Equation4541 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ y
def Equation4542 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ z
def Equation4544 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ x
def Equation4548 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ x
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
def Equation4679 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ z) ∘ x
def Equation4683 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (y ∘ w) ∘ u
def Equation4684 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (z ∘ y) ∘ x
def Equation4690 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ y) ∘ u
theorem Equation98_implies_Equation90 (G : Type*) [Magma G] (h : Equation98 G) : Equation90 G := λ x y z => h x y z z x
theorem Equation150_implies_Equation142 (G : Type*) [Magma G] (h : Equation150 G) : Equation142 G := λ x y z => h x y z z x
theorem Equation202_implies_Equation194 (G : Type*) [Magma G] (h : Equation202 G) : Equation194 G := λ x y z => h x y z z x
theorem Equation254_implies_Equation246 (G : Type*) [Magma G] (h : Equation254 G) : Equation246 G := λ x y z => h x y z z x
theorem Equation306_implies_Equation298 (G : Type*) [Magma G] (h : Equation306 G) : Equation298 G := λ x y z => h x y z z x
theorem Equation358_implies_Equation350 (G : Type*) [Magma G] (h : Equation358 G) : Equation350 G := λ x y z => h x y z z x
theorem Equation410_implies_Equation402 (G : Type*) [Magma G] (h : Equation410 G) : Equation402 G := λ x y z => h x y z z x
theorem Equation462_implies_Equation454 (G : Type*) [Magma G] (h : Equation462 G) : Equation454 G := λ x y z => h x y z z x
theorem Equation499_implies_Equation491 (G : Type*) [Magma G] (h : Equation499 G) : Equation491 G := λ x y z => h x y z z x
theorem Equation536_implies_Equation528 (G : Type*) [Magma G] (h : Equation536 G) : Equation528 G := λ x y z => h x y z z x
theorem Equation553_implies_Equation545 (G : Type*) [Magma G] (h : Equation553 G) : Equation545 G := λ x y z => h x y z z x
theorem Equation570_implies_Equation562 (G : Type*) [Magma G] (h : Equation570 G) : Equation562 G := λ x y z => h x y z z x
theorem Equation587_implies_Equation579 (G : Type*) [Magma G] (h : Equation587 G) : Equation579 G := λ x y z => h x y z z x
theorem Equation592_implies_Equation571 (G : Type*) [Magma G] (h : Equation592 G) : Equation571 G := λ x y z => h x y z z x
theorem Equation597_implies_Equation575 (G : Type*) [Magma G] (h : Equation597 G) : Equation575 G := λ x y z => h x y z z x
theorem Equation602_implies_Equation579 (G : Type*) [Magma G] (h : Equation602 G) : Equation579 G := λ x y z => h x y z z x
theorem Equation607_implies_Equation579 (G : Type*) [Magma G] (h : Equation607 G) : Equation579 G := λ x y z => h x y z z x
theorem Equation608_implies_Equation571 (G : Type*) [Magma G] (h : Equation608 G) : Equation571 G := λ x y z => h x y z z x
theorem Equation609_implies_Equation572 (G : Type*) [Magma G] (h : Equation609 G) : Equation572 G := λ x y z => h x y z z x
theorem Equation610_implies_Equation573 (G : Type*) [Magma G] (h : Equation610 G) : Equation573 G := λ x y z => h x y z z x
theorem Equation611_implies_Equation573 (G : Type*) [Magma G] (h : Equation611 G) : Equation573 G := λ x y z => h x y z z x
theorem Equation612_implies_Equation571 (G : Type*) [Magma G] (h : Equation612 G) : Equation571 G := λ x y z => h x y z z x
theorem Equation665_implies_Equation657 (G : Type*) [Magma G] (h : Equation665 G) : Equation657 G := λ x y z => h x y z z x
theorem Equation702_implies_Equation694 (G : Type*) [Magma G] (h : Equation702 G) : Equation694 G := λ x y z => h x y z z x
theorem Equation739_implies_Equation731 (G : Type*) [Magma G] (h : Equation739 G) : Equation731 G := λ x y z => h x y z z x
theorem Equation756_implies_Equation748 (G : Type*) [Magma G] (h : Equation756 G) : Equation748 G := λ x y z => h x y z z x
theorem Equation773_implies_Equation765 (G : Type*) [Magma G] (h : Equation773 G) : Equation765 G := λ x y z => h x y z z x
theorem Equation790_implies_Equation782 (G : Type*) [Magma G] (h : Equation790 G) : Equation782 G := λ x y z => h x y z z x
theorem Equation795_implies_Equation774 (G : Type*) [Magma G] (h : Equation795 G) : Equation774 G := λ x y z => h x y z z x
theorem Equation800_implies_Equation778 (G : Type*) [Magma G] (h : Equation800 G) : Equation778 G := λ x y z => h x y z z x
theorem Equation805_implies_Equation782 (G : Type*) [Magma G] (h : Equation805 G) : Equation782 G := λ x y z => h x y z z x
theorem Equation810_implies_Equation782 (G : Type*) [Magma G] (h : Equation810 G) : Equation782 G := λ x y z => h x y z z x
theorem Equation811_implies_Equation774 (G : Type*) [Magma G] (h : Equation811 G) : Equation774 G := λ x y z => h x y z z x
theorem Equation812_implies_Equation775 (G : Type*) [Magma G] (h : Equation812 G) : Equation775 G := λ x y z => h x y z z x
theorem Equation813_implies_Equation776 (G : Type*) [Magma G] (h : Equation813 G) : Equation776 G := λ x y z => h x y z z x
theorem Equation814_implies_Equation776 (G : Type*) [Magma G] (h : Equation814 G) : Equation776 G := λ x y z => h x y z z x
theorem Equation815_implies_Equation774 (G : Type*) [Magma G] (h : Equation815 G) : Equation774 G := λ x y z => h x y z z x
theorem Equation868_implies_Equation860 (G : Type*) [Magma G] (h : Equation868 G) : Equation860 G := λ x y z => h x y z z x
theorem Equation905_implies_Equation897 (G : Type*) [Magma G] (h : Equation905 G) : Equation897 G := λ x y z => h x y z z x
theorem Equation942_implies_Equation934 (G : Type*) [Magma G] (h : Equation942 G) : Equation934 G := λ x y z => h x y z z x
theorem Equation959_implies_Equation951 (G : Type*) [Magma G] (h : Equation959 G) : Equation951 G := λ x y z => h x y z z x
theorem Equation976_implies_Equation968 (G : Type*) [Magma G] (h : Equation976 G) : Equation968 G := λ x y z => h x y z z x
theorem Equation993_implies_Equation985 (G : Type*) [Magma G] (h : Equation993 G) : Equation985 G := λ x y z => h x y z z x
theorem Equation998_implies_Equation977 (G : Type*) [Magma G] (h : Equation998 G) : Equation977 G := λ x y z => h x y z z x
theorem Equation1003_implies_Equation981 (G : Type*) [Magma G] (h : Equation1003 G) : Equation981 G := λ x y z => h x y z z x
theorem Equation1008_implies_Equation985 (G : Type*) [Magma G] (h : Equation1008 G) : Equation985 G := λ x y z => h x y z z x
theorem Equation1013_implies_Equation985 (G : Type*) [Magma G] (h : Equation1013 G) : Equation985 G := λ x y z => h x y z z x
theorem Equation1014_implies_Equation977 (G : Type*) [Magma G] (h : Equation1014 G) : Equation977 G := λ x y z => h x y z z x
theorem Equation1015_implies_Equation978 (G : Type*) [Magma G] (h : Equation1015 G) : Equation978 G := λ x y z => h x y z z x
theorem Equation1016_implies_Equation979 (G : Type*) [Magma G] (h : Equation1016 G) : Equation979 G := λ x y z => h x y z z x
theorem Equation1017_implies_Equation979 (G : Type*) [Magma G] (h : Equation1017 G) : Equation979 G := λ x y z => h x y z z x
theorem Equation1018_implies_Equation977 (G : Type*) [Magma G] (h : Equation1018 G) : Equation977 G := λ x y z => h x y z z x
theorem Equation1071_implies_Equation1063 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1063 G := λ x y z => h x y z z x
theorem Equation1108_implies_Equation1100 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1100 G := λ x y z => h x y z z x
theorem Equation1145_implies_Equation1137 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1137 G := λ x y z => h x y z z x
theorem Equation1162_implies_Equation1154 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1154 G := λ x y z => h x y z z x
theorem Equation1179_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1171 G := λ x y z => h x y z z x
theorem Equation1196_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1188 G := λ x y z => h x y z z x
theorem Equation1201_implies_Equation1180 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1180 G := λ x y z => h x y z z x
theorem Equation1206_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1184 G := λ x y z => h x y z z x
theorem Equation1211_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1188 G := λ x y z => h x y z z x
theorem Equation1216_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1188 G := λ x y z => h x y z z x
theorem Equation1217_implies_Equation1180 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1180 G := λ x y z => h x y z z x
theorem Equation1218_implies_Equation1181 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1181 G := λ x y z => h x y z z x
theorem Equation1219_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1182 G := λ x y z => h x y z z x
theorem Equation1220_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1182 G := λ x y z => h x y z z x
theorem Equation1221_implies_Equation1180 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1180 G := λ x y z => h x y z z x
theorem Equation1274_implies_Equation1266 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1266 G := λ x y z => h x y z z x
theorem Equation1311_implies_Equation1303 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1303 G := λ x y z => h x y z z x
theorem Equation1348_implies_Equation1340 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1340 G := λ x y z => h x y z z x
theorem Equation1365_implies_Equation1357 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1357 G := λ x y z => h x y z z x
theorem Equation1382_implies_Equation1374 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1374 G := λ x y z => h x y z z x
theorem Equation1399_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1391 G := λ x y z => h x y z z x
theorem Equation1404_implies_Equation1383 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1383 G := λ x y z => h x y z z x
theorem Equation1409_implies_Equation1387 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1387 G := λ x y z => h x y z z x
theorem Equation1414_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1391 G := λ x y z => h x y z z x
theorem Equation1419_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1391 G := λ x y z => h x y z z x
theorem Equation1420_implies_Equation1383 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1383 G := λ x y z => h x y z z x
theorem Equation1421_implies_Equation1384 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1384 G := λ x y z => h x y z z x
theorem Equation1422_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1385 G := λ x y z => h x y z z x
theorem Equation1423_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1385 G := λ x y z => h x y z z x
theorem Equation1424_implies_Equation1383 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1383 G := λ x y z => h x y z z x
theorem Equation1477_implies_Equation1469 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1469 G := λ x y z => h x y z z x
theorem Equation1514_implies_Equation1506 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1506 G := λ x y z => h x y z z x
theorem Equation1551_implies_Equation1543 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1543 G := λ x y z => h x y z z x
theorem Equation1568_implies_Equation1560 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1560 G := λ x y z => h x y z z x
theorem Equation1585_implies_Equation1577 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1577 G := λ x y z => h x y z z x
theorem Equation1602_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1594 G := λ x y z => h x y z z x
theorem Equation1607_implies_Equation1586 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1586 G := λ x y z => h x y z z x
theorem Equation1612_implies_Equation1590 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1590 G := λ x y z => h x y z z x
theorem Equation1617_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1594 G := λ x y z => h x y z z x
theorem Equation1622_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1594 G := λ x y z => h x y z z x
theorem Equation1623_implies_Equation1586 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1586 G := λ x y z => h x y z z x
theorem Equation1624_implies_Equation1587 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1587 G := λ x y z => h x y z z x
theorem Equation1625_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1588 G := λ x y z => h x y z z x
theorem Equation1626_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1588 G := λ x y z => h x y z z x
theorem Equation1627_implies_Equation1586 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1586 G := λ x y z => h x y z z x
theorem Equation1680_implies_Equation1672 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1672 G := λ x y z => h x y z z x
theorem Equation1717_implies_Equation1709 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1709 G := λ x y z => h x y z z x
theorem Equation1754_implies_Equation1746 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1746 G := λ x y z => h x y z z x
theorem Equation1771_implies_Equation1763 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1763 G := λ x y z => h x y z z x
theorem Equation1788_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1780 G := λ x y z => h x y z z x
theorem Equation1805_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1797 G := λ x y z => h x y z z x
theorem Equation1810_implies_Equation1789 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1789 G := λ x y z => h x y z z x
theorem Equation1815_implies_Equation1793 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1793 G := λ x y z => h x y z z x
theorem Equation1820_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1797 G := λ x y z => h x y z z x
theorem Equation1825_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1797 G := λ x y z => h x y z z x
theorem Equation1826_implies_Equation1789 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1789 G := λ x y z => h x y z z x
theorem Equation1827_implies_Equation1790 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1790 G := λ x y z => h x y z z x
theorem Equation1828_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1791 G := λ x y z => h x y z z x
theorem Equation1829_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1791 G := λ x y z => h x y z z x
theorem Equation1830_implies_Equation1789 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1789 G := λ x y z => h x y z z x
theorem Equation1883_implies_Equation1875 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1875 G := λ x y z => h x y z z x
theorem Equation1920_implies_Equation1912 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1912 G := λ x y z => h x y z z x
theorem Equation1957_implies_Equation1949 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1949 G := λ x y z => h x y z z x
theorem Equation1974_implies_Equation1966 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1966 G := λ x y z => h x y z z x
theorem Equation1991_implies_Equation1983 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1983 G := λ x y z => h x y z z x
theorem Equation2008_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2008 G) : Equation2000 G := λ x y z => h x y z z x
theorem Equation2013_implies_Equation1992 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1992 G := λ x y z => h x y z z x
theorem Equation2018_implies_Equation1996 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1996 G := λ x y z => h x y z z x
theorem Equation2023_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2023 G) : Equation2000 G := λ x y z => h x y z z x
theorem Equation2028_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2028 G) : Equation2000 G := λ x y z => h x y z z x
theorem Equation2029_implies_Equation1992 (G : Type*) [Magma G] (h : Equation2029 G) : Equation1992 G := λ x y z => h x y z z x
theorem Equation2030_implies_Equation1993 (G : Type*) [Magma G] (h : Equation2030 G) : Equation1993 G := λ x y z => h x y z z x
theorem Equation2031_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2031 G) : Equation1994 G := λ x y z => h x y z z x
theorem Equation2032_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2032 G) : Equation1994 G := λ x y z => h x y z z x
theorem Equation2033_implies_Equation1992 (G : Type*) [Magma G] (h : Equation2033 G) : Equation1992 G := λ x y z => h x y z z x
theorem Equation2086_implies_Equation2078 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2078 G := λ x y z => h x y z z x
theorem Equation2123_implies_Equation2115 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2115 G := λ x y z => h x y z z x
theorem Equation2160_implies_Equation2152 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2152 G := λ x y z => h x y z z x
theorem Equation2177_implies_Equation2169 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2169 G := λ x y z => h x y z z x
theorem Equation2194_implies_Equation2186 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2186 G := λ x y z => h x y z z x
theorem Equation2211_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2203 G := λ x y z => h x y z z x
theorem Equation2216_implies_Equation2195 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2195 G := λ x y z => h x y z z x
theorem Equation2221_implies_Equation2199 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2199 G := λ x y z => h x y z z x
theorem Equation2226_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2203 G := λ x y z => h x y z z x
theorem Equation2231_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2203 G := λ x y z => h x y z z x
theorem Equation2232_implies_Equation2195 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2195 G := λ x y z => h x y z z x
theorem Equation2233_implies_Equation2196 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2196 G := λ x y z => h x y z z x
theorem Equation2234_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2197 G := λ x y z => h x y z z x
theorem Equation2235_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2197 G := λ x y z => h x y z z x
theorem Equation2236_implies_Equation2195 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2195 G := λ x y z => h x y z z x
theorem Equation2289_implies_Equation2281 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2281 G := λ x y z => h x y z z x
theorem Equation2326_implies_Equation2318 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2318 G := λ x y z => h x y z z x
theorem Equation2363_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2355 G := λ x y z => h x y z z x
theorem Equation2380_implies_Equation2372 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2372 G := λ x y z => h x y z z x
theorem Equation2397_implies_Equation2389 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2389 G := λ x y z => h x y z z x
theorem Equation2414_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2406 G := λ x y z => h x y z z x
theorem Equation2419_implies_Equation2398 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2398 G := λ x y z => h x y z z x
theorem Equation2424_implies_Equation2402 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2402 G := λ x y z => h x y z z x
theorem Equation2429_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2406 G := λ x y z => h x y z z x
theorem Equation2434_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2406 G := λ x y z => h x y z z x
theorem Equation2435_implies_Equation2398 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2398 G := λ x y z => h x y z z x
theorem Equation2436_implies_Equation2399 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2399 G := λ x y z => h x y z z x
theorem Equation2437_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2400 G := λ x y z => h x y z z x
theorem Equation2438_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2400 G := λ x y z => h x y z z x
theorem Equation2439_implies_Equation2398 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2398 G := λ x y z => h x y z z x
theorem Equation2492_implies_Equation2484 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2484 G := λ x y z => h x y z z x
theorem Equation2529_implies_Equation2521 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2521 G := λ x y z => h x y z z x
theorem Equation2566_implies_Equation2558 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2558 G := λ x y z => h x y z z x
theorem Equation2583_implies_Equation2575 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2575 G := λ x y z => h x y z z x
theorem Equation2600_implies_Equation2592 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2592 G := λ x y z => h x y z z x
theorem Equation2617_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2609 G := λ x y z => h x y z z x
theorem Equation2622_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2601 G := λ x y z => h x y z z x
theorem Equation2627_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2605 G := λ x y z => h x y z z x
theorem Equation2632_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2609 G := λ x y z => h x y z z x
theorem Equation2637_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2609 G := λ x y z => h x y z z x
theorem Equation2638_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2601 G := λ x y z => h x y z z x
theorem Equation2639_implies_Equation2602 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2602 G := λ x y z => h x y z z x
theorem Equation2640_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2603 G := λ x y z => h x y z z x
theorem Equation2641_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2603 G := λ x y z => h x y z z x
theorem Equation2642_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2601 G := λ x y z => h x y z z x
theorem Equation2695_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2687 G := λ x y z => h x y z z x
theorem Equation2732_implies_Equation2724 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2724 G := λ x y z => h x y z z x
theorem Equation2769_implies_Equation2761 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2761 G := λ x y z => h x y z z x
theorem Equation2786_implies_Equation2778 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2778 G := λ x y z => h x y z z x
theorem Equation2803_implies_Equation2795 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2795 G := λ x y z => h x y z z x
theorem Equation2820_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2812 G := λ x y z => h x y z z x
theorem Equation2825_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2804 G := λ x y z => h x y z z x
theorem Equation2830_implies_Equation2808 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2808 G := λ x y z => h x y z z x
theorem Equation2835_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2812 G := λ x y z => h x y z z x
theorem Equation2840_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2812 G := λ x y z => h x y z z x
theorem Equation2841_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2804 G := λ x y z => h x y z z x
theorem Equation2842_implies_Equation2805 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2805 G := λ x y z => h x y z z x
theorem Equation2843_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2806 G := λ x y z => h x y z z x
theorem Equation2844_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2806 G := λ x y z => h x y z z x
theorem Equation2845_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2804 G := λ x y z => h x y z z x
theorem Equation2898_implies_Equation2890 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2890 G := λ x y z => h x y z z x
theorem Equation2935_implies_Equation2927 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2927 G := λ x y z => h x y z z x
theorem Equation2972_implies_Equation2964 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2964 G := λ x y z => h x y z z x
theorem Equation2989_implies_Equation2981 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2981 G := λ x y z => h x y z z x
theorem Equation3006_implies_Equation2998 (G : Type*) [Magma G] (h : Equation3006 G) : Equation2998 G := λ x y z => h x y z z x
theorem Equation3023_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3015 G := λ x y z => h x y z z x
theorem Equation3028_implies_Equation3007 (G : Type*) [Magma G] (h : Equation3028 G) : Equation3007 G := λ x y z => h x y z z x
theorem Equation3033_implies_Equation3011 (G : Type*) [Magma G] (h : Equation3033 G) : Equation3011 G := λ x y z => h x y z z x
theorem Equation3038_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3015 G := λ x y z => h x y z z x
theorem Equation3043_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3043 G) : Equation3015 G := λ x y z => h x y z z x
theorem Equation3044_implies_Equation3007 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3007 G := λ x y z => h x y z z x
theorem Equation3045_implies_Equation3008 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3008 G := λ x y z => h x y z z x
theorem Equation3046_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3009 G := λ x y z => h x y z z x
theorem Equation3047_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3009 G := λ x y z => h x y z z x
theorem Equation3048_implies_Equation3007 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3007 G := λ x y z => h x y z z x
theorem Equation3101_implies_Equation3093 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3093 G := λ x y z => h x y z z x
theorem Equation3138_implies_Equation3130 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3130 G := λ x y z => h x y z z x
theorem Equation3175_implies_Equation3167 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3167 G := λ x y z => h x y z z x
theorem Equation3192_implies_Equation3184 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3184 G := λ x y z => h x y z z x
theorem Equation3209_implies_Equation3201 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3201 G := λ x y z => h x y z z x
theorem Equation3226_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3218 G := λ x y z => h x y z z x
theorem Equation3231_implies_Equation3210 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3210 G := λ x y z => h x y z z x
theorem Equation3236_implies_Equation3214 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3214 G := λ x y z => h x y z z x
theorem Equation3241_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3218 G := λ x y z => h x y z z x
theorem Equation3246_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3218 G := λ x y z => h x y z z x
theorem Equation3247_implies_Equation3210 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3210 G := λ x y z => h x y z z x
theorem Equation3248_implies_Equation3211 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3211 G := λ x y z => h x y z z x
theorem Equation3249_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3212 G := λ x y z => h x y z z x
theorem Equation3250_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3212 G := λ x y z => h x y z z x
theorem Equation3251_implies_Equation3210 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3210 G := λ x y z => h x y z z x
theorem Equation3304_implies_Equation3296 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3296 G := λ x y z => h x y z z x
theorem Equation3341_implies_Equation3333 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3333 G := λ x y z => h x y z z x
theorem Equation3378_implies_Equation3370 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3370 G := λ x y z => h x y z z x
theorem Equation3395_implies_Equation3387 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3387 G := λ x y z => h x y z z x
theorem Equation3412_implies_Equation3404 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3404 G := λ x y z => h x y z z x
theorem Equation3429_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3421 G := λ x y z => h x y z z x
theorem Equation3434_implies_Equation3413 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3413 G := λ x y z => h x y z z x
theorem Equation3439_implies_Equation3417 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3417 G := λ x y z => h x y z z x
theorem Equation3444_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3421 G := λ x y z => h x y z z x
theorem Equation3449_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3421 G := λ x y z => h x y z z x
theorem Equation3450_implies_Equation3413 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3413 G := λ x y z => h x y z z x
theorem Equation3451_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3414 G := λ x y z => h x y z z x
theorem Equation3452_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3415 G := λ x y z => h x y z z x
theorem Equation3453_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3415 G := λ x y z => h x y z z x
theorem Equation3454_implies_Equation3413 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3413 G := λ x y z => h x y z z x
theorem Equation3507_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3499 G := λ x y z => h x y z z x
theorem Equation3544_implies_Equation3536 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3536 G := λ x y z => h x y z z x
theorem Equation3581_implies_Equation3573 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3573 G := λ x y z => h x y z z x
theorem Equation3598_implies_Equation3590 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3590 G := λ x y z => h x y z z x
theorem Equation3615_implies_Equation3607 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3607 G := λ x y z => h x y z z x
theorem Equation3632_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3624 G := λ x y z => h x y z z x
theorem Equation3637_implies_Equation3616 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3616 G := λ x y z => h x y z z x
theorem Equation3642_implies_Equation3620 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3620 G := λ x y z => h x y z z x
theorem Equation3647_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3624 G := λ x y z => h x y z z x
theorem Equation3652_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3624 G := λ x y z => h x y z z x
theorem Equation3653_implies_Equation3616 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3616 G := λ x y z => h x y z z x
theorem Equation3654_implies_Equation3617 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3617 G := λ x y z => h x y z z x
theorem Equation3655_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3618 G := λ x y z => h x y z z x
theorem Equation3656_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3618 G := λ x y z => h x y z z x
theorem Equation3657_implies_Equation3616 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3616 G := λ x y z => h x y z z x
theorem Equation3710_implies_Equation3702 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3702 G := λ x y z => h x y z z x
theorem Equation3747_implies_Equation3739 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3739 G := λ x y z => h x y z z x
theorem Equation3784_implies_Equation3776 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3776 G := λ x y z => h x y z z x
theorem Equation3801_implies_Equation3793 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3793 G := λ x y z => h x y z z x
theorem Equation3818_implies_Equation3810 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3810 G := λ x y z => h x y z z x
theorem Equation3835_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3827 G := λ x y z => h x y z z x
theorem Equation3840_implies_Equation3819 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3819 G := λ x y z => h x y z z x
theorem Equation3845_implies_Equation3823 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3823 G := λ x y z => h x y z z x
theorem Equation3850_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3827 G := λ x y z => h x y z z x
theorem Equation3855_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3827 G := λ x y z => h x y z z x
theorem Equation3856_implies_Equation3819 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3819 G := λ x y z => h x y z z x
theorem Equation3857_implies_Equation3820 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3820 G := λ x y z => h x y z z x
theorem Equation3858_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3821 G := λ x y z => h x y z z x
theorem Equation3859_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3821 G := λ x y z => h x y z z x
theorem Equation3860_implies_Equation3819 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3819 G := λ x y z => h x y z z x
theorem Equation3913_implies_Equation3905 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3905 G := λ x y z => h x y z z x
theorem Equation3950_implies_Equation3942 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3942 G := λ x y z => h x y z z x
theorem Equation3987_implies_Equation3979 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3979 G := λ x y z => h x y z z x
theorem Equation4004_implies_Equation3996 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3996 G := λ x y z => h x y z z x
theorem Equation4021_implies_Equation4013 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4013 G := λ x y z => h x y z z x
theorem Equation4038_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4030 G := λ x y z => h x y z z x
theorem Equation4043_implies_Equation4022 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4022 G := λ x y z => h x y z z x
theorem Equation4048_implies_Equation4026 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4026 G := λ x y z => h x y z z x
theorem Equation4053_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4030 G := λ x y z => h x y z z x
theorem Equation4058_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4030 G := λ x y z => h x y z z x
theorem Equation4059_implies_Equation4022 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4022 G := λ x y z => h x y z z x
theorem Equation4060_implies_Equation4023 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4023 G := λ x y z => h x y z z x
theorem Equation4061_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4024 G := λ x y z => h x y z z x
theorem Equation4062_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4024 G := λ x y z => h x y z z x
theorem Equation4063_implies_Equation4022 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4022 G := λ x y z => h x y z z x
theorem Equation4116_implies_Equation4108 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4108 G := λ x y z => h x y z z x
theorem Equation4153_implies_Equation4145 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4145 G := λ x y z => h x y z z x
theorem Equation4190_implies_Equation4182 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4182 G := λ x y z => h x y z z x
theorem Equation4207_implies_Equation4199 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4199 G := λ x y z => h x y z z x
theorem Equation4224_implies_Equation4216 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4216 G := λ x y z => h x y z z x
theorem Equation4241_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4233 G := λ x y z => h x y z z x
theorem Equation4246_implies_Equation4225 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4225 G := λ x y z => h x y z z x
theorem Equation4251_implies_Equation4229 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4229 G := λ x y z => h x y z z x
theorem Equation4256_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4233 G := λ x y z => h x y z z x
theorem Equation4261_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4233 G := λ x y z => h x y z z x
theorem Equation4262_implies_Equation4225 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4225 G := λ x y z => h x y z z x
theorem Equation4263_implies_Equation4226 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4226 G := λ x y z => h x y z z x
theorem Equation4264_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4227 G := λ x y z => h x y z z x
theorem Equation4265_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4227 G := λ x y z => h x y z z x
theorem Equation4266_implies_Equation4225 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4225 G := λ x y z => h x y z z x
theorem Equation4368_implies_Equation4364 (G : Type*) [Magma G] (h : Equation4368 G) : Equation4364 G := λ x y z => h x y z z x
theorem Equation4375_implies_Equation4369 (G : Type*) [Magma G] (h : Equation4375 G) : Equation4369 G := λ x y z => h x y z z x
theorem Equation4431_implies_Equation4423 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4423 G := λ x y z => h x y z z x
theorem Equation4468_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4460 G := λ x y z => h x y z z x
theorem Equation4505_implies_Equation4497 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4497 G := λ x y z => h x y z z x
theorem Equation4522_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4514 G := λ x y z => h x y z z x
theorem Equation4539_implies_Equation4531 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4531 G := λ x y z => h x y z z x
theorem Equation4556_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4548 G := λ x y z => h x y z z x
theorem Equation4561_implies_Equation4540 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4540 G := λ x y z => h x y z z x
theorem Equation4566_implies_Equation4544 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4544 G := λ x y z => h x y z z x
theorem Equation4571_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4548 G := λ x y z => h x y z z x
theorem Equation4576_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4548 G := λ x y z => h x y z z x
theorem Equation4577_implies_Equation4540 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4540 G := λ x y z => h x y z z x
theorem Equation4578_implies_Equation4541 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4541 G := λ x y z => h x y z z x
theorem Equation4579_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4542 G := λ x y z => h x y z z x
theorem Equation4580_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4542 G := λ x y z => h x y z z x
theorem Equation4581_implies_Equation4540 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4540 G := λ x y z => h x y z z x
theorem Equation4683_implies_Equation4679 (G : Type*) [Magma G] (h : Equation4683 G) : Equation4679 G := λ x y z => h x y z z x
theorem Equation4690_implies_Equation4684 (G : Type*) [Magma G] (h : Equation4690 G) : Equation4684 G := λ x y z => h x y z z x