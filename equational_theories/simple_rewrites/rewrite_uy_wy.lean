import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation87 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ y))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation139 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ y)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation191 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ y)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation243 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ y
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation295 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ y
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation347 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ y)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation399 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ y
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation451 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ y)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation488 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ y)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation525 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ y)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation542 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ y)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation555 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ y)))
def Equation558 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ x)))
def Equation559 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ y)))
def Equation560 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ z)))
def Equation563 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ y)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation576 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ y)))
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
def Equation654 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ y))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation691 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ y))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation728 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ y))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation745 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ y))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation758 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ y))
def Equation761 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ x))
def Equation762 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ y))
def Equation763 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ z))
def Equation766 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ y))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation779 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ y))
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
def Equation857 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ y))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation894 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ y))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation931 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ y))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation948 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ y))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation961 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ y))
def Equation964 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ x))
def Equation965 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ y))
def Equation966 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ z))
def Equation969 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ y))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation982 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ y))
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
def Equation1060 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ y)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1097 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ y)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1134 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ y)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1151 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ y)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1164 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ y)
def Equation1167 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ x)
def Equation1168 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ y)
def Equation1169 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ z)
def Equation1172 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ y)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1185 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ y)
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
def Equation1263 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ y)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1300 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ y)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1337 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ y)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1354 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ y)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1367 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ y)
def Equation1370 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ x)
def Equation1371 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ y)
def Equation1372 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ z)
def Equation1375 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ y)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1388 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ y)
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
def Equation1466 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ y))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1503 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ y))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1540 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ y))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1557 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ y))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1570 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ y))
def Equation1573 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ x))
def Equation1574 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ y))
def Equation1575 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ z))
def Equation1578 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ y))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1591 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ y))
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
def Equation1669 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ y)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1706 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ y)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1743 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ y)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1760 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ y)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1773 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ y)
def Equation1776 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ x)
def Equation1777 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ y)
def Equation1778 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ z)
def Equation1781 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ y)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1794 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ y)
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
def Equation1872 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ y)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1909 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ y)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1946 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ y)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1963 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ y)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1976 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ y)
def Equation1979 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ x)
def Equation1980 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ y)
def Equation1981 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ z)
def Equation1984 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ y)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation1997 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ y)
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
def Equation2075 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ y)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2112 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ y)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2149 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ y)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2166 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ y)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2179 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ y)
def Equation2182 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ x)
def Equation2183 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ y)
def Equation2184 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ z)
def Equation2187 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ y)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2200 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ y)
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
def Equation2278 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ y
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2315 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ y
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2352 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ y
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2369 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ y
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2382 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ y
def Equation2385 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ x
def Equation2386 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ y
def Equation2387 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ z
def Equation2390 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ y
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2403 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ y
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
def Equation2481 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ y
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2518 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ y
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2555 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ y
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2572 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ y
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2585 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ y
def Equation2588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ x
def Equation2589 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ y
def Equation2590 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ z
def Equation2593 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ y
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2606 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ y
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
def Equation2684 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ y
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2721 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ y
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2758 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ y
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2775 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ y
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2788 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ y
def Equation2791 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ x
def Equation2792 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ y
def Equation2793 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ z
def Equation2796 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ y
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2809 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ y
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
def Equation2887 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ y
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2924 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ y
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2961 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ y
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2978 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ y
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation2991 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ y
def Equation2994 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ x
def Equation2995 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ y
def Equation2996 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ z
def Equation2999 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ y
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3012 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ y
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
def Equation3090 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ y
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3127 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ y
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3164 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ y
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3181 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ y
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3194 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ y
def Equation3197 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ x
def Equation3198 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ y
def Equation3199 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ z
def Equation3202 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ y
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3215 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ y
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
def Equation3293 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ y))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3330 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ y))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3367 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ y))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3384 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ y))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3397 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ y))
def Equation3400 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ x))
def Equation3401 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ y))
def Equation3402 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ z))
def Equation3405 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ y))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3418 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ y))
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
def Equation3496 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ y)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3533 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ y)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3570 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ y)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3587 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ y)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3600 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ y)
def Equation3603 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ x)
def Equation3604 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ y)
def Equation3605 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ z)
def Equation3608 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ y)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3621 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ y)
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
def Equation3699 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ y)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3736 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ y)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3773 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ y)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3790 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ y)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3803 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ y)
def Equation3806 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ x)
def Equation3807 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ y)
def Equation3808 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ z)
def Equation3811 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ y)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3824 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ y)
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
def Equation3902 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ y
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3939 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ y
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3976 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ y
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation3993 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ y
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4006 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ y
def Equation4009 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ x
def Equation4010 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ y
def Equation4011 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ z
def Equation4014 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ y
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4027 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ y
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
def Equation4105 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ y
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4142 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ y
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4179 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ y
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4196 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ y
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4209 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ y
def Equation4212 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ x
def Equation4213 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ y
def Equation4214 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ z
def Equation4217 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ y
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4230 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ y
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
def Equation4304 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ y)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4331 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ y)
def Equation4338 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
def Equation4351 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (y ∘ y)
def Equation4356 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
def Equation4420 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ y
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4457 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ y
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4494 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ y
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4511 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ y
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4524 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ y
def Equation4527 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ x
def Equation4528 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ y
def Equation4529 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ z
def Equation4532 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ y
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4545 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ y
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
def Equation4619 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ y
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4646 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ y
def Equation4653 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
def Equation4666 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ y) ∘ y
def Equation4671 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
theorem Equation98_implies_Equation87 (G : Type*) [Magma G] (h : Equation98 G) : Equation87 G := λ x y z => h x y z y y
theorem Equation150_implies_Equation139 (G : Type*) [Magma G] (h : Equation150 G) : Equation139 G := λ x y z => h x y z y y
theorem Equation202_implies_Equation191 (G : Type*) [Magma G] (h : Equation202 G) : Equation191 G := λ x y z => h x y z y y
theorem Equation254_implies_Equation243 (G : Type*) [Magma G] (h : Equation254 G) : Equation243 G := λ x y z => h x y z y y
theorem Equation306_implies_Equation295 (G : Type*) [Magma G] (h : Equation306 G) : Equation295 G := λ x y z => h x y z y y
theorem Equation358_implies_Equation347 (G : Type*) [Magma G] (h : Equation358 G) : Equation347 G := λ x y z => h x y z y y
theorem Equation410_implies_Equation399 (G : Type*) [Magma G] (h : Equation410 G) : Equation399 G := λ x y z => h x y z y y
theorem Equation462_implies_Equation451 (G : Type*) [Magma G] (h : Equation462 G) : Equation451 G := λ x y z => h x y z y y
theorem Equation499_implies_Equation488 (G : Type*) [Magma G] (h : Equation499 G) : Equation488 G := λ x y z => h x y z y y
theorem Equation536_implies_Equation525 (G : Type*) [Magma G] (h : Equation536 G) : Equation525 G := λ x y z => h x y z y y
theorem Equation553_implies_Equation542 (G : Type*) [Magma G] (h : Equation553 G) : Equation542 G := λ x y z => h x y z y y
theorem Equation570_implies_Equation559 (G : Type*) [Magma G] (h : Equation570 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation587_implies_Equation576 (G : Type*) [Magma G] (h : Equation587 G) : Equation576 G := λ x y z => h x y z y y
theorem Equation592_implies_Equation555 (G : Type*) [Magma G] (h : Equation592 G) : Equation555 G := λ x y z => h x y z y y
theorem Equation597_implies_Equation559 (G : Type*) [Magma G] (h : Equation597 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation602_implies_Equation563 (G : Type*) [Magma G] (h : Equation602 G) : Equation563 G := λ x y z => h x y z y y
theorem Equation607_implies_Equation559 (G : Type*) [Magma G] (h : Equation607 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation608_implies_Equation558 (G : Type*) [Magma G] (h : Equation608 G) : Equation558 G := λ x y z => h x y z y y
theorem Equation609_implies_Equation559 (G : Type*) [Magma G] (h : Equation609 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation610_implies_Equation560 (G : Type*) [Magma G] (h : Equation610 G) : Equation560 G := λ x y z => h x y z y y
theorem Equation611_implies_Equation559 (G : Type*) [Magma G] (h : Equation611 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation612_implies_Equation559 (G : Type*) [Magma G] (h : Equation612 G) : Equation559 G := λ x y z => h x y z y y
theorem Equation665_implies_Equation654 (G : Type*) [Magma G] (h : Equation665 G) : Equation654 G := λ x y z => h x y z y y
theorem Equation702_implies_Equation691 (G : Type*) [Magma G] (h : Equation702 G) : Equation691 G := λ x y z => h x y z y y
theorem Equation739_implies_Equation728 (G : Type*) [Magma G] (h : Equation739 G) : Equation728 G := λ x y z => h x y z y y
theorem Equation756_implies_Equation745 (G : Type*) [Magma G] (h : Equation756 G) : Equation745 G := λ x y z => h x y z y y
theorem Equation773_implies_Equation762 (G : Type*) [Magma G] (h : Equation773 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation790_implies_Equation779 (G : Type*) [Magma G] (h : Equation790 G) : Equation779 G := λ x y z => h x y z y y
theorem Equation795_implies_Equation758 (G : Type*) [Magma G] (h : Equation795 G) : Equation758 G := λ x y z => h x y z y y
theorem Equation800_implies_Equation762 (G : Type*) [Magma G] (h : Equation800 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation805_implies_Equation766 (G : Type*) [Magma G] (h : Equation805 G) : Equation766 G := λ x y z => h x y z y y
theorem Equation810_implies_Equation762 (G : Type*) [Magma G] (h : Equation810 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation811_implies_Equation761 (G : Type*) [Magma G] (h : Equation811 G) : Equation761 G := λ x y z => h x y z y y
theorem Equation812_implies_Equation762 (G : Type*) [Magma G] (h : Equation812 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation813_implies_Equation763 (G : Type*) [Magma G] (h : Equation813 G) : Equation763 G := λ x y z => h x y z y y
theorem Equation814_implies_Equation762 (G : Type*) [Magma G] (h : Equation814 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation815_implies_Equation762 (G : Type*) [Magma G] (h : Equation815 G) : Equation762 G := λ x y z => h x y z y y
theorem Equation868_implies_Equation857 (G : Type*) [Magma G] (h : Equation868 G) : Equation857 G := λ x y z => h x y z y y
theorem Equation905_implies_Equation894 (G : Type*) [Magma G] (h : Equation905 G) : Equation894 G := λ x y z => h x y z y y
theorem Equation942_implies_Equation931 (G : Type*) [Magma G] (h : Equation942 G) : Equation931 G := λ x y z => h x y z y y
theorem Equation959_implies_Equation948 (G : Type*) [Magma G] (h : Equation959 G) : Equation948 G := λ x y z => h x y z y y
theorem Equation976_implies_Equation965 (G : Type*) [Magma G] (h : Equation976 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation993_implies_Equation982 (G : Type*) [Magma G] (h : Equation993 G) : Equation982 G := λ x y z => h x y z y y
theorem Equation998_implies_Equation961 (G : Type*) [Magma G] (h : Equation998 G) : Equation961 G := λ x y z => h x y z y y
theorem Equation1003_implies_Equation965 (G : Type*) [Magma G] (h : Equation1003 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation1008_implies_Equation969 (G : Type*) [Magma G] (h : Equation1008 G) : Equation969 G := λ x y z => h x y z y y
theorem Equation1013_implies_Equation965 (G : Type*) [Magma G] (h : Equation1013 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation1014_implies_Equation964 (G : Type*) [Magma G] (h : Equation1014 G) : Equation964 G := λ x y z => h x y z y y
theorem Equation1015_implies_Equation965 (G : Type*) [Magma G] (h : Equation1015 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation1016_implies_Equation966 (G : Type*) [Magma G] (h : Equation1016 G) : Equation966 G := λ x y z => h x y z y y
theorem Equation1017_implies_Equation965 (G : Type*) [Magma G] (h : Equation1017 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation1018_implies_Equation965 (G : Type*) [Magma G] (h : Equation1018 G) : Equation965 G := λ x y z => h x y z y y
theorem Equation1071_implies_Equation1060 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1060 G := λ x y z => h x y z y y
theorem Equation1108_implies_Equation1097 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1097 G := λ x y z => h x y z y y
theorem Equation1145_implies_Equation1134 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1134 G := λ x y z => h x y z y y
theorem Equation1162_implies_Equation1151 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1151 G := λ x y z => h x y z y y
theorem Equation1179_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1196_implies_Equation1185 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1185 G := λ x y z => h x y z y y
theorem Equation1201_implies_Equation1164 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1164 G := λ x y z => h x y z y y
theorem Equation1206_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1211_implies_Equation1172 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1172 G := λ x y z => h x y z y y
theorem Equation1216_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1217_implies_Equation1167 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1167 G := λ x y z => h x y z y y
theorem Equation1218_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1219_implies_Equation1169 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1169 G := λ x y z => h x y z y y
theorem Equation1220_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1221_implies_Equation1168 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1168 G := λ x y z => h x y z y y
theorem Equation1274_implies_Equation1263 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1263 G := λ x y z => h x y z y y
theorem Equation1311_implies_Equation1300 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1300 G := λ x y z => h x y z y y
theorem Equation1348_implies_Equation1337 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1337 G := λ x y z => h x y z y y
theorem Equation1365_implies_Equation1354 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1354 G := λ x y z => h x y z y y
theorem Equation1382_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1399_implies_Equation1388 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1388 G := λ x y z => h x y z y y
theorem Equation1404_implies_Equation1367 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1367 G := λ x y z => h x y z y y
theorem Equation1409_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1414_implies_Equation1375 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1375 G := λ x y z => h x y z y y
theorem Equation1419_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1420_implies_Equation1370 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1370 G := λ x y z => h x y z y y
theorem Equation1421_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1422_implies_Equation1372 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1372 G := λ x y z => h x y z y y
theorem Equation1423_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1424_implies_Equation1371 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1371 G := λ x y z => h x y z y y
theorem Equation1477_implies_Equation1466 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1466 G := λ x y z => h x y z y y
theorem Equation1514_implies_Equation1503 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1503 G := λ x y z => h x y z y y
theorem Equation1551_implies_Equation1540 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1540 G := λ x y z => h x y z y y
theorem Equation1568_implies_Equation1557 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1557 G := λ x y z => h x y z y y
theorem Equation1585_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1602_implies_Equation1591 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1591 G := λ x y z => h x y z y y
theorem Equation1607_implies_Equation1570 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1570 G := λ x y z => h x y z y y
theorem Equation1612_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1617_implies_Equation1578 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1578 G := λ x y z => h x y z y y
theorem Equation1622_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1623_implies_Equation1573 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1573 G := λ x y z => h x y z y y
theorem Equation1624_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1625_implies_Equation1575 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1575 G := λ x y z => h x y z y y
theorem Equation1626_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1627_implies_Equation1574 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1574 G := λ x y z => h x y z y y
theorem Equation1680_implies_Equation1669 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1669 G := λ x y z => h x y z y y
theorem Equation1717_implies_Equation1706 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1706 G := λ x y z => h x y z y y
theorem Equation1754_implies_Equation1743 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1743 G := λ x y z => h x y z y y
theorem Equation1771_implies_Equation1760 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1760 G := λ x y z => h x y z y y
theorem Equation1788_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1805_implies_Equation1794 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1794 G := λ x y z => h x y z y y
theorem Equation1810_implies_Equation1773 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1773 G := λ x y z => h x y z y y
theorem Equation1815_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1820_implies_Equation1781 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1781 G := λ x y z => h x y z y y
theorem Equation1825_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1826_implies_Equation1776 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1776 G := λ x y z => h x y z y y
theorem Equation1827_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1828_implies_Equation1778 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1778 G := λ x y z => h x y z y y
theorem Equation1829_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1830_implies_Equation1777 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1777 G := λ x y z => h x y z y y
theorem Equation1883_implies_Equation1872 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1872 G := λ x y z => h x y z y y
theorem Equation1920_implies_Equation1909 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1909 G := λ x y z => h x y z y y
theorem Equation1957_implies_Equation1946 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1946 G := λ x y z => h x y z y y
theorem Equation1974_implies_Equation1963 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1963 G := λ x y z => h x y z y y
theorem Equation1991_implies_Equation1980 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2008_implies_Equation1997 (G : Type*) [Magma G] (h : Equation2008 G) : Equation1997 G := λ x y z => h x y z y y
theorem Equation2013_implies_Equation1976 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1976 G := λ x y z => h x y z y y
theorem Equation2018_implies_Equation1980 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2023_implies_Equation1984 (G : Type*) [Magma G] (h : Equation2023 G) : Equation1984 G := λ x y z => h x y z y y
theorem Equation2028_implies_Equation1980 (G : Type*) [Magma G] (h : Equation2028 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2029_implies_Equation1979 (G : Type*) [Magma G] (h : Equation2029 G) : Equation1979 G := λ x y z => h x y z y y
theorem Equation2030_implies_Equation1980 (G : Type*) [Magma G] (h : Equation2030 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2031_implies_Equation1981 (G : Type*) [Magma G] (h : Equation2031 G) : Equation1981 G := λ x y z => h x y z y y
theorem Equation2032_implies_Equation1980 (G : Type*) [Magma G] (h : Equation2032 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2033_implies_Equation1980 (G : Type*) [Magma G] (h : Equation2033 G) : Equation1980 G := λ x y z => h x y z y y
theorem Equation2086_implies_Equation2075 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2075 G := λ x y z => h x y z y y
theorem Equation2123_implies_Equation2112 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2112 G := λ x y z => h x y z y y
theorem Equation2160_implies_Equation2149 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2149 G := λ x y z => h x y z y y
theorem Equation2177_implies_Equation2166 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2166 G := λ x y z => h x y z y y
theorem Equation2194_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2211_implies_Equation2200 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2200 G := λ x y z => h x y z y y
theorem Equation2216_implies_Equation2179 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2179 G := λ x y z => h x y z y y
theorem Equation2221_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2226_implies_Equation2187 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2187 G := λ x y z => h x y z y y
theorem Equation2231_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2232_implies_Equation2182 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2182 G := λ x y z => h x y z y y
theorem Equation2233_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2234_implies_Equation2184 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2184 G := λ x y z => h x y z y y
theorem Equation2235_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2236_implies_Equation2183 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2183 G := λ x y z => h x y z y y
theorem Equation2289_implies_Equation2278 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2278 G := λ x y z => h x y z y y
theorem Equation2326_implies_Equation2315 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2315 G := λ x y z => h x y z y y
theorem Equation2363_implies_Equation2352 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2352 G := λ x y z => h x y z y y
theorem Equation2380_implies_Equation2369 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2369 G := λ x y z => h x y z y y
theorem Equation2397_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2414_implies_Equation2403 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2403 G := λ x y z => h x y z y y
theorem Equation2419_implies_Equation2382 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2382 G := λ x y z => h x y z y y
theorem Equation2424_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2429_implies_Equation2390 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2390 G := λ x y z => h x y z y y
theorem Equation2434_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2435_implies_Equation2385 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2385 G := λ x y z => h x y z y y
theorem Equation2436_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2437_implies_Equation2387 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2387 G := λ x y z => h x y z y y
theorem Equation2438_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2439_implies_Equation2386 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2386 G := λ x y z => h x y z y y
theorem Equation2492_implies_Equation2481 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2481 G := λ x y z => h x y z y y
theorem Equation2529_implies_Equation2518 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2518 G := λ x y z => h x y z y y
theorem Equation2566_implies_Equation2555 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2555 G := λ x y z => h x y z y y
theorem Equation2583_implies_Equation2572 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2572 G := λ x y z => h x y z y y
theorem Equation2600_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2617_implies_Equation2606 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2606 G := λ x y z => h x y z y y
theorem Equation2622_implies_Equation2585 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2585 G := λ x y z => h x y z y y
theorem Equation2627_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2632_implies_Equation2593 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2593 G := λ x y z => h x y z y y
theorem Equation2637_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2638_implies_Equation2588 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2588 G := λ x y z => h x y z y y
theorem Equation2639_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2640_implies_Equation2590 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2590 G := λ x y z => h x y z y y
theorem Equation2641_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2642_implies_Equation2589 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2589 G := λ x y z => h x y z y y
theorem Equation2695_implies_Equation2684 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2684 G := λ x y z => h x y z y y
theorem Equation2732_implies_Equation2721 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2721 G := λ x y z => h x y z y y
theorem Equation2769_implies_Equation2758 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2758 G := λ x y z => h x y z y y
theorem Equation2786_implies_Equation2775 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2775 G := λ x y z => h x y z y y
theorem Equation2803_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2820_implies_Equation2809 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2809 G := λ x y z => h x y z y y
theorem Equation2825_implies_Equation2788 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2788 G := λ x y z => h x y z y y
theorem Equation2830_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2835_implies_Equation2796 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2796 G := λ x y z => h x y z y y
theorem Equation2840_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2841_implies_Equation2791 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2791 G := λ x y z => h x y z y y
theorem Equation2842_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2843_implies_Equation2793 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2793 G := λ x y z => h x y z y y
theorem Equation2844_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2845_implies_Equation2792 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2792 G := λ x y z => h x y z y y
theorem Equation2898_implies_Equation2887 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2887 G := λ x y z => h x y z y y
theorem Equation2935_implies_Equation2924 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2924 G := λ x y z => h x y z y y
theorem Equation2972_implies_Equation2961 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2961 G := λ x y z => h x y z y y
theorem Equation2989_implies_Equation2978 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2978 G := λ x y z => h x y z y y
theorem Equation3006_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3006 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3023_implies_Equation3012 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3012 G := λ x y z => h x y z y y
theorem Equation3028_implies_Equation2991 (G : Type*) [Magma G] (h : Equation3028 G) : Equation2991 G := λ x y z => h x y z y y
theorem Equation3033_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3033 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3038_implies_Equation2999 (G : Type*) [Magma G] (h : Equation3038 G) : Equation2999 G := λ x y z => h x y z y y
theorem Equation3043_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3043 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3044_implies_Equation2994 (G : Type*) [Magma G] (h : Equation3044 G) : Equation2994 G := λ x y z => h x y z y y
theorem Equation3045_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3045 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3046_implies_Equation2996 (G : Type*) [Magma G] (h : Equation3046 G) : Equation2996 G := λ x y z => h x y z y y
theorem Equation3047_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3047 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3048_implies_Equation2995 (G : Type*) [Magma G] (h : Equation3048 G) : Equation2995 G := λ x y z => h x y z y y
theorem Equation3101_implies_Equation3090 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3090 G := λ x y z => h x y z y y
theorem Equation3138_implies_Equation3127 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3127 G := λ x y z => h x y z y y
theorem Equation3175_implies_Equation3164 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3164 G := λ x y z => h x y z y y
theorem Equation3192_implies_Equation3181 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3181 G := λ x y z => h x y z y y
theorem Equation3209_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3226_implies_Equation3215 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3215 G := λ x y z => h x y z y y
theorem Equation3231_implies_Equation3194 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3194 G := λ x y z => h x y z y y
theorem Equation3236_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3241_implies_Equation3202 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3202 G := λ x y z => h x y z y y
theorem Equation3246_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3247_implies_Equation3197 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3197 G := λ x y z => h x y z y y
theorem Equation3248_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3249_implies_Equation3199 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3199 G := λ x y z => h x y z y y
theorem Equation3250_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3251_implies_Equation3198 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3198 G := λ x y z => h x y z y y
theorem Equation3304_implies_Equation3293 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3293 G := λ x y z => h x y z y y
theorem Equation3341_implies_Equation3330 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3330 G := λ x y z => h x y z y y
theorem Equation3378_implies_Equation3367 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3367 G := λ x y z => h x y z y y
theorem Equation3395_implies_Equation3384 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3384 G := λ x y z => h x y z y y
theorem Equation3412_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3429_implies_Equation3418 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3418 G := λ x y z => h x y z y y
theorem Equation3434_implies_Equation3397 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3397 G := λ x y z => h x y z y y
theorem Equation3439_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3444_implies_Equation3405 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3405 G := λ x y z => h x y z y y
theorem Equation3449_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3450_implies_Equation3400 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3400 G := λ x y z => h x y z y y
theorem Equation3451_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3452_implies_Equation3402 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3402 G := λ x y z => h x y z y y
theorem Equation3453_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3454_implies_Equation3401 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3401 G := λ x y z => h x y z y y
theorem Equation3507_implies_Equation3496 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3496 G := λ x y z => h x y z y y
theorem Equation3544_implies_Equation3533 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3533 G := λ x y z => h x y z y y
theorem Equation3581_implies_Equation3570 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3570 G := λ x y z => h x y z y y
theorem Equation3598_implies_Equation3587 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3587 G := λ x y z => h x y z y y
theorem Equation3615_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3632_implies_Equation3621 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3621 G := λ x y z => h x y z y y
theorem Equation3637_implies_Equation3600 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3600 G := λ x y z => h x y z y y
theorem Equation3642_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3647_implies_Equation3608 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3608 G := λ x y z => h x y z y y
theorem Equation3652_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3653_implies_Equation3603 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3603 G := λ x y z => h x y z y y
theorem Equation3654_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3655_implies_Equation3605 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3605 G := λ x y z => h x y z y y
theorem Equation3656_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3657_implies_Equation3604 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3604 G := λ x y z => h x y z y y
theorem Equation3710_implies_Equation3699 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3699 G := λ x y z => h x y z y y
theorem Equation3747_implies_Equation3736 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3736 G := λ x y z => h x y z y y
theorem Equation3784_implies_Equation3773 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3773 G := λ x y z => h x y z y y
theorem Equation3801_implies_Equation3790 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3790 G := λ x y z => h x y z y y
theorem Equation3818_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3835_implies_Equation3824 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3824 G := λ x y z => h x y z y y
theorem Equation3840_implies_Equation3803 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3803 G := λ x y z => h x y z y y
theorem Equation3845_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3850_implies_Equation3811 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3811 G := λ x y z => h x y z y y
theorem Equation3855_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3856_implies_Equation3806 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3806 G := λ x y z => h x y z y y
theorem Equation3857_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3858_implies_Equation3808 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3808 G := λ x y z => h x y z y y
theorem Equation3859_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3860_implies_Equation3807 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3807 G := λ x y z => h x y z y y
theorem Equation3913_implies_Equation3902 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3902 G := λ x y z => h x y z y y
theorem Equation3950_implies_Equation3939 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3939 G := λ x y z => h x y z y y
theorem Equation3987_implies_Equation3976 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3976 G := λ x y z => h x y z y y
theorem Equation4004_implies_Equation3993 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3993 G := λ x y z => h x y z y y
theorem Equation4021_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4038_implies_Equation4027 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4027 G := λ x y z => h x y z y y
theorem Equation4043_implies_Equation4006 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4006 G := λ x y z => h x y z y y
theorem Equation4048_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4053_implies_Equation4014 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4014 G := λ x y z => h x y z y y
theorem Equation4058_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4059_implies_Equation4009 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4009 G := λ x y z => h x y z y y
theorem Equation4060_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4061_implies_Equation4011 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4011 G := λ x y z => h x y z y y
theorem Equation4062_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4063_implies_Equation4010 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4010 G := λ x y z => h x y z y y
theorem Equation4116_implies_Equation4105 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4105 G := λ x y z => h x y z y y
theorem Equation4153_implies_Equation4142 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4142 G := λ x y z => h x y z y y
theorem Equation4190_implies_Equation4179 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4179 G := λ x y z => h x y z y y
theorem Equation4207_implies_Equation4196 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4196 G := λ x y z => h x y z y y
theorem Equation4224_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4241_implies_Equation4230 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4230 G := λ x y z => h x y z y y
theorem Equation4246_implies_Equation4209 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4209 G := λ x y z => h x y z y y
theorem Equation4251_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4256_implies_Equation4217 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4217 G := λ x y z => h x y z y y
theorem Equation4261_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4262_implies_Equation4212 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4212 G := λ x y z => h x y z y y
theorem Equation4263_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4264_implies_Equation4214 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4214 G := λ x y z => h x y z y y
theorem Equation4265_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4266_implies_Equation4213 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4213 G := λ x y z => h x y z y y
theorem Equation4313_implies_Equation4304 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4304 G := λ x y z => h x y z y y
theorem Equation4338_implies_Equation4331 (G : Type*) [Magma G] (h : Equation4338 G) : Equation4331 G := λ x y z => h x y z y y
theorem Equation4356_implies_Equation4351 (G : Type*) [Magma G] (h : Equation4356 G) : Equation4351 G := λ x y z => h x y z y y
theorem Equation4431_implies_Equation4420 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4420 G := λ x y z => h x y z y y
theorem Equation4468_implies_Equation4457 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4457 G := λ x y z => h x y z y y
theorem Equation4505_implies_Equation4494 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4494 G := λ x y z => h x y z y y
theorem Equation4522_implies_Equation4511 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4511 G := λ x y z => h x y z y y
theorem Equation4539_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4556_implies_Equation4545 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4545 G := λ x y z => h x y z y y
theorem Equation4561_implies_Equation4524 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4524 G := λ x y z => h x y z y y
theorem Equation4566_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4571_implies_Equation4532 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4532 G := λ x y z => h x y z y y
theorem Equation4576_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4577_implies_Equation4527 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4527 G := λ x y z => h x y z y y
theorem Equation4578_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4579_implies_Equation4529 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4529 G := λ x y z => h x y z y y
theorem Equation4580_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4581_implies_Equation4528 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4528 G := λ x y z => h x y z y y
theorem Equation4628_implies_Equation4619 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4619 G := λ x y z => h x y z y y
theorem Equation4653_implies_Equation4646 (G : Type*) [Magma G] (h : Equation4653 G) : Equation4646 G := λ x y z => h x y z y y
theorem Equation4671_implies_Equation4666 (G : Type*) [Magma G] (h : Equation4671 G) : Equation4666 G := λ x y z => h x y z y y