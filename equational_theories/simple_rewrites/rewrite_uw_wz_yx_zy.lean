import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation61 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ w))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation113 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ w)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation165 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ w)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ w
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation269 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ w
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation321 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ w)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ w
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation425 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation435 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation445 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation449 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation453 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation457 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation458 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation459 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation460 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation461 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
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
def Equation628 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation638 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation648 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation652 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation656 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation660 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation661 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation662 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation663 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation664 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
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
def Equation831 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation841 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation851 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation855 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation859 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation863 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation864 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation865 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation866 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation867 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
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
def Equation1034 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1044 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1054 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1058 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1062 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1066 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1067 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1068 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1069 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1070 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
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
def Equation1237 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1247 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1257 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1261 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1265 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1269 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1270 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1271 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1272 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1273 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
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
def Equation1440 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1450 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1460 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1464 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1468 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1472 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1473 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1474 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1476 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
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
def Equation1643 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1653 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1663 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1667 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1671 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1675 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1676 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1677 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1678 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1679 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
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
def Equation1846 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation1856 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation1866 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation1870 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation1874 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1878 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1879 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation1880 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1881 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation1882 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
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
def Equation2049 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2059 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2069 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2073 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2077 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2081 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2082 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2083 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2084 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2085 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
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
def Equation2252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2262 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2272 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2276 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2280 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2284 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2285 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2286 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2287 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2288 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
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
def Equation2455 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2465 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2479 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2483 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2488 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2489 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2490 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2491 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
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
def Equation2658 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2668 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2678 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2682 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2686 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2690 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2691 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2692 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2693 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2694 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
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
def Equation2861 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ w
def Equation2871 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ w
def Equation2881 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ w
def Equation2885 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ w
def Equation2889 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2893 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2894 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ x
def Equation2895 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2896 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ z
def Equation2897 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
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
def Equation3064 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ w
def Equation3074 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ w
def Equation3084 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ w
def Equation3088 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ w
def Equation3092 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
def Equation3096 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ w
def Equation3097 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ x
def Equation3098 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
def Equation3099 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ z
def Equation3100 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ w
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
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
def Equation3267 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ (y ∘ (z ∘ w))
def Equation3277 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (x ∘ (z ∘ w))
def Equation3287 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (y ∘ (z ∘ w))
def Equation3291 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (x ∘ w))
def Equation3295 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
def Equation3299 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (z ∘ w))
def Equation3300 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ x))
def Equation3301 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
def Equation3302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ z))
def Equation3303 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ w))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
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
def Equation3470 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ ((y ∘ z) ∘ w)
def Equation3480 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((x ∘ z) ∘ w)
def Equation3490 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((y ∘ z) ∘ w)
def Equation3494 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ x) ∘ w)
def Equation3498 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
def Equation3502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ z) ∘ w)
def Equation3503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ x)
def Equation3504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
def Equation3505 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ z)
def Equation3506 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ w)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
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
def Equation3673 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ y) ∘ (z ∘ w)
def Equation3683 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ x) ∘ (z ∘ w)
def Equation3693 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ y) ∘ (z ∘ w)
def Equation3697 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (x ∘ w)
def Equation3701 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
def Equation3705 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (z ∘ w)
def Equation3706 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ x)
def Equation3707 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
def Equation3708 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ z)
def Equation3709 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ w)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
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
def Equation3876 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ (y ∘ z)) ∘ w
def Equation3886 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (x ∘ z)) ∘ w
def Equation3896 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (y ∘ z)) ∘ w
def Equation3900 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ x)) ∘ w
def Equation3904 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
def Equation3908 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ z)) ∘ w
def Equation3909 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ x
def Equation3910 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
def Equation3911 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ z
def Equation3912 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ w
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
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
def Equation4079 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((x ∘ y) ∘ z) ∘ w
def Equation4089 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ x) ∘ z) ∘ w
def Equation4099 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ y) ∘ z) ∘ w
def Equation4103 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ x) ∘ w
def Equation4107 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
def Equation4111 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ z) ∘ w
def Equation4112 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ x
def Equation4113 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
def Equation4114 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ z
def Equation4115 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ w
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
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
def Equation4281 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = y ∘ (z ∘ w)
def Equation4289 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = x ∘ (z ∘ w)
def Equation4298 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = y ∘ (z ∘ w)
def Equation4302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (x ∘ w)
def Equation4306 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
def Equation4310 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4338 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
def Equation4356 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
def Equation4361 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = x ∘ (w ∘ u)
def Equation4368 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = y ∘ (w ∘ u)
def Equation4373 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = z ∘ (w ∘ u)
def Equation4375 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (y ∘ u)
def Equation4377 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (z ∘ u)
def Equation4378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (u ∘ z)
def Equation4394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = (y ∘ z) ∘ w
def Equation4404 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (x ∘ z) ∘ w
def Equation4414 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (y ∘ z) ∘ w
def Equation4418 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ x) ∘ w
def Equation4422 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
def Equation4426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ z) ∘ w
def Equation4427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ x
def Equation4428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
def Equation4429 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ z
def Equation4430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ w
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
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
def Equation4596 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ x = (y ∘ z) ∘ w
def Equation4604 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (x ∘ z) ∘ w
def Equation4613 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (y ∘ z) ∘ w
def Equation4617 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ x) ∘ w
def Equation4621 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
def Equation4625 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4653 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
def Equation4671 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
def Equation4676 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (x ∘ w) ∘ u
def Equation4683 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (y ∘ w) ∘ u
def Equation4688 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (z ∘ w) ∘ u
def Equation4690 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ y) ∘ u
def Equation4692 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ z) ∘ u
def Equation4693 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ u) ∘ z
theorem Equation98_implies_Equation61 (G : Type*) [Magma G] (h : Equation98 G) : Equation61 G := λ x y z w => h x x y z w
theorem Equation150_implies_Equation113 (G : Type*) [Magma G] (h : Equation150 G) : Equation113 G := λ x y z w => h x x y z w
theorem Equation202_implies_Equation165 (G : Type*) [Magma G] (h : Equation202 G) : Equation165 G := λ x y z w => h x x y z w
theorem Equation254_implies_Equation217 (G : Type*) [Magma G] (h : Equation254 G) : Equation217 G := λ x y z w => h x x y z w
theorem Equation306_implies_Equation269 (G : Type*) [Magma G] (h : Equation306 G) : Equation269 G := λ x y z w => h x x y z w
theorem Equation358_implies_Equation321 (G : Type*) [Magma G] (h : Equation358 G) : Equation321 G := λ x y z w => h x x y z w
theorem Equation410_implies_Equation373 (G : Type*) [Magma G] (h : Equation410 G) : Equation373 G := λ x y z w => h x x y z w
theorem Equation462_implies_Equation425 (G : Type*) [Magma G] (h : Equation462 G) : Equation425 G := λ x y z w => h x x y z w
theorem Equation499_implies_Equation425 (G : Type*) [Magma G] (h : Equation499 G) : Equation425 G := λ x y z w => h x x y z w
theorem Equation536_implies_Equation425 (G : Type*) [Magma G] (h : Equation536 G) : Equation425 G := λ x y z w => h x x y z w
theorem Equation553_implies_Equation435 (G : Type*) [Magma G] (h : Equation553 G) : Equation435 G := λ x y z w => h x x y z w
theorem Equation570_implies_Equation435 (G : Type*) [Magma G] (h : Equation570 G) : Equation435 G := λ x y z w => h x x y z w
theorem Equation587_implies_Equation445 (G : Type*) [Magma G] (h : Equation587 G) : Equation445 G := λ x y z w => h x x y z w
theorem Equation592_implies_Equation449 (G : Type*) [Magma G] (h : Equation592 G) : Equation449 G := λ x y z w => h x x y z w
theorem Equation597_implies_Equation449 (G : Type*) [Magma G] (h : Equation597 G) : Equation449 G := λ x y z w => h x x y z w
theorem Equation602_implies_Equation453 (G : Type*) [Magma G] (h : Equation602 G) : Equation453 G := λ x y z w => h x x y z w
theorem Equation607_implies_Equation457 (G : Type*) [Magma G] (h : Equation607 G) : Equation457 G := λ x y z w => h x x y z w
theorem Equation608_implies_Equation458 (G : Type*) [Magma G] (h : Equation608 G) : Equation458 G := λ x y z w => h x x y z w
theorem Equation609_implies_Equation458 (G : Type*) [Magma G] (h : Equation609 G) : Equation458 G := λ x y z w => h x x y z w
theorem Equation610_implies_Equation459 (G : Type*) [Magma G] (h : Equation610 G) : Equation459 G := λ x y z w => h x x y z w
theorem Equation611_implies_Equation460 (G : Type*) [Magma G] (h : Equation611 G) : Equation460 G := λ x y z w => h x x y z w
theorem Equation612_implies_Equation461 (G : Type*) [Magma G] (h : Equation612 G) : Equation461 G := λ x y z w => h x x y z w
theorem Equation665_implies_Equation628 (G : Type*) [Magma G] (h : Equation665 G) : Equation628 G := λ x y z w => h x x y z w
theorem Equation702_implies_Equation628 (G : Type*) [Magma G] (h : Equation702 G) : Equation628 G := λ x y z w => h x x y z w
theorem Equation739_implies_Equation628 (G : Type*) [Magma G] (h : Equation739 G) : Equation628 G := λ x y z w => h x x y z w
theorem Equation756_implies_Equation638 (G : Type*) [Magma G] (h : Equation756 G) : Equation638 G := λ x y z w => h x x y z w
theorem Equation773_implies_Equation638 (G : Type*) [Magma G] (h : Equation773 G) : Equation638 G := λ x y z w => h x x y z w
theorem Equation790_implies_Equation648 (G : Type*) [Magma G] (h : Equation790 G) : Equation648 G := λ x y z w => h x x y z w
theorem Equation795_implies_Equation652 (G : Type*) [Magma G] (h : Equation795 G) : Equation652 G := λ x y z w => h x x y z w
theorem Equation800_implies_Equation652 (G : Type*) [Magma G] (h : Equation800 G) : Equation652 G := λ x y z w => h x x y z w
theorem Equation805_implies_Equation656 (G : Type*) [Magma G] (h : Equation805 G) : Equation656 G := λ x y z w => h x x y z w
theorem Equation810_implies_Equation660 (G : Type*) [Magma G] (h : Equation810 G) : Equation660 G := λ x y z w => h x x y z w
theorem Equation811_implies_Equation661 (G : Type*) [Magma G] (h : Equation811 G) : Equation661 G := λ x y z w => h x x y z w
theorem Equation812_implies_Equation661 (G : Type*) [Magma G] (h : Equation812 G) : Equation661 G := λ x y z w => h x x y z w
theorem Equation813_implies_Equation662 (G : Type*) [Magma G] (h : Equation813 G) : Equation662 G := λ x y z w => h x x y z w
theorem Equation814_implies_Equation663 (G : Type*) [Magma G] (h : Equation814 G) : Equation663 G := λ x y z w => h x x y z w
theorem Equation815_implies_Equation664 (G : Type*) [Magma G] (h : Equation815 G) : Equation664 G := λ x y z w => h x x y z w
theorem Equation868_implies_Equation831 (G : Type*) [Magma G] (h : Equation868 G) : Equation831 G := λ x y z w => h x x y z w
theorem Equation905_implies_Equation831 (G : Type*) [Magma G] (h : Equation905 G) : Equation831 G := λ x y z w => h x x y z w
theorem Equation942_implies_Equation831 (G : Type*) [Magma G] (h : Equation942 G) : Equation831 G := λ x y z w => h x x y z w
theorem Equation959_implies_Equation841 (G : Type*) [Magma G] (h : Equation959 G) : Equation841 G := λ x y z w => h x x y z w
theorem Equation976_implies_Equation841 (G : Type*) [Magma G] (h : Equation976 G) : Equation841 G := λ x y z w => h x x y z w
theorem Equation993_implies_Equation851 (G : Type*) [Magma G] (h : Equation993 G) : Equation851 G := λ x y z w => h x x y z w
theorem Equation998_implies_Equation855 (G : Type*) [Magma G] (h : Equation998 G) : Equation855 G := λ x y z w => h x x y z w
theorem Equation1003_implies_Equation855 (G : Type*) [Magma G] (h : Equation1003 G) : Equation855 G := λ x y z w => h x x y z w
theorem Equation1008_implies_Equation859 (G : Type*) [Magma G] (h : Equation1008 G) : Equation859 G := λ x y z w => h x x y z w
theorem Equation1013_implies_Equation863 (G : Type*) [Magma G] (h : Equation1013 G) : Equation863 G := λ x y z w => h x x y z w
theorem Equation1014_implies_Equation864 (G : Type*) [Magma G] (h : Equation1014 G) : Equation864 G := λ x y z w => h x x y z w
theorem Equation1015_implies_Equation864 (G : Type*) [Magma G] (h : Equation1015 G) : Equation864 G := λ x y z w => h x x y z w
theorem Equation1016_implies_Equation865 (G : Type*) [Magma G] (h : Equation1016 G) : Equation865 G := λ x y z w => h x x y z w
theorem Equation1017_implies_Equation866 (G : Type*) [Magma G] (h : Equation1017 G) : Equation866 G := λ x y z w => h x x y z w
theorem Equation1018_implies_Equation867 (G : Type*) [Magma G] (h : Equation1018 G) : Equation867 G := λ x y z w => h x x y z w
theorem Equation1071_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1034 G := λ x y z w => h x x y z w
theorem Equation1108_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1034 G := λ x y z w => h x x y z w
theorem Equation1145_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1034 G := λ x y z w => h x x y z w
theorem Equation1162_implies_Equation1044 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1044 G := λ x y z w => h x x y z w
theorem Equation1179_implies_Equation1044 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1044 G := λ x y z w => h x x y z w
theorem Equation1196_implies_Equation1054 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1054 G := λ x y z w => h x x y z w
theorem Equation1201_implies_Equation1058 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1058 G := λ x y z w => h x x y z w
theorem Equation1206_implies_Equation1058 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1058 G := λ x y z w => h x x y z w
theorem Equation1211_implies_Equation1062 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1062 G := λ x y z w => h x x y z w
theorem Equation1216_implies_Equation1066 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1066 G := λ x y z w => h x x y z w
theorem Equation1217_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1067 G := λ x y z w => h x x y z w
theorem Equation1218_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1067 G := λ x y z w => h x x y z w
theorem Equation1219_implies_Equation1068 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1068 G := λ x y z w => h x x y z w
theorem Equation1220_implies_Equation1069 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1069 G := λ x y z w => h x x y z w
theorem Equation1221_implies_Equation1070 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1070 G := λ x y z w => h x x y z w
theorem Equation1274_implies_Equation1237 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1237 G := λ x y z w => h x x y z w
theorem Equation1311_implies_Equation1237 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1237 G := λ x y z w => h x x y z w
theorem Equation1348_implies_Equation1237 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1237 G := λ x y z w => h x x y z w
theorem Equation1365_implies_Equation1247 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1247 G := λ x y z w => h x x y z w
theorem Equation1382_implies_Equation1247 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1247 G := λ x y z w => h x x y z w
theorem Equation1399_implies_Equation1257 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1257 G := λ x y z w => h x x y z w
theorem Equation1404_implies_Equation1261 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1261 G := λ x y z w => h x x y z w
theorem Equation1409_implies_Equation1261 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1261 G := λ x y z w => h x x y z w
theorem Equation1414_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1265 G := λ x y z w => h x x y z w
theorem Equation1419_implies_Equation1269 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1269 G := λ x y z w => h x x y z w
theorem Equation1420_implies_Equation1270 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1270 G := λ x y z w => h x x y z w
theorem Equation1421_implies_Equation1270 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1270 G := λ x y z w => h x x y z w
theorem Equation1422_implies_Equation1271 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1271 G := λ x y z w => h x x y z w
theorem Equation1423_implies_Equation1272 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1272 G := λ x y z w => h x x y z w
theorem Equation1424_implies_Equation1273 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1273 G := λ x y z w => h x x y z w
theorem Equation1477_implies_Equation1440 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1440 G := λ x y z w => h x x y z w
theorem Equation1514_implies_Equation1440 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1440 G := λ x y z w => h x x y z w
theorem Equation1551_implies_Equation1440 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1440 G := λ x y z w => h x x y z w
theorem Equation1568_implies_Equation1450 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1450 G := λ x y z w => h x x y z w
theorem Equation1585_implies_Equation1450 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1450 G := λ x y z w => h x x y z w
theorem Equation1602_implies_Equation1460 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1460 G := λ x y z w => h x x y z w
theorem Equation1607_implies_Equation1464 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1464 G := λ x y z w => h x x y z w
theorem Equation1612_implies_Equation1464 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1464 G := λ x y z w => h x x y z w
theorem Equation1617_implies_Equation1468 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1468 G := λ x y z w => h x x y z w
theorem Equation1622_implies_Equation1472 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1472 G := λ x y z w => h x x y z w
theorem Equation1623_implies_Equation1473 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1473 G := λ x y z w => h x x y z w
theorem Equation1624_implies_Equation1473 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1473 G := λ x y z w => h x x y z w
theorem Equation1625_implies_Equation1474 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1474 G := λ x y z w => h x x y z w
theorem Equation1626_implies_Equation1475 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1475 G := λ x y z w => h x x y z w
theorem Equation1627_implies_Equation1476 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1476 G := λ x y z w => h x x y z w
theorem Equation1680_implies_Equation1643 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1643 G := λ x y z w => h x x y z w
theorem Equation1717_implies_Equation1643 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1643 G := λ x y z w => h x x y z w
theorem Equation1754_implies_Equation1643 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1643 G := λ x y z w => h x x y z w
theorem Equation1771_implies_Equation1653 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1653 G := λ x y z w => h x x y z w
theorem Equation1788_implies_Equation1653 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1653 G := λ x y z w => h x x y z w
theorem Equation1805_implies_Equation1663 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1663 G := λ x y z w => h x x y z w
theorem Equation1810_implies_Equation1667 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1667 G := λ x y z w => h x x y z w
theorem Equation1815_implies_Equation1667 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1667 G := λ x y z w => h x x y z w
theorem Equation1820_implies_Equation1671 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1671 G := λ x y z w => h x x y z w
theorem Equation1825_implies_Equation1675 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1675 G := λ x y z w => h x x y z w
theorem Equation1826_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1676 G := λ x y z w => h x x y z w
theorem Equation1827_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1676 G := λ x y z w => h x x y z w
theorem Equation1828_implies_Equation1677 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1677 G := λ x y z w => h x x y z w
theorem Equation1829_implies_Equation1678 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1678 G := λ x y z w => h x x y z w
theorem Equation1830_implies_Equation1679 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1679 G := λ x y z w => h x x y z w
theorem Equation1883_implies_Equation1846 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1846 G := λ x y z w => h x x y z w
theorem Equation1920_implies_Equation1846 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1846 G := λ x y z w => h x x y z w
theorem Equation1957_implies_Equation1846 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1846 G := λ x y z w => h x x y z w
theorem Equation1974_implies_Equation1856 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1856 G := λ x y z w => h x x y z w
theorem Equation1991_implies_Equation1856 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1856 G := λ x y z w => h x x y z w
theorem Equation2008_implies_Equation1866 (G : Type*) [Magma G] (h : Equation2008 G) : Equation1866 G := λ x y z w => h x x y z w
theorem Equation2013_implies_Equation1870 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1870 G := λ x y z w => h x x y z w
theorem Equation2018_implies_Equation1870 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1870 G := λ x y z w => h x x y z w
theorem Equation2023_implies_Equation1874 (G : Type*) [Magma G] (h : Equation2023 G) : Equation1874 G := λ x y z w => h x x y z w
theorem Equation2028_implies_Equation1878 (G : Type*) [Magma G] (h : Equation2028 G) : Equation1878 G := λ x y z w => h x x y z w
theorem Equation2029_implies_Equation1879 (G : Type*) [Magma G] (h : Equation2029 G) : Equation1879 G := λ x y z w => h x x y z w
theorem Equation2030_implies_Equation1879 (G : Type*) [Magma G] (h : Equation2030 G) : Equation1879 G := λ x y z w => h x x y z w
theorem Equation2031_implies_Equation1880 (G : Type*) [Magma G] (h : Equation2031 G) : Equation1880 G := λ x y z w => h x x y z w
theorem Equation2032_implies_Equation1881 (G : Type*) [Magma G] (h : Equation2032 G) : Equation1881 G := λ x y z w => h x x y z w
theorem Equation2033_implies_Equation1882 (G : Type*) [Magma G] (h : Equation2033 G) : Equation1882 G := λ x y z w => h x x y z w
theorem Equation2086_implies_Equation2049 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2049 G := λ x y z w => h x x y z w
theorem Equation2123_implies_Equation2049 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2049 G := λ x y z w => h x x y z w
theorem Equation2160_implies_Equation2049 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2049 G := λ x y z w => h x x y z w
theorem Equation2177_implies_Equation2059 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2059 G := λ x y z w => h x x y z w
theorem Equation2194_implies_Equation2059 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2059 G := λ x y z w => h x x y z w
theorem Equation2211_implies_Equation2069 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2069 G := λ x y z w => h x x y z w
theorem Equation2216_implies_Equation2073 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2073 G := λ x y z w => h x x y z w
theorem Equation2221_implies_Equation2073 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2073 G := λ x y z w => h x x y z w
theorem Equation2226_implies_Equation2077 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2077 G := λ x y z w => h x x y z w
theorem Equation2231_implies_Equation2081 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2081 G := λ x y z w => h x x y z w
theorem Equation2232_implies_Equation2082 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2082 G := λ x y z w => h x x y z w
theorem Equation2233_implies_Equation2082 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2082 G := λ x y z w => h x x y z w
theorem Equation2234_implies_Equation2083 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2083 G := λ x y z w => h x x y z w
theorem Equation2235_implies_Equation2084 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2084 G := λ x y z w => h x x y z w
theorem Equation2236_implies_Equation2085 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2085 G := λ x y z w => h x x y z w
theorem Equation2289_implies_Equation2252 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2252 G := λ x y z w => h x x y z w
theorem Equation2326_implies_Equation2252 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2252 G := λ x y z w => h x x y z w
theorem Equation2363_implies_Equation2252 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2252 G := λ x y z w => h x x y z w
theorem Equation2380_implies_Equation2262 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2262 G := λ x y z w => h x x y z w
theorem Equation2397_implies_Equation2262 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2262 G := λ x y z w => h x x y z w
theorem Equation2414_implies_Equation2272 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2272 G := λ x y z w => h x x y z w
theorem Equation2419_implies_Equation2276 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2276 G := λ x y z w => h x x y z w
theorem Equation2424_implies_Equation2276 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2276 G := λ x y z w => h x x y z w
theorem Equation2429_implies_Equation2280 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2280 G := λ x y z w => h x x y z w
theorem Equation2434_implies_Equation2284 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2284 G := λ x y z w => h x x y z w
theorem Equation2435_implies_Equation2285 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2285 G := λ x y z w => h x x y z w
theorem Equation2436_implies_Equation2285 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2285 G := λ x y z w => h x x y z w
theorem Equation2437_implies_Equation2286 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2286 G := λ x y z w => h x x y z w
theorem Equation2438_implies_Equation2287 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2287 G := λ x y z w => h x x y z w
theorem Equation2439_implies_Equation2288 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2288 G := λ x y z w => h x x y z w
theorem Equation2492_implies_Equation2455 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2455 G := λ x y z w => h x x y z w
theorem Equation2529_implies_Equation2455 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2455 G := λ x y z w => h x x y z w
theorem Equation2566_implies_Equation2455 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2455 G := λ x y z w => h x x y z w
theorem Equation2583_implies_Equation2465 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2465 G := λ x y z w => h x x y z w
theorem Equation2600_implies_Equation2465 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2465 G := λ x y z w => h x x y z w
theorem Equation2617_implies_Equation2475 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2475 G := λ x y z w => h x x y z w
theorem Equation2622_implies_Equation2479 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2479 G := λ x y z w => h x x y z w
theorem Equation2627_implies_Equation2479 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2479 G := λ x y z w => h x x y z w
theorem Equation2632_implies_Equation2483 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2483 G := λ x y z w => h x x y z w
theorem Equation2637_implies_Equation2487 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2487 G := λ x y z w => h x x y z w
theorem Equation2638_implies_Equation2488 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2488 G := λ x y z w => h x x y z w
theorem Equation2639_implies_Equation2488 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2488 G := λ x y z w => h x x y z w
theorem Equation2640_implies_Equation2489 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2489 G := λ x y z w => h x x y z w
theorem Equation2641_implies_Equation2490 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2490 G := λ x y z w => h x x y z w
theorem Equation2642_implies_Equation2491 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2491 G := λ x y z w => h x x y z w
theorem Equation2695_implies_Equation2658 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2658 G := λ x y z w => h x x y z w
theorem Equation2732_implies_Equation2658 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2658 G := λ x y z w => h x x y z w
theorem Equation2769_implies_Equation2658 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2658 G := λ x y z w => h x x y z w
theorem Equation2786_implies_Equation2668 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2668 G := λ x y z w => h x x y z w
theorem Equation2803_implies_Equation2668 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2668 G := λ x y z w => h x x y z w
theorem Equation2820_implies_Equation2678 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2678 G := λ x y z w => h x x y z w
theorem Equation2825_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2682 G := λ x y z w => h x x y z w
theorem Equation2830_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2682 G := λ x y z w => h x x y z w
theorem Equation2835_implies_Equation2686 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2686 G := λ x y z w => h x x y z w
theorem Equation2840_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2690 G := λ x y z w => h x x y z w
theorem Equation2841_implies_Equation2691 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2691 G := λ x y z w => h x x y z w
theorem Equation2842_implies_Equation2691 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2691 G := λ x y z w => h x x y z w
theorem Equation2843_implies_Equation2692 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2692 G := λ x y z w => h x x y z w
theorem Equation2844_implies_Equation2693 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2693 G := λ x y z w => h x x y z w
theorem Equation2845_implies_Equation2694 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2694 G := λ x y z w => h x x y z w
theorem Equation2898_implies_Equation2861 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2861 G := λ x y z w => h x x y z w
theorem Equation2935_implies_Equation2861 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2861 G := λ x y z w => h x x y z w
theorem Equation2972_implies_Equation2861 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2861 G := λ x y z w => h x x y z w
theorem Equation2989_implies_Equation2871 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2871 G := λ x y z w => h x x y z w
theorem Equation3006_implies_Equation2871 (G : Type*) [Magma G] (h : Equation3006 G) : Equation2871 G := λ x y z w => h x x y z w
theorem Equation3023_implies_Equation2881 (G : Type*) [Magma G] (h : Equation3023 G) : Equation2881 G := λ x y z w => h x x y z w
theorem Equation3028_implies_Equation2885 (G : Type*) [Magma G] (h : Equation3028 G) : Equation2885 G := λ x y z w => h x x y z w
theorem Equation3033_implies_Equation2885 (G : Type*) [Magma G] (h : Equation3033 G) : Equation2885 G := λ x y z w => h x x y z w
theorem Equation3038_implies_Equation2889 (G : Type*) [Magma G] (h : Equation3038 G) : Equation2889 G := λ x y z w => h x x y z w
theorem Equation3043_implies_Equation2893 (G : Type*) [Magma G] (h : Equation3043 G) : Equation2893 G := λ x y z w => h x x y z w
theorem Equation3044_implies_Equation2894 (G : Type*) [Magma G] (h : Equation3044 G) : Equation2894 G := λ x y z w => h x x y z w
theorem Equation3045_implies_Equation2894 (G : Type*) [Magma G] (h : Equation3045 G) : Equation2894 G := λ x y z w => h x x y z w
theorem Equation3046_implies_Equation2895 (G : Type*) [Magma G] (h : Equation3046 G) : Equation2895 G := λ x y z w => h x x y z w
theorem Equation3047_implies_Equation2896 (G : Type*) [Magma G] (h : Equation3047 G) : Equation2896 G := λ x y z w => h x x y z w
theorem Equation3048_implies_Equation2897 (G : Type*) [Magma G] (h : Equation3048 G) : Equation2897 G := λ x y z w => h x x y z w
theorem Equation3101_implies_Equation3064 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3064 G := λ x y z w => h x x y z w
theorem Equation3138_implies_Equation3064 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3064 G := λ x y z w => h x x y z w
theorem Equation3175_implies_Equation3064 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3064 G := λ x y z w => h x x y z w
theorem Equation3192_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3074 G := λ x y z w => h x x y z w
theorem Equation3209_implies_Equation3074 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3074 G := λ x y z w => h x x y z w
theorem Equation3226_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3084 G := λ x y z w => h x x y z w
theorem Equation3231_implies_Equation3088 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3088 G := λ x y z w => h x x y z w
theorem Equation3236_implies_Equation3088 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3088 G := λ x y z w => h x x y z w
theorem Equation3241_implies_Equation3092 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3092 G := λ x y z w => h x x y z w
theorem Equation3246_implies_Equation3096 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3096 G := λ x y z w => h x x y z w
theorem Equation3247_implies_Equation3097 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3097 G := λ x y z w => h x x y z w
theorem Equation3248_implies_Equation3097 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3097 G := λ x y z w => h x x y z w
theorem Equation3249_implies_Equation3098 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3098 G := λ x y z w => h x x y z w
theorem Equation3250_implies_Equation3099 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3099 G := λ x y z w => h x x y z w
theorem Equation3251_implies_Equation3100 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3100 G := λ x y z w => h x x y z w
theorem Equation3304_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3267 G := λ x y z w => h x x y z w
theorem Equation3341_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3267 G := λ x y z w => h x x y z w
theorem Equation3378_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3267 G := λ x y z w => h x x y z w
theorem Equation3395_implies_Equation3277 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3277 G := λ x y z w => h x x y z w
theorem Equation3412_implies_Equation3277 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3277 G := λ x y z w => h x x y z w
theorem Equation3429_implies_Equation3287 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3287 G := λ x y z w => h x x y z w
theorem Equation3434_implies_Equation3291 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3291 G := λ x y z w => h x x y z w
theorem Equation3439_implies_Equation3291 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3291 G := λ x y z w => h x x y z w
theorem Equation3444_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3295 G := λ x y z w => h x x y z w
theorem Equation3449_implies_Equation3299 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3299 G := λ x y z w => h x x y z w
theorem Equation3450_implies_Equation3300 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3300 G := λ x y z w => h x x y z w
theorem Equation3451_implies_Equation3300 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3300 G := λ x y z w => h x x y z w
theorem Equation3452_implies_Equation3301 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3301 G := λ x y z w => h x x y z w
theorem Equation3453_implies_Equation3302 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3302 G := λ x y z w => h x x y z w
theorem Equation3454_implies_Equation3303 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3303 G := λ x y z w => h x x y z w
theorem Equation3507_implies_Equation3470 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3470 G := λ x y z w => h x x y z w
theorem Equation3544_implies_Equation3470 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3470 G := λ x y z w => h x x y z w
theorem Equation3581_implies_Equation3470 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3470 G := λ x y z w => h x x y z w
theorem Equation3598_implies_Equation3480 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3480 G := λ x y z w => h x x y z w
theorem Equation3615_implies_Equation3480 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3480 G := λ x y z w => h x x y z w
theorem Equation3632_implies_Equation3490 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3490 G := λ x y z w => h x x y z w
theorem Equation3637_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3494 G := λ x y z w => h x x y z w
theorem Equation3642_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3494 G := λ x y z w => h x x y z w
theorem Equation3647_implies_Equation3498 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3498 G := λ x y z w => h x x y z w
theorem Equation3652_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3502 G := λ x y z w => h x x y z w
theorem Equation3653_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3503 G := λ x y z w => h x x y z w
theorem Equation3654_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3503 G := λ x y z w => h x x y z w
theorem Equation3655_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3504 G := λ x y z w => h x x y z w
theorem Equation3656_implies_Equation3505 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3505 G := λ x y z w => h x x y z w
theorem Equation3657_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3506 G := λ x y z w => h x x y z w
theorem Equation3710_implies_Equation3673 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3673 G := λ x y z w => h x x y z w
theorem Equation3747_implies_Equation3673 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3673 G := λ x y z w => h x x y z w
theorem Equation3784_implies_Equation3673 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3673 G := λ x y z w => h x x y z w
theorem Equation3801_implies_Equation3683 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3683 G := λ x y z w => h x x y z w
theorem Equation3818_implies_Equation3683 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3683 G := λ x y z w => h x x y z w
theorem Equation3835_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3693 G := λ x y z w => h x x y z w
theorem Equation3840_implies_Equation3697 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3697 G := λ x y z w => h x x y z w
theorem Equation3845_implies_Equation3697 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3697 G := λ x y z w => h x x y z w
theorem Equation3850_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3701 G := λ x y z w => h x x y z w
theorem Equation3855_implies_Equation3705 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3705 G := λ x y z w => h x x y z w
theorem Equation3856_implies_Equation3706 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3706 G := λ x y z w => h x x y z w
theorem Equation3857_implies_Equation3706 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3706 G := λ x y z w => h x x y z w
theorem Equation3858_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3707 G := λ x y z w => h x x y z w
theorem Equation3859_implies_Equation3708 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3708 G := λ x y z w => h x x y z w
theorem Equation3860_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3709 G := λ x y z w => h x x y z w
theorem Equation3913_implies_Equation3876 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3876 G := λ x y z w => h x x y z w
theorem Equation3950_implies_Equation3876 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3876 G := λ x y z w => h x x y z w
theorem Equation3987_implies_Equation3876 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3876 G := λ x y z w => h x x y z w
theorem Equation4004_implies_Equation3886 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3886 G := λ x y z w => h x x y z w
theorem Equation4021_implies_Equation3886 (G : Type*) [Magma G] (h : Equation4021 G) : Equation3886 G := λ x y z w => h x x y z w
theorem Equation4038_implies_Equation3896 (G : Type*) [Magma G] (h : Equation4038 G) : Equation3896 G := λ x y z w => h x x y z w
theorem Equation4043_implies_Equation3900 (G : Type*) [Magma G] (h : Equation4043 G) : Equation3900 G := λ x y z w => h x x y z w
theorem Equation4048_implies_Equation3900 (G : Type*) [Magma G] (h : Equation4048 G) : Equation3900 G := λ x y z w => h x x y z w
theorem Equation4053_implies_Equation3904 (G : Type*) [Magma G] (h : Equation4053 G) : Equation3904 G := λ x y z w => h x x y z w
theorem Equation4058_implies_Equation3908 (G : Type*) [Magma G] (h : Equation4058 G) : Equation3908 G := λ x y z w => h x x y z w
theorem Equation4059_implies_Equation3909 (G : Type*) [Magma G] (h : Equation4059 G) : Equation3909 G := λ x y z w => h x x y z w
theorem Equation4060_implies_Equation3909 (G : Type*) [Magma G] (h : Equation4060 G) : Equation3909 G := λ x y z w => h x x y z w
theorem Equation4061_implies_Equation3910 (G : Type*) [Magma G] (h : Equation4061 G) : Equation3910 G := λ x y z w => h x x y z w
theorem Equation4062_implies_Equation3911 (G : Type*) [Magma G] (h : Equation4062 G) : Equation3911 G := λ x y z w => h x x y z w
theorem Equation4063_implies_Equation3912 (G : Type*) [Magma G] (h : Equation4063 G) : Equation3912 G := λ x y z w => h x x y z w
theorem Equation4116_implies_Equation4079 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4079 G := λ x y z w => h x x y z w
theorem Equation4153_implies_Equation4079 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4079 G := λ x y z w => h x x y z w
theorem Equation4190_implies_Equation4079 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4079 G := λ x y z w => h x x y z w
theorem Equation4207_implies_Equation4089 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4089 G := λ x y z w => h x x y z w
theorem Equation4224_implies_Equation4089 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4089 G := λ x y z w => h x x y z w
theorem Equation4241_implies_Equation4099 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4099 G := λ x y z w => h x x y z w
theorem Equation4246_implies_Equation4103 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4103 G := λ x y z w => h x x y z w
theorem Equation4251_implies_Equation4103 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4103 G := λ x y z w => h x x y z w
theorem Equation4256_implies_Equation4107 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4107 G := λ x y z w => h x x y z w
theorem Equation4261_implies_Equation4111 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4111 G := λ x y z w => h x x y z w
theorem Equation4262_implies_Equation4112 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4112 G := λ x y z w => h x x y z w
theorem Equation4263_implies_Equation4112 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4112 G := λ x y z w => h x x y z w
theorem Equation4264_implies_Equation4113 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4113 G := λ x y z w => h x x y z w
theorem Equation4265_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4114 G := λ x y z w => h x x y z w
theorem Equation4266_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4115 G := λ x y z w => h x x y z w
theorem Equation4313_implies_Equation4281 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4281 G := λ x y z w => h x x y z w
theorem Equation4338_implies_Equation4281 (G : Type*) [Magma G] (h : Equation4338 G) : Equation4281 G := λ x y z w => h x x y z w
theorem Equation4356_implies_Equation4281 (G : Type*) [Magma G] (h : Equation4356 G) : Equation4281 G := λ x y z w => h x x y z w
theorem Equation4361_implies_Equation4289 (G : Type*) [Magma G] (h : Equation4361 G) : Equation4289 G := λ x y z w => h x x y z w
theorem Equation4368_implies_Equation4289 (G : Type*) [Magma G] (h : Equation4368 G) : Equation4289 G := λ x y z w => h x x y z w
theorem Equation4373_implies_Equation4298 (G : Type*) [Magma G] (h : Equation4373 G) : Equation4298 G := λ x y z w => h x x y z w
theorem Equation4375_implies_Equation4302 (G : Type*) [Magma G] (h : Equation4375 G) : Equation4302 G := λ x y z w => h x x y z w
theorem Equation4377_implies_Equation4306 (G : Type*) [Magma G] (h : Equation4377 G) : Equation4306 G := λ x y z w => h x x y z w
theorem Equation4378_implies_Equation4310 (G : Type*) [Magma G] (h : Equation4378 G) : Equation4310 G := λ x y z w => h x x y z w
theorem Equation4431_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4394 G := λ x y z w => h x x y z w
theorem Equation4468_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4394 G := λ x y z w => h x x y z w
theorem Equation4505_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4394 G := λ x y z w => h x x y z w
theorem Equation4522_implies_Equation4404 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4404 G := λ x y z w => h x x y z w
theorem Equation4539_implies_Equation4404 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4404 G := λ x y z w => h x x y z w
theorem Equation4556_implies_Equation4414 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4414 G := λ x y z w => h x x y z w
theorem Equation4561_implies_Equation4418 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4418 G := λ x y z w => h x x y z w
theorem Equation4566_implies_Equation4418 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4418 G := λ x y z w => h x x y z w
theorem Equation4571_implies_Equation4422 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4422 G := λ x y z w => h x x y z w
theorem Equation4576_implies_Equation4426 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4426 G := λ x y z w => h x x y z w
theorem Equation4577_implies_Equation4427 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4427 G := λ x y z w => h x x y z w
theorem Equation4578_implies_Equation4427 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4427 G := λ x y z w => h x x y z w
theorem Equation4579_implies_Equation4428 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4428 G := λ x y z w => h x x y z w
theorem Equation4580_implies_Equation4429 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4429 G := λ x y z w => h x x y z w
theorem Equation4581_implies_Equation4430 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4430 G := λ x y z w => h x x y z w
theorem Equation4628_implies_Equation4596 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4596 G := λ x y z w => h x x y z w
theorem Equation4653_implies_Equation4596 (G : Type*) [Magma G] (h : Equation4653 G) : Equation4596 G := λ x y z w => h x x y z w
theorem Equation4671_implies_Equation4596 (G : Type*) [Magma G] (h : Equation4671 G) : Equation4596 G := λ x y z w => h x x y z w
theorem Equation4676_implies_Equation4604 (G : Type*) [Magma G] (h : Equation4676 G) : Equation4604 G := λ x y z w => h x x y z w
theorem Equation4683_implies_Equation4604 (G : Type*) [Magma G] (h : Equation4683 G) : Equation4604 G := λ x y z w => h x x y z w
theorem Equation4688_implies_Equation4613 (G : Type*) [Magma G] (h : Equation4688 G) : Equation4613 G := λ x y z w => h x x y z w
theorem Equation4690_implies_Equation4617 (G : Type*) [Magma G] (h : Equation4690 G) : Equation4617 G := λ x y z w => h x x y z w
theorem Equation4692_implies_Equation4621 (G : Type*) [Magma G] (h : Equation4692 G) : Equation4621 G := λ x y z w => h x x y z w
theorem Equation4693_implies_Equation4625 (G : Type*) [Magma G] (h : Equation4693 G) : Equation4625 G := λ x y z w => h x x y z w