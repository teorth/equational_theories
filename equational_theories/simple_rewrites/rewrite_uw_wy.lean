import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation89 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ w))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ w)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation193 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ w)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ w
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation297 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ w
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation349 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ w)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation401 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ w
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation453 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation490 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (y ∘ w)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation527 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation544 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (y ∘ w)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation557 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (x ∘ w)))
def Equation561 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (y ∘ w)))
def Equation565 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
def Equation566 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ x)))
def Equation567 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ y)))
def Equation568 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ z)))
def Equation569 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation578 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
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
def Equation656 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation693 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ y) ∘ w))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation730 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation747 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ y) ∘ w))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation760 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ x) ∘ w))
def Equation764 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ y) ∘ w))
def Equation768 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
def Equation769 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ x))
def Equation770 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ y))
def Equation771 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ z))
def Equation772 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation781 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
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
def Equation859 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation896 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (y ∘ w))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation933 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation950 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (y ∘ w))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation963 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (x ∘ w))
def Equation967 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (y ∘ w))
def Equation971 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
def Equation972 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ x))
def Equation973 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ y))
def Equation974 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ z))
def Equation975 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation984 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
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
def Equation1062 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1099 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ w)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1136 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1153 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ w)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1166 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ w)
def Equation1170 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ w)
def Equation1174 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
def Equation1175 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ x)
def Equation1176 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ y)
def Equation1177 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ z)
def Equation1178 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1187 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
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
def Equation1265 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1302 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ y) ∘ w)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1339 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1356 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ y) ∘ w)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1369 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ x) ∘ w)
def Equation1373 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ y) ∘ w)
def Equation1377 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
def Equation1378 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ x)
def Equation1379 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ y)
def Equation1380 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ z)
def Equation1381 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1390 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
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
def Equation1468 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1505 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (y ∘ w))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1542 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1559 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (y ∘ w))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1572 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (x ∘ w))
def Equation1576 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (y ∘ w))
def Equation1580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
def Equation1581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ x))
def Equation1582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ y))
def Equation1583 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ z))
def Equation1584 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1593 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
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
def Equation1671 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1708 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ w)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1745 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1762 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ w)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1775 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ w)
def Equation1779 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ w)
def Equation1783 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
def Equation1784 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ x)
def Equation1785 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ y)
def Equation1786 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ z)
def Equation1787 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1796 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
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
def Equation1874 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1911 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ w)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1948 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1965 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ w)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1978 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ w)
def Equation1982 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ w)
def Equation1986 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
def Equation1987 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ x)
def Equation1988 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ y)
def Equation1989 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ z)
def Equation1990 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation1999 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
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
def Equation2077 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2114 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ w)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2151 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2168 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ w)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2181 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ w)
def Equation2185 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ w)
def Equation2189 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
def Equation2190 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ x)
def Equation2191 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ y)
def Equation2192 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ z)
def Equation2193 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2202 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
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
def Equation2280 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2317 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ w
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2354 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2371 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ w
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2384 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ w
def Equation2388 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ w
def Equation2392 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
def Equation2393 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ x
def Equation2394 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ y
def Equation2395 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ z
def Equation2396 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2405 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
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
def Equation2483 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2520 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ w
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2557 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2574 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ w
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2587 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ w
def Equation2591 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ w
def Equation2595 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
def Equation2596 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ x
def Equation2597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ y
def Equation2598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ z
def Equation2599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
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
def Equation2686 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2723 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ w
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2760 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2777 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ w
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2790 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ w
def Equation2794 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ w
def Equation2798 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
def Equation2799 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ x
def Equation2800 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ y
def Equation2801 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ z
def Equation2802 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2811 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
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
def Equation2889 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2926 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ w
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2963 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2980 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ w
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation2993 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ w
def Equation2997 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ w
def Equation3001 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
def Equation3002 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ x
def Equation3003 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ y
def Equation3004 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ z
def Equation3005 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3014 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
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
def Equation3092 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3129 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ w
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3166 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ w
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3183 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ w
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3196 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ w
def Equation3200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ w
def Equation3204 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
def Equation3205 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ x
def Equation3206 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ y
def Equation3207 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ z
def Equation3208 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
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
def Equation3295 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3332 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (y ∘ w))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3369 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (y ∘ w))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3386 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (y ∘ w))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3399 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (x ∘ w))
def Equation3403 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (y ∘ w))
def Equation3407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
def Equation3408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ x))
def Equation3409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ y))
def Equation3410 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ z))
def Equation3411 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3420 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
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
def Equation3498 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ y) ∘ w)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ y) ∘ w)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3589 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ y) ∘ w)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3602 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ x) ∘ w)
def Equation3606 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ y) ∘ w)
def Equation3610 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
def Equation3611 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ x)
def Equation3612 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ y)
def Equation3613 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ z)
def Equation3614 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3623 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
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
def Equation3701 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3738 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (y ∘ w)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3775 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (y ∘ w)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3792 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (y ∘ w)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3805 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (x ∘ w)
def Equation3809 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (y ∘ w)
def Equation3813 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
def Equation3814 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ x)
def Equation3815 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ y)
def Equation3816 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ z)
def Equation3817 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3826 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
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
def Equation3904 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3941 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ y)) ∘ w
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3978 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ y)) ∘ w
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation3995 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ y)) ∘ w
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4008 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ x)) ∘ w
def Equation4012 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ y)) ∘ w
def Equation4016 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
def Equation4017 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ x
def Equation4018 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ y
def Equation4019 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ z
def Equation4020 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4029 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
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
def Equation4107 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4144 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ y) ∘ w
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4181 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ y) ∘ w
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4198 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ y) ∘ w
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4211 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ x) ∘ w
def Equation4215 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ y) ∘ w
def Equation4219 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
def Equation4220 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ x
def Equation4221 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ y
def Equation4222 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ z
def Equation4223 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4232 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
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
def Equation4306 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4333 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (y ∘ w)
def Equation4338 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
def Equation4352 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (y ∘ w)
def Equation4356 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
def Equation4357 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (y ∘ w)
def Equation4361 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = x ∘ (w ∘ u)
def Equation4365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (z ∘ w)
def Equation4367 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ z)
def Equation4370 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (y ∘ w)
def Equation4373 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = z ∘ (w ∘ u)
def Equation4377 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (z ∘ u)
def Equation4378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (u ∘ z)
def Equation4422 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4459 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ y) ∘ w
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4496 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ y) ∘ w
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4513 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4526 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ x) ∘ w
def Equation4530 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ y) ∘ w
def Equation4534 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
def Equation4535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ x
def Equation4536 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ y
def Equation4537 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ z
def Equation4538 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4547 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
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
def Equation4621 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4648 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ y) ∘ w
def Equation4653 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
def Equation4667 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ y) ∘ w
def Equation4671 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
def Equation4672 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ y) ∘ w
def Equation4676 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (x ∘ w) ∘ u
def Equation4680 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ z) ∘ w
def Equation4682 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ z
def Equation4685 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ y) ∘ w
def Equation4688 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (z ∘ w) ∘ u
def Equation4692 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ z) ∘ u
def Equation4693 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ u) ∘ z
theorem Equation98_implies_Equation89 (G : Type*) [Magma G] (h : Equation98 G) : Equation89 G := λ x y z w => h x y z y w
theorem Equation150_implies_Equation141 (G : Type*) [Magma G] (h : Equation150 G) : Equation141 G := λ x y z w => h x y z y w
theorem Equation202_implies_Equation193 (G : Type*) [Magma G] (h : Equation202 G) : Equation193 G := λ x y z w => h x y z y w
theorem Equation254_implies_Equation245 (G : Type*) [Magma G] (h : Equation254 G) : Equation245 G := λ x y z w => h x y z y w
theorem Equation306_implies_Equation297 (G : Type*) [Magma G] (h : Equation306 G) : Equation297 G := λ x y z w => h x y z y w
theorem Equation358_implies_Equation349 (G : Type*) [Magma G] (h : Equation358 G) : Equation349 G := λ x y z w => h x y z y w
theorem Equation410_implies_Equation401 (G : Type*) [Magma G] (h : Equation410 G) : Equation401 G := λ x y z w => h x y z y w
theorem Equation462_implies_Equation453 (G : Type*) [Magma G] (h : Equation462 G) : Equation453 G := λ x y z w => h x y z y w
theorem Equation499_implies_Equation490 (G : Type*) [Magma G] (h : Equation499 G) : Equation490 G := λ x y z w => h x y z y w
theorem Equation536_implies_Equation527 (G : Type*) [Magma G] (h : Equation536 G) : Equation527 G := λ x y z w => h x y z y w
theorem Equation553_implies_Equation544 (G : Type*) [Magma G] (h : Equation553 G) : Equation544 G := λ x y z w => h x y z y w
theorem Equation570_implies_Equation561 (G : Type*) [Magma G] (h : Equation570 G) : Equation561 G := λ x y z w => h x y z y w
theorem Equation587_implies_Equation578 (G : Type*) [Magma G] (h : Equation587 G) : Equation578 G := λ x y z w => h x y z y w
theorem Equation592_implies_Equation557 (G : Type*) [Magma G] (h : Equation592 G) : Equation557 G := λ x y z w => h x y z y w
theorem Equation597_implies_Equation561 (G : Type*) [Magma G] (h : Equation597 G) : Equation561 G := λ x y z w => h x y z y w
theorem Equation602_implies_Equation565 (G : Type*) [Magma G] (h : Equation602 G) : Equation565 G := λ x y z w => h x y z y w
theorem Equation607_implies_Equation561 (G : Type*) [Magma G] (h : Equation607 G) : Equation561 G := λ x y z w => h x y z y w
theorem Equation608_implies_Equation566 (G : Type*) [Magma G] (h : Equation608 G) : Equation566 G := λ x y z w => h x y z y w
theorem Equation609_implies_Equation567 (G : Type*) [Magma G] (h : Equation609 G) : Equation567 G := λ x y z w => h x y z y w
theorem Equation610_implies_Equation568 (G : Type*) [Magma G] (h : Equation610 G) : Equation568 G := λ x y z w => h x y z y w
theorem Equation611_implies_Equation567 (G : Type*) [Magma G] (h : Equation611 G) : Equation567 G := λ x y z w => h x y z y w
theorem Equation612_implies_Equation569 (G : Type*) [Magma G] (h : Equation612 G) : Equation569 G := λ x y z w => h x y z y w
theorem Equation665_implies_Equation656 (G : Type*) [Magma G] (h : Equation665 G) : Equation656 G := λ x y z w => h x y z y w
theorem Equation702_implies_Equation693 (G : Type*) [Magma G] (h : Equation702 G) : Equation693 G := λ x y z w => h x y z y w
theorem Equation739_implies_Equation730 (G : Type*) [Magma G] (h : Equation739 G) : Equation730 G := λ x y z w => h x y z y w
theorem Equation756_implies_Equation747 (G : Type*) [Magma G] (h : Equation756 G) : Equation747 G := λ x y z w => h x y z y w
theorem Equation773_implies_Equation764 (G : Type*) [Magma G] (h : Equation773 G) : Equation764 G := λ x y z w => h x y z y w
theorem Equation790_implies_Equation781 (G : Type*) [Magma G] (h : Equation790 G) : Equation781 G := λ x y z w => h x y z y w
theorem Equation795_implies_Equation760 (G : Type*) [Magma G] (h : Equation795 G) : Equation760 G := λ x y z w => h x y z y w
theorem Equation800_implies_Equation764 (G : Type*) [Magma G] (h : Equation800 G) : Equation764 G := λ x y z w => h x y z y w
theorem Equation805_implies_Equation768 (G : Type*) [Magma G] (h : Equation805 G) : Equation768 G := λ x y z w => h x y z y w
theorem Equation810_implies_Equation764 (G : Type*) [Magma G] (h : Equation810 G) : Equation764 G := λ x y z w => h x y z y w
theorem Equation811_implies_Equation769 (G : Type*) [Magma G] (h : Equation811 G) : Equation769 G := λ x y z w => h x y z y w
theorem Equation812_implies_Equation770 (G : Type*) [Magma G] (h : Equation812 G) : Equation770 G := λ x y z w => h x y z y w
theorem Equation813_implies_Equation771 (G : Type*) [Magma G] (h : Equation813 G) : Equation771 G := λ x y z w => h x y z y w
theorem Equation814_implies_Equation770 (G : Type*) [Magma G] (h : Equation814 G) : Equation770 G := λ x y z w => h x y z y w
theorem Equation815_implies_Equation772 (G : Type*) [Magma G] (h : Equation815 G) : Equation772 G := λ x y z w => h x y z y w
theorem Equation868_implies_Equation859 (G : Type*) [Magma G] (h : Equation868 G) : Equation859 G := λ x y z w => h x y z y w
theorem Equation905_implies_Equation896 (G : Type*) [Magma G] (h : Equation905 G) : Equation896 G := λ x y z w => h x y z y w
theorem Equation942_implies_Equation933 (G : Type*) [Magma G] (h : Equation942 G) : Equation933 G := λ x y z w => h x y z y w
theorem Equation959_implies_Equation950 (G : Type*) [Magma G] (h : Equation959 G) : Equation950 G := λ x y z w => h x y z y w
theorem Equation976_implies_Equation967 (G : Type*) [Magma G] (h : Equation976 G) : Equation967 G := λ x y z w => h x y z y w
theorem Equation993_implies_Equation984 (G : Type*) [Magma G] (h : Equation993 G) : Equation984 G := λ x y z w => h x y z y w
theorem Equation998_implies_Equation963 (G : Type*) [Magma G] (h : Equation998 G) : Equation963 G := λ x y z w => h x y z y w
theorem Equation1003_implies_Equation967 (G : Type*) [Magma G] (h : Equation1003 G) : Equation967 G := λ x y z w => h x y z y w
theorem Equation1008_implies_Equation971 (G : Type*) [Magma G] (h : Equation1008 G) : Equation971 G := λ x y z w => h x y z y w
theorem Equation1013_implies_Equation967 (G : Type*) [Magma G] (h : Equation1013 G) : Equation967 G := λ x y z w => h x y z y w
theorem Equation1014_implies_Equation972 (G : Type*) [Magma G] (h : Equation1014 G) : Equation972 G := λ x y z w => h x y z y w
theorem Equation1015_implies_Equation973 (G : Type*) [Magma G] (h : Equation1015 G) : Equation973 G := λ x y z w => h x y z y w
theorem Equation1016_implies_Equation974 (G : Type*) [Magma G] (h : Equation1016 G) : Equation974 G := λ x y z w => h x y z y w
theorem Equation1017_implies_Equation973 (G : Type*) [Magma G] (h : Equation1017 G) : Equation973 G := λ x y z w => h x y z y w
theorem Equation1018_implies_Equation975 (G : Type*) [Magma G] (h : Equation1018 G) : Equation975 G := λ x y z w => h x y z y w
theorem Equation1071_implies_Equation1062 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1062 G := λ x y z w => h x y z y w
theorem Equation1108_implies_Equation1099 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1099 G := λ x y z w => h x y z y w
theorem Equation1145_implies_Equation1136 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1136 G := λ x y z w => h x y z y w
theorem Equation1162_implies_Equation1153 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1153 G := λ x y z w => h x y z y w
theorem Equation1179_implies_Equation1170 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1170 G := λ x y z w => h x y z y w
theorem Equation1196_implies_Equation1187 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1187 G := λ x y z w => h x y z y w
theorem Equation1201_implies_Equation1166 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1166 G := λ x y z w => h x y z y w
theorem Equation1206_implies_Equation1170 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1170 G := λ x y z w => h x y z y w
theorem Equation1211_implies_Equation1174 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1174 G := λ x y z w => h x y z y w
theorem Equation1216_implies_Equation1170 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1170 G := λ x y z w => h x y z y w
theorem Equation1217_implies_Equation1175 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1175 G := λ x y z w => h x y z y w
theorem Equation1218_implies_Equation1176 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1176 G := λ x y z w => h x y z y w
theorem Equation1219_implies_Equation1177 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1177 G := λ x y z w => h x y z y w
theorem Equation1220_implies_Equation1176 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1176 G := λ x y z w => h x y z y w
theorem Equation1221_implies_Equation1178 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1178 G := λ x y z w => h x y z y w
theorem Equation1274_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1265 G := λ x y z w => h x y z y w
theorem Equation1311_implies_Equation1302 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1302 G := λ x y z w => h x y z y w
theorem Equation1348_implies_Equation1339 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1339 G := λ x y z w => h x y z y w
theorem Equation1365_implies_Equation1356 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1356 G := λ x y z w => h x y z y w
theorem Equation1382_implies_Equation1373 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1373 G := λ x y z w => h x y z y w
theorem Equation1399_implies_Equation1390 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1390 G := λ x y z w => h x y z y w
theorem Equation1404_implies_Equation1369 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1369 G := λ x y z w => h x y z y w
theorem Equation1409_implies_Equation1373 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1373 G := λ x y z w => h x y z y w
theorem Equation1414_implies_Equation1377 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1377 G := λ x y z w => h x y z y w
theorem Equation1419_implies_Equation1373 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1373 G := λ x y z w => h x y z y w
theorem Equation1420_implies_Equation1378 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1378 G := λ x y z w => h x y z y w
theorem Equation1421_implies_Equation1379 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1379 G := λ x y z w => h x y z y w
theorem Equation1422_implies_Equation1380 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1380 G := λ x y z w => h x y z y w
theorem Equation1423_implies_Equation1379 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1379 G := λ x y z w => h x y z y w
theorem Equation1424_implies_Equation1381 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1381 G := λ x y z w => h x y z y w
theorem Equation1477_implies_Equation1468 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1468 G := λ x y z w => h x y z y w
theorem Equation1514_implies_Equation1505 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1505 G := λ x y z w => h x y z y w
theorem Equation1551_implies_Equation1542 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1542 G := λ x y z w => h x y z y w
theorem Equation1568_implies_Equation1559 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1559 G := λ x y z w => h x y z y w
theorem Equation1585_implies_Equation1576 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1576 G := λ x y z w => h x y z y w
theorem Equation1602_implies_Equation1593 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1593 G := λ x y z w => h x y z y w
theorem Equation1607_implies_Equation1572 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1572 G := λ x y z w => h x y z y w
theorem Equation1612_implies_Equation1576 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1576 G := λ x y z w => h x y z y w
theorem Equation1617_implies_Equation1580 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1580 G := λ x y z w => h x y z y w
theorem Equation1622_implies_Equation1576 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1576 G := λ x y z w => h x y z y w
theorem Equation1623_implies_Equation1581 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1581 G := λ x y z w => h x y z y w
theorem Equation1624_implies_Equation1582 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1582 G := λ x y z w => h x y z y w
theorem Equation1625_implies_Equation1583 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1583 G := λ x y z w => h x y z y w
theorem Equation1626_implies_Equation1582 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1582 G := λ x y z w => h x y z y w
theorem Equation1627_implies_Equation1584 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1584 G := λ x y z w => h x y z y w
theorem Equation1680_implies_Equation1671 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1671 G := λ x y z w => h x y z y w
theorem Equation1717_implies_Equation1708 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1708 G := λ x y z w => h x y z y w
theorem Equation1754_implies_Equation1745 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1745 G := λ x y z w => h x y z y w
theorem Equation1771_implies_Equation1762 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1762 G := λ x y z w => h x y z y w
theorem Equation1788_implies_Equation1779 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1779 G := λ x y z w => h x y z y w
theorem Equation1805_implies_Equation1796 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1796 G := λ x y z w => h x y z y w
theorem Equation1810_implies_Equation1775 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1775 G := λ x y z w => h x y z y w
theorem Equation1815_implies_Equation1779 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1779 G := λ x y z w => h x y z y w
theorem Equation1820_implies_Equation1783 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1783 G := λ x y z w => h x y z y w
theorem Equation1825_implies_Equation1779 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1779 G := λ x y z w => h x y z y w
theorem Equation1826_implies_Equation1784 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1784 G := λ x y z w => h x y z y w
theorem Equation1827_implies_Equation1785 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1785 G := λ x y z w => h x y z y w
theorem Equation1828_implies_Equation1786 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1786 G := λ x y z w => h x y z y w
theorem Equation1829_implies_Equation1785 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1785 G := λ x y z w => h x y z y w
theorem Equation1830_implies_Equation1787 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1787 G := λ x y z w => h x y z y w
theorem Equation1883_implies_Equation1874 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1874 G := λ x y z w => h x y z y w
theorem Equation1920_implies_Equation1911 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1911 G := λ x y z w => h x y z y w
theorem Equation1957_implies_Equation1948 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1948 G := λ x y z w => h x y z y w
theorem Equation1974_implies_Equation1965 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1965 G := λ x y z w => h x y z y w
theorem Equation1991_implies_Equation1982 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1982 G := λ x y z w => h x y z y w
theorem Equation2008_implies_Equation1999 (G : Type*) [Magma G] (h : Equation2008 G) : Equation1999 G := λ x y z w => h x y z y w
theorem Equation2013_implies_Equation1978 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1978 G := λ x y z w => h x y z y w
theorem Equation2018_implies_Equation1982 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1982 G := λ x y z w => h x y z y w
theorem Equation2023_implies_Equation1986 (G : Type*) [Magma G] (h : Equation2023 G) : Equation1986 G := λ x y z w => h x y z y w
theorem Equation2028_implies_Equation1982 (G : Type*) [Magma G] (h : Equation2028 G) : Equation1982 G := λ x y z w => h x y z y w
theorem Equation2029_implies_Equation1987 (G : Type*) [Magma G] (h : Equation2029 G) : Equation1987 G := λ x y z w => h x y z y w
theorem Equation2030_implies_Equation1988 (G : Type*) [Magma G] (h : Equation2030 G) : Equation1988 G := λ x y z w => h x y z y w
theorem Equation2031_implies_Equation1989 (G : Type*) [Magma G] (h : Equation2031 G) : Equation1989 G := λ x y z w => h x y z y w
theorem Equation2032_implies_Equation1988 (G : Type*) [Magma G] (h : Equation2032 G) : Equation1988 G := λ x y z w => h x y z y w
theorem Equation2033_implies_Equation1990 (G : Type*) [Magma G] (h : Equation2033 G) : Equation1990 G := λ x y z w => h x y z y w
theorem Equation2086_implies_Equation2077 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2077 G := λ x y z w => h x y z y w
theorem Equation2123_implies_Equation2114 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2114 G := λ x y z w => h x y z y w
theorem Equation2160_implies_Equation2151 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2151 G := λ x y z w => h x y z y w
theorem Equation2177_implies_Equation2168 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2168 G := λ x y z w => h x y z y w
theorem Equation2194_implies_Equation2185 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2185 G := λ x y z w => h x y z y w
theorem Equation2211_implies_Equation2202 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2202 G := λ x y z w => h x y z y w
theorem Equation2216_implies_Equation2181 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2181 G := λ x y z w => h x y z y w
theorem Equation2221_implies_Equation2185 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2185 G := λ x y z w => h x y z y w
theorem Equation2226_implies_Equation2189 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2189 G := λ x y z w => h x y z y w
theorem Equation2231_implies_Equation2185 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2185 G := λ x y z w => h x y z y w
theorem Equation2232_implies_Equation2190 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2190 G := λ x y z w => h x y z y w
theorem Equation2233_implies_Equation2191 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2191 G := λ x y z w => h x y z y w
theorem Equation2234_implies_Equation2192 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2192 G := λ x y z w => h x y z y w
theorem Equation2235_implies_Equation2191 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2191 G := λ x y z w => h x y z y w
theorem Equation2236_implies_Equation2193 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2193 G := λ x y z w => h x y z y w
theorem Equation2289_implies_Equation2280 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2280 G := λ x y z w => h x y z y w
theorem Equation2326_implies_Equation2317 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2317 G := λ x y z w => h x y z y w
theorem Equation2363_implies_Equation2354 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2354 G := λ x y z w => h x y z y w
theorem Equation2380_implies_Equation2371 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2371 G := λ x y z w => h x y z y w
theorem Equation2397_implies_Equation2388 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2388 G := λ x y z w => h x y z y w
theorem Equation2414_implies_Equation2405 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2405 G := λ x y z w => h x y z y w
theorem Equation2419_implies_Equation2384 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2384 G := λ x y z w => h x y z y w
theorem Equation2424_implies_Equation2388 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2388 G := λ x y z w => h x y z y w
theorem Equation2429_implies_Equation2392 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2392 G := λ x y z w => h x y z y w
theorem Equation2434_implies_Equation2388 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2388 G := λ x y z w => h x y z y w
theorem Equation2435_implies_Equation2393 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2393 G := λ x y z w => h x y z y w
theorem Equation2436_implies_Equation2394 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2394 G := λ x y z w => h x y z y w
theorem Equation2437_implies_Equation2395 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2395 G := λ x y z w => h x y z y w
theorem Equation2438_implies_Equation2394 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2394 G := λ x y z w => h x y z y w
theorem Equation2439_implies_Equation2396 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2396 G := λ x y z w => h x y z y w
theorem Equation2492_implies_Equation2483 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2483 G := λ x y z w => h x y z y w
theorem Equation2529_implies_Equation2520 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2520 G := λ x y z w => h x y z y w
theorem Equation2566_implies_Equation2557 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2557 G := λ x y z w => h x y z y w
theorem Equation2583_implies_Equation2574 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2574 G := λ x y z w => h x y z y w
theorem Equation2600_implies_Equation2591 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2591 G := λ x y z w => h x y z y w
theorem Equation2617_implies_Equation2608 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2608 G := λ x y z w => h x y z y w
theorem Equation2622_implies_Equation2587 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2587 G := λ x y z w => h x y z y w
theorem Equation2627_implies_Equation2591 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2591 G := λ x y z w => h x y z y w
theorem Equation2632_implies_Equation2595 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2595 G := λ x y z w => h x y z y w
theorem Equation2637_implies_Equation2591 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2591 G := λ x y z w => h x y z y w
theorem Equation2638_implies_Equation2596 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2596 G := λ x y z w => h x y z y w
theorem Equation2639_implies_Equation2597 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2597 G := λ x y z w => h x y z y w
theorem Equation2640_implies_Equation2598 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2598 G := λ x y z w => h x y z y w
theorem Equation2641_implies_Equation2597 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2597 G := λ x y z w => h x y z y w
theorem Equation2642_implies_Equation2599 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2599 G := λ x y z w => h x y z y w
theorem Equation2695_implies_Equation2686 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2686 G := λ x y z w => h x y z y w
theorem Equation2732_implies_Equation2723 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2723 G := λ x y z w => h x y z y w
theorem Equation2769_implies_Equation2760 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2760 G := λ x y z w => h x y z y w
theorem Equation2786_implies_Equation2777 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2777 G := λ x y z w => h x y z y w
theorem Equation2803_implies_Equation2794 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2794 G := λ x y z w => h x y z y w
theorem Equation2820_implies_Equation2811 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2811 G := λ x y z w => h x y z y w
theorem Equation2825_implies_Equation2790 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2790 G := λ x y z w => h x y z y w
theorem Equation2830_implies_Equation2794 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2794 G := λ x y z w => h x y z y w
theorem Equation2835_implies_Equation2798 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2798 G := λ x y z w => h x y z y w
theorem Equation2840_implies_Equation2794 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2794 G := λ x y z w => h x y z y w
theorem Equation2841_implies_Equation2799 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2799 G := λ x y z w => h x y z y w
theorem Equation2842_implies_Equation2800 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2800 G := λ x y z w => h x y z y w
theorem Equation2843_implies_Equation2801 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2801 G := λ x y z w => h x y z y w
theorem Equation2844_implies_Equation2800 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2800 G := λ x y z w => h x y z y w
theorem Equation2845_implies_Equation2802 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2802 G := λ x y z w => h x y z y w
theorem Equation2898_implies_Equation2889 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2889 G := λ x y z w => h x y z y w
theorem Equation2935_implies_Equation2926 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2926 G := λ x y z w => h x y z y w
theorem Equation2972_implies_Equation2963 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2963 G := λ x y z w => h x y z y w
theorem Equation2989_implies_Equation2980 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2980 G := λ x y z w => h x y z y w
theorem Equation3006_implies_Equation2997 (G : Type*) [Magma G] (h : Equation3006 G) : Equation2997 G := λ x y z w => h x y z y w
theorem Equation3023_implies_Equation3014 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3014 G := λ x y z w => h x y z y w
theorem Equation3028_implies_Equation2993 (G : Type*) [Magma G] (h : Equation3028 G) : Equation2993 G := λ x y z w => h x y z y w
theorem Equation3033_implies_Equation2997 (G : Type*) [Magma G] (h : Equation3033 G) : Equation2997 G := λ x y z w => h x y z y w
theorem Equation3038_implies_Equation3001 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3001 G := λ x y z w => h x y z y w
theorem Equation3043_implies_Equation2997 (G : Type*) [Magma G] (h : Equation3043 G) : Equation2997 G := λ x y z w => h x y z y w
theorem Equation3044_implies_Equation3002 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3002 G := λ x y z w => h x y z y w
theorem Equation3045_implies_Equation3003 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3003 G := λ x y z w => h x y z y w
theorem Equation3046_implies_Equation3004 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3004 G := λ x y z w => h x y z y w
theorem Equation3047_implies_Equation3003 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3003 G := λ x y z w => h x y z y w
theorem Equation3048_implies_Equation3005 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3005 G := λ x y z w => h x y z y w
theorem Equation3101_implies_Equation3092 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3092 G := λ x y z w => h x y z y w
theorem Equation3138_implies_Equation3129 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3129 G := λ x y z w => h x y z y w
theorem Equation3175_implies_Equation3166 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3166 G := λ x y z w => h x y z y w
theorem Equation3192_implies_Equation3183 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3183 G := λ x y z w => h x y z y w
theorem Equation3209_implies_Equation3200 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3200 G := λ x y z w => h x y z y w
theorem Equation3226_implies_Equation3217 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3217 G := λ x y z w => h x y z y w
theorem Equation3231_implies_Equation3196 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3196 G := λ x y z w => h x y z y w
theorem Equation3236_implies_Equation3200 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3200 G := λ x y z w => h x y z y w
theorem Equation3241_implies_Equation3204 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3204 G := λ x y z w => h x y z y w
theorem Equation3246_implies_Equation3200 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3200 G := λ x y z w => h x y z y w
theorem Equation3247_implies_Equation3205 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3205 G := λ x y z w => h x y z y w
theorem Equation3248_implies_Equation3206 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3206 G := λ x y z w => h x y z y w
theorem Equation3249_implies_Equation3207 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3207 G := λ x y z w => h x y z y w
theorem Equation3250_implies_Equation3206 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3206 G := λ x y z w => h x y z y w
theorem Equation3251_implies_Equation3208 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3208 G := λ x y z w => h x y z y w
theorem Equation3304_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3295 G := λ x y z w => h x y z y w
theorem Equation3341_implies_Equation3332 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3332 G := λ x y z w => h x y z y w
theorem Equation3378_implies_Equation3369 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3369 G := λ x y z w => h x y z y w
theorem Equation3395_implies_Equation3386 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3386 G := λ x y z w => h x y z y w
theorem Equation3412_implies_Equation3403 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3403 G := λ x y z w => h x y z y w
theorem Equation3429_implies_Equation3420 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3420 G := λ x y z w => h x y z y w
theorem Equation3434_implies_Equation3399 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3399 G := λ x y z w => h x y z y w
theorem Equation3439_implies_Equation3403 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3403 G := λ x y z w => h x y z y w
theorem Equation3444_implies_Equation3407 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3407 G := λ x y z w => h x y z y w
theorem Equation3449_implies_Equation3403 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3403 G := λ x y z w => h x y z y w
theorem Equation3450_implies_Equation3408 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3408 G := λ x y z w => h x y z y w
theorem Equation3451_implies_Equation3409 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3409 G := λ x y z w => h x y z y w
theorem Equation3452_implies_Equation3410 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3410 G := λ x y z w => h x y z y w
theorem Equation3453_implies_Equation3409 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3409 G := λ x y z w => h x y z y w
theorem Equation3454_implies_Equation3411 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3411 G := λ x y z w => h x y z y w
theorem Equation3507_implies_Equation3498 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3498 G := λ x y z w => h x y z y w
theorem Equation3544_implies_Equation3535 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3535 G := λ x y z w => h x y z y w
theorem Equation3581_implies_Equation3572 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3572 G := λ x y z w => h x y z y w
theorem Equation3598_implies_Equation3589 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3589 G := λ x y z w => h x y z y w
theorem Equation3615_implies_Equation3606 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3606 G := λ x y z w => h x y z y w
theorem Equation3632_implies_Equation3623 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3623 G := λ x y z w => h x y z y w
theorem Equation3637_implies_Equation3602 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3602 G := λ x y z w => h x y z y w
theorem Equation3642_implies_Equation3606 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3606 G := λ x y z w => h x y z y w
theorem Equation3647_implies_Equation3610 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3610 G := λ x y z w => h x y z y w
theorem Equation3652_implies_Equation3606 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3606 G := λ x y z w => h x y z y w
theorem Equation3653_implies_Equation3611 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3611 G := λ x y z w => h x y z y w
theorem Equation3654_implies_Equation3612 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3612 G := λ x y z w => h x y z y w
theorem Equation3655_implies_Equation3613 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3613 G := λ x y z w => h x y z y w
theorem Equation3656_implies_Equation3612 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3612 G := λ x y z w => h x y z y w
theorem Equation3657_implies_Equation3614 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3614 G := λ x y z w => h x y z y w
theorem Equation3710_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3701 G := λ x y z w => h x y z y w
theorem Equation3747_implies_Equation3738 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3738 G := λ x y z w => h x y z y w
theorem Equation3784_implies_Equation3775 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3775 G := λ x y z w => h x y z y w
theorem Equation3801_implies_Equation3792 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3792 G := λ x y z w => h x y z y w
theorem Equation3818_implies_Equation3809 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3809 G := λ x y z w => h x y z y w
theorem Equation3835_implies_Equation3826 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3826 G := λ x y z w => h x y z y w
theorem Equation3840_implies_Equation3805 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3805 G := λ x y z w => h x y z y w
theorem Equation3845_implies_Equation3809 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3809 G := λ x y z w => h x y z y w
theorem Equation3850_implies_Equation3813 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3813 G := λ x y z w => h x y z y w
theorem Equation3855_implies_Equation3809 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3809 G := λ x y z w => h x y z y w
theorem Equation3856_implies_Equation3814 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3814 G := λ x y z w => h x y z y w
theorem Equation3857_implies_Equation3815 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3815 G := λ x y z w => h x y z y w
theorem Equation3858_implies_Equation3816 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3816 G := λ x y z w => h x y z y w
theorem Equation3859_implies_Equation3815 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3815 G := λ x y z w => h x y z y w
theorem Equation3860_implies_Equation3817 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3817 G := λ x y z w => h x y z y w
theorem Equation3913_implies_Equation3904 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3904 G := λ x y z w => h x y z y w
theorem Equation3950_implies_Equation3941 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3941 G := λ x y z w => h x y z y w
theorem Equation3987_implies_Equation3978 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3978 G := λ x y z w => h x y z y w
theorem Equation4004_implies_Equation3995 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3995 G := λ x y z w => h x y z y w
theorem Equation4021_implies_Equation4012 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4012 G := λ x y z w => h x y z y w
theorem Equation4038_implies_Equation4029 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4029 G := λ x y z w => h x y z y w
theorem Equation4043_implies_Equation4008 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4008 G := λ x y z w => h x y z y w
theorem Equation4048_implies_Equation4012 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4012 G := λ x y z w => h x y z y w
theorem Equation4053_implies_Equation4016 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4016 G := λ x y z w => h x y z y w
theorem Equation4058_implies_Equation4012 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4012 G := λ x y z w => h x y z y w
theorem Equation4059_implies_Equation4017 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4017 G := λ x y z w => h x y z y w
theorem Equation4060_implies_Equation4018 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4018 G := λ x y z w => h x y z y w
theorem Equation4061_implies_Equation4019 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4019 G := λ x y z w => h x y z y w
theorem Equation4062_implies_Equation4018 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4018 G := λ x y z w => h x y z y w
theorem Equation4063_implies_Equation4020 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4020 G := λ x y z w => h x y z y w
theorem Equation4116_implies_Equation4107 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4107 G := λ x y z w => h x y z y w
theorem Equation4153_implies_Equation4144 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4144 G := λ x y z w => h x y z y w
theorem Equation4190_implies_Equation4181 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4181 G := λ x y z w => h x y z y w
theorem Equation4207_implies_Equation4198 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4198 G := λ x y z w => h x y z y w
theorem Equation4224_implies_Equation4215 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4215 G := λ x y z w => h x y z y w
theorem Equation4241_implies_Equation4232 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4232 G := λ x y z w => h x y z y w
theorem Equation4246_implies_Equation4211 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4211 G := λ x y z w => h x y z y w
theorem Equation4251_implies_Equation4215 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4215 G := λ x y z w => h x y z y w
theorem Equation4256_implies_Equation4219 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4219 G := λ x y z w => h x y z y w
theorem Equation4261_implies_Equation4215 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4215 G := λ x y z w => h x y z y w
theorem Equation4262_implies_Equation4220 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4220 G := λ x y z w => h x y z y w
theorem Equation4263_implies_Equation4221 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4221 G := λ x y z w => h x y z y w
theorem Equation4264_implies_Equation4222 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4222 G := λ x y z w => h x y z y w
theorem Equation4265_implies_Equation4221 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4221 G := λ x y z w => h x y z y w
theorem Equation4266_implies_Equation4223 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4223 G := λ x y z w => h x y z y w
theorem Equation4313_implies_Equation4306 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4306 G := λ x y z w => h x y z y w
theorem Equation4338_implies_Equation4333 (G : Type*) [Magma G] (h : Equation4338 G) : Equation4333 G := λ x y z w => h x y z y w
theorem Equation4356_implies_Equation4352 (G : Type*) [Magma G] (h : Equation4356 G) : Equation4352 G := λ x y z w => h x y z y w
theorem Equation4361_implies_Equation4357 (G : Type*) [Magma G] (h : Equation4361 G) : Equation4357 G := λ x y z w => h x y z y w
theorem Equation4373_implies_Equation4370 (G : Type*) [Magma G] (h : Equation4373 G) : Equation4370 G := λ x y z w => h x y z y w
theorem Equation4377_implies_Equation4365 (G : Type*) [Magma G] (h : Equation4377 G) : Equation4365 G := λ x y z w => h x y z y w
theorem Equation4378_implies_Equation4367 (G : Type*) [Magma G] (h : Equation4378 G) : Equation4367 G := λ x y z w => h x y z y w
theorem Equation4431_implies_Equation4422 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4422 G := λ x y z w => h x y z y w
theorem Equation4468_implies_Equation4459 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4459 G := λ x y z w => h x y z y w
theorem Equation4505_implies_Equation4496 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4496 G := λ x y z w => h x y z y w
theorem Equation4522_implies_Equation4513 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4513 G := λ x y z w => h x y z y w
theorem Equation4539_implies_Equation4530 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4530 G := λ x y z w => h x y z y w
theorem Equation4556_implies_Equation4547 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4547 G := λ x y z w => h x y z y w
theorem Equation4561_implies_Equation4526 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4526 G := λ x y z w => h x y z y w
theorem Equation4566_implies_Equation4530 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4530 G := λ x y z w => h x y z y w
theorem Equation4571_implies_Equation4534 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4534 G := λ x y z w => h x y z y w
theorem Equation4576_implies_Equation4530 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4530 G := λ x y z w => h x y z y w
theorem Equation4577_implies_Equation4535 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4535 G := λ x y z w => h x y z y w
theorem Equation4578_implies_Equation4536 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4536 G := λ x y z w => h x y z y w
theorem Equation4579_implies_Equation4537 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4537 G := λ x y z w => h x y z y w
theorem Equation4580_implies_Equation4536 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4536 G := λ x y z w => h x y z y w
theorem Equation4581_implies_Equation4538 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4538 G := λ x y z w => h x y z y w
theorem Equation4628_implies_Equation4621 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4621 G := λ x y z w => h x y z y w
theorem Equation4653_implies_Equation4648 (G : Type*) [Magma G] (h : Equation4653 G) : Equation4648 G := λ x y z w => h x y z y w
theorem Equation4671_implies_Equation4667 (G : Type*) [Magma G] (h : Equation4671 G) : Equation4667 G := λ x y z w => h x y z y w
theorem Equation4676_implies_Equation4672 (G : Type*) [Magma G] (h : Equation4676 G) : Equation4672 G := λ x y z w => h x y z y w
theorem Equation4688_implies_Equation4685 (G : Type*) [Magma G] (h : Equation4688 G) : Equation4685 G := λ x y z w => h x y z y w
theorem Equation4692_implies_Equation4680 (G : Type*) [Magma G] (h : Equation4692 G) : Equation4680 G := λ x y z w => h x y z y w
theorem Equation4693_implies_Equation4682 (G : Type*) [Magma G] (h : Equation4693 G) : Equation4682 G := λ x y z w => h x y z y w