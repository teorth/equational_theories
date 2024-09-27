import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation93 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ w))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation145 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ w)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation197 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ w)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation249 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ w
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation301 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ w
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation353 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ w)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation405 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ w
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation457 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation494 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (z ∘ w)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation531 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation548 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (z ∘ w)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation565 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation574 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (x ∘ w)))
def Equation578 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
def Equation582 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (z ∘ w)))
def Equation583 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ x)))
def Equation584 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ y)))
def Equation585 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ z)))
def Equation586 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ w)))
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
def Equation660 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation697 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ z) ∘ w))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation734 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation751 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ z) ∘ w))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation768 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation777 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ x) ∘ w))
def Equation781 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
def Equation785 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ z) ∘ w))
def Equation786 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ x))
def Equation787 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ y))
def Equation788 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ z))
def Equation789 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ w))
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
def Equation863 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation900 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (z ∘ w))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation937 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation954 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (z ∘ w))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation971 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation980 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (x ∘ w))
def Equation984 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
def Equation988 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (z ∘ w))
def Equation989 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ x))
def Equation990 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ y))
def Equation991 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ z))
def Equation992 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ w))
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
def Equation1066 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1103 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ w)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1140 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1157 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ w)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1174 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1183 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ w)
def Equation1187 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
def Equation1191 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ w)
def Equation1192 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ x)
def Equation1193 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ y)
def Equation1194 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ z)
def Equation1195 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ w)
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
def Equation1269 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1306 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ z) ∘ w)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1343 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1360 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ z) ∘ w)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1377 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1386 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ x) ∘ w)
def Equation1390 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
def Equation1394 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ z) ∘ w)
def Equation1395 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ x)
def Equation1396 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ y)
def Equation1397 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ z)
def Equation1398 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ w)
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
def Equation1472 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1509 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (z ∘ w))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1546 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (z ∘ w))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1589 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (x ∘ w))
def Equation1593 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
def Equation1597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (z ∘ w))
def Equation1598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ x))
def Equation1599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ y))
def Equation1600 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ z))
def Equation1601 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ w))
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
def Equation1675 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1712 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ w)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1749 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1766 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ w)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1783 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1792 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ w)
def Equation1796 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
def Equation1800 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ w)
def Equation1801 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ x)
def Equation1802 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ y)
def Equation1803 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ z)
def Equation1804 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ w)
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
def Equation1878 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1915 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ w)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1952 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1969 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ w)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1986 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation1995 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ w)
def Equation1999 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
def Equation2003 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ w)
def Equation2004 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ x)
def Equation2005 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ y)
def Equation2006 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ z)
def Equation2007 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ w)
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
def Equation2081 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2118 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ w)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2155 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2172 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ w)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2189 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2198 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ w)
def Equation2202 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
def Equation2206 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ w)
def Equation2207 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ x)
def Equation2208 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ y)
def Equation2209 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ z)
def Equation2210 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ w)
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
def Equation2284 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2321 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ w
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2358 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2375 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ w
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2392 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2401 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ w
def Equation2405 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
def Equation2409 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ w
def Equation2410 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ x
def Equation2411 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ y
def Equation2412 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ z
def Equation2413 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ w
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
def Equation2487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ w
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2561 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2578 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ w
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2595 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2604 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ w
def Equation2608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
def Equation2612 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ w
def Equation2613 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ x
def Equation2614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ y
def Equation2615 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ z
def Equation2616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ w
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
def Equation2690 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2727 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ w
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2764 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2781 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ w
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2798 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2807 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ w
def Equation2811 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
def Equation2815 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ w
def Equation2816 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ x
def Equation2817 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ y
def Equation2818 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ z
def Equation2819 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ w
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
def Equation2893 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2930 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ w
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2967 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2984 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ w
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3001 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3010 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ w
def Equation3014 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
def Equation3018 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ w
def Equation3019 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ x
def Equation3020 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ y
def Equation3021 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ z
def Equation3022 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ w
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
def Equation3096 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ w
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3133 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ w
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3170 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ w
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3187 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ w
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3204 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3213 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ w
def Equation3217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
def Equation3221 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ w
def Equation3222 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ x
def Equation3223 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ y
def Equation3224 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ z
def Equation3225 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ w
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
def Equation3299 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (z ∘ w))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3336 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (z ∘ w))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (z ∘ w))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3390 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (z ∘ w))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3416 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (x ∘ w))
def Equation3420 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
def Equation3424 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (z ∘ w))
def Equation3425 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ x))
def Equation3426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ y))
def Equation3427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ z))
def Equation3428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ w))
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
def Equation3502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ z) ∘ w)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3539 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ z) ∘ w)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3576 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ z) ∘ w)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3593 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ z) ∘ w)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3610 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3619 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ x) ∘ w)
def Equation3623 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
def Equation3627 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ z) ∘ w)
def Equation3628 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ x)
def Equation3629 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ y)
def Equation3630 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ z)
def Equation3631 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ w)
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
def Equation3705 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (z ∘ w)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3742 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (z ∘ w)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3779 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (z ∘ w)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3796 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (z ∘ w)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3813 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3822 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (x ∘ w)
def Equation3826 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
def Equation3830 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (z ∘ w)
def Equation3831 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ x)
def Equation3832 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ y)
def Equation3833 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ z)
def Equation3834 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ w)
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
def Equation3908 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ z)) ∘ w
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3945 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ z)) ∘ w
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3982 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ z)) ∘ w
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation3999 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ z)) ∘ w
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4016 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4025 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ x)) ∘ w
def Equation4029 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
def Equation4033 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ z)) ∘ w
def Equation4034 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ x
def Equation4035 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ y
def Equation4036 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ z
def Equation4037 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ w
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
def Equation4111 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ z) ∘ w
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4148 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ z) ∘ w
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4185 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ z) ∘ w
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4202 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ z) ∘ w
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4219 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4228 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ x) ∘ w
def Equation4232 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
def Equation4236 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ z) ∘ w
def Equation4237 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ x
def Equation4238 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ y
def Equation4239 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ z
def Equation4240 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ w
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
def Equation4308 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (z ∘ w)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4359 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (z ∘ w)
def Equation4361 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = x ∘ (w ∘ u)
def Equation4365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (z ∘ w)
def Equation4368 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = y ∘ (w ∘ u)
def Equation4370 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (y ∘ w)
def Equation4375 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (y ∘ u)
def Equation4426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ z) ∘ w
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4463 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ z) ∘ w
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4500 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ z) ∘ w
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ z) ∘ w
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4534 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ x) ∘ w
def Equation4547 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
def Equation4551 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ z) ∘ w
def Equation4552 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ x
def Equation4553 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ y
def Equation4554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ z
def Equation4555 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ w
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
def Equation4623 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ z) ∘ w
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4674 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ z) ∘ w
def Equation4676 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (x ∘ w) ∘ u
def Equation4680 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ z) ∘ w
def Equation4683 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (y ∘ w) ∘ u
def Equation4685 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ y) ∘ w
def Equation4690 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ y) ∘ u
theorem Equation98_implies_Equation93 (G : Type*) [Magma G] (h : Equation98 G) : Equation93 G := λ x y z w => h x y z z w
theorem Equation150_implies_Equation145 (G : Type*) [Magma G] (h : Equation150 G) : Equation145 G := λ x y z w => h x y z z w
theorem Equation202_implies_Equation197 (G : Type*) [Magma G] (h : Equation202 G) : Equation197 G := λ x y z w => h x y z z w
theorem Equation254_implies_Equation249 (G : Type*) [Magma G] (h : Equation254 G) : Equation249 G := λ x y z w => h x y z z w
theorem Equation306_implies_Equation301 (G : Type*) [Magma G] (h : Equation306 G) : Equation301 G := λ x y z w => h x y z z w
theorem Equation358_implies_Equation353 (G : Type*) [Magma G] (h : Equation358 G) : Equation353 G := λ x y z w => h x y z z w
theorem Equation410_implies_Equation405 (G : Type*) [Magma G] (h : Equation410 G) : Equation405 G := λ x y z w => h x y z z w
theorem Equation462_implies_Equation457 (G : Type*) [Magma G] (h : Equation462 G) : Equation457 G := λ x y z w => h x y z z w
theorem Equation499_implies_Equation494 (G : Type*) [Magma G] (h : Equation499 G) : Equation494 G := λ x y z w => h x y z z w
theorem Equation536_implies_Equation531 (G : Type*) [Magma G] (h : Equation536 G) : Equation531 G := λ x y z w => h x y z z w
theorem Equation553_implies_Equation548 (G : Type*) [Magma G] (h : Equation553 G) : Equation548 G := λ x y z w => h x y z z w
theorem Equation570_implies_Equation565 (G : Type*) [Magma G] (h : Equation570 G) : Equation565 G := λ x y z w => h x y z z w
theorem Equation587_implies_Equation582 (G : Type*) [Magma G] (h : Equation587 G) : Equation582 G := λ x y z w => h x y z z w
theorem Equation592_implies_Equation574 (G : Type*) [Magma G] (h : Equation592 G) : Equation574 G := λ x y z w => h x y z z w
theorem Equation597_implies_Equation578 (G : Type*) [Magma G] (h : Equation597 G) : Equation578 G := λ x y z w => h x y z z w
theorem Equation602_implies_Equation582 (G : Type*) [Magma G] (h : Equation602 G) : Equation582 G := λ x y z w => h x y z z w
theorem Equation607_implies_Equation582 (G : Type*) [Magma G] (h : Equation607 G) : Equation582 G := λ x y z w => h x y z z w
theorem Equation608_implies_Equation583 (G : Type*) [Magma G] (h : Equation608 G) : Equation583 G := λ x y z w => h x y z z w
theorem Equation609_implies_Equation584 (G : Type*) [Magma G] (h : Equation609 G) : Equation584 G := λ x y z w => h x y z z w
theorem Equation610_implies_Equation585 (G : Type*) [Magma G] (h : Equation610 G) : Equation585 G := λ x y z w => h x y z z w
theorem Equation611_implies_Equation585 (G : Type*) [Magma G] (h : Equation611 G) : Equation585 G := λ x y z w => h x y z z w
theorem Equation612_implies_Equation586 (G : Type*) [Magma G] (h : Equation612 G) : Equation586 G := λ x y z w => h x y z z w
theorem Equation665_implies_Equation660 (G : Type*) [Magma G] (h : Equation665 G) : Equation660 G := λ x y z w => h x y z z w
theorem Equation702_implies_Equation697 (G : Type*) [Magma G] (h : Equation702 G) : Equation697 G := λ x y z w => h x y z z w
theorem Equation739_implies_Equation734 (G : Type*) [Magma G] (h : Equation739 G) : Equation734 G := λ x y z w => h x y z z w
theorem Equation756_implies_Equation751 (G : Type*) [Magma G] (h : Equation756 G) : Equation751 G := λ x y z w => h x y z z w
theorem Equation773_implies_Equation768 (G : Type*) [Magma G] (h : Equation773 G) : Equation768 G := λ x y z w => h x y z z w
theorem Equation790_implies_Equation785 (G : Type*) [Magma G] (h : Equation790 G) : Equation785 G := λ x y z w => h x y z z w
theorem Equation795_implies_Equation777 (G : Type*) [Magma G] (h : Equation795 G) : Equation777 G := λ x y z w => h x y z z w
theorem Equation800_implies_Equation781 (G : Type*) [Magma G] (h : Equation800 G) : Equation781 G := λ x y z w => h x y z z w
theorem Equation805_implies_Equation785 (G : Type*) [Magma G] (h : Equation805 G) : Equation785 G := λ x y z w => h x y z z w
theorem Equation810_implies_Equation785 (G : Type*) [Magma G] (h : Equation810 G) : Equation785 G := λ x y z w => h x y z z w
theorem Equation811_implies_Equation786 (G : Type*) [Magma G] (h : Equation811 G) : Equation786 G := λ x y z w => h x y z z w
theorem Equation812_implies_Equation787 (G : Type*) [Magma G] (h : Equation812 G) : Equation787 G := λ x y z w => h x y z z w
theorem Equation813_implies_Equation788 (G : Type*) [Magma G] (h : Equation813 G) : Equation788 G := λ x y z w => h x y z z w
theorem Equation814_implies_Equation788 (G : Type*) [Magma G] (h : Equation814 G) : Equation788 G := λ x y z w => h x y z z w
theorem Equation815_implies_Equation789 (G : Type*) [Magma G] (h : Equation815 G) : Equation789 G := λ x y z w => h x y z z w
theorem Equation868_implies_Equation863 (G : Type*) [Magma G] (h : Equation868 G) : Equation863 G := λ x y z w => h x y z z w
theorem Equation905_implies_Equation900 (G : Type*) [Magma G] (h : Equation905 G) : Equation900 G := λ x y z w => h x y z z w
theorem Equation942_implies_Equation937 (G : Type*) [Magma G] (h : Equation942 G) : Equation937 G := λ x y z w => h x y z z w
theorem Equation959_implies_Equation954 (G : Type*) [Magma G] (h : Equation959 G) : Equation954 G := λ x y z w => h x y z z w
theorem Equation976_implies_Equation971 (G : Type*) [Magma G] (h : Equation976 G) : Equation971 G := λ x y z w => h x y z z w
theorem Equation993_implies_Equation988 (G : Type*) [Magma G] (h : Equation993 G) : Equation988 G := λ x y z w => h x y z z w
theorem Equation998_implies_Equation980 (G : Type*) [Magma G] (h : Equation998 G) : Equation980 G := λ x y z w => h x y z z w
theorem Equation1003_implies_Equation984 (G : Type*) [Magma G] (h : Equation1003 G) : Equation984 G := λ x y z w => h x y z z w
theorem Equation1008_implies_Equation988 (G : Type*) [Magma G] (h : Equation1008 G) : Equation988 G := λ x y z w => h x y z z w
theorem Equation1013_implies_Equation988 (G : Type*) [Magma G] (h : Equation1013 G) : Equation988 G := λ x y z w => h x y z z w
theorem Equation1014_implies_Equation989 (G : Type*) [Magma G] (h : Equation1014 G) : Equation989 G := λ x y z w => h x y z z w
theorem Equation1015_implies_Equation990 (G : Type*) [Magma G] (h : Equation1015 G) : Equation990 G := λ x y z w => h x y z z w
theorem Equation1016_implies_Equation991 (G : Type*) [Magma G] (h : Equation1016 G) : Equation991 G := λ x y z w => h x y z z w
theorem Equation1017_implies_Equation991 (G : Type*) [Magma G] (h : Equation1017 G) : Equation991 G := λ x y z w => h x y z z w
theorem Equation1018_implies_Equation992 (G : Type*) [Magma G] (h : Equation1018 G) : Equation992 G := λ x y z w => h x y z z w
theorem Equation1071_implies_Equation1066 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1066 G := λ x y z w => h x y z z w
theorem Equation1108_implies_Equation1103 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1103 G := λ x y z w => h x y z z w
theorem Equation1145_implies_Equation1140 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1140 G := λ x y z w => h x y z z w
theorem Equation1162_implies_Equation1157 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1157 G := λ x y z w => h x y z z w
theorem Equation1179_implies_Equation1174 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1174 G := λ x y z w => h x y z z w
theorem Equation1196_implies_Equation1191 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1191 G := λ x y z w => h x y z z w
theorem Equation1201_implies_Equation1183 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1183 G := λ x y z w => h x y z z w
theorem Equation1206_implies_Equation1187 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1187 G := λ x y z w => h x y z z w
theorem Equation1211_implies_Equation1191 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1191 G := λ x y z w => h x y z z w
theorem Equation1216_implies_Equation1191 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1191 G := λ x y z w => h x y z z w
theorem Equation1217_implies_Equation1192 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1192 G := λ x y z w => h x y z z w
theorem Equation1218_implies_Equation1193 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1193 G := λ x y z w => h x y z z w
theorem Equation1219_implies_Equation1194 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1194 G := λ x y z w => h x y z z w
theorem Equation1220_implies_Equation1194 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1194 G := λ x y z w => h x y z z w
theorem Equation1221_implies_Equation1195 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1195 G := λ x y z w => h x y z z w
theorem Equation1274_implies_Equation1269 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1269 G := λ x y z w => h x y z z w
theorem Equation1311_implies_Equation1306 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1306 G := λ x y z w => h x y z z w
theorem Equation1348_implies_Equation1343 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1343 G := λ x y z w => h x y z z w
theorem Equation1365_implies_Equation1360 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1360 G := λ x y z w => h x y z z w
theorem Equation1382_implies_Equation1377 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1377 G := λ x y z w => h x y z z w
theorem Equation1399_implies_Equation1394 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1394 G := λ x y z w => h x y z z w
theorem Equation1404_implies_Equation1386 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1386 G := λ x y z w => h x y z z w
theorem Equation1409_implies_Equation1390 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1390 G := λ x y z w => h x y z z w
theorem Equation1414_implies_Equation1394 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1394 G := λ x y z w => h x y z z w
theorem Equation1419_implies_Equation1394 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1394 G := λ x y z w => h x y z z w
theorem Equation1420_implies_Equation1395 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1395 G := λ x y z w => h x y z z w
theorem Equation1421_implies_Equation1396 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1396 G := λ x y z w => h x y z z w
theorem Equation1422_implies_Equation1397 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1397 G := λ x y z w => h x y z z w
theorem Equation1423_implies_Equation1397 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1397 G := λ x y z w => h x y z z w
theorem Equation1424_implies_Equation1398 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1398 G := λ x y z w => h x y z z w
theorem Equation1477_implies_Equation1472 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1472 G := λ x y z w => h x y z z w
theorem Equation1514_implies_Equation1509 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1509 G := λ x y z w => h x y z z w
theorem Equation1551_implies_Equation1546 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1546 G := λ x y z w => h x y z z w
theorem Equation1568_implies_Equation1563 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1563 G := λ x y z w => h x y z z w
theorem Equation1585_implies_Equation1580 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1580 G := λ x y z w => h x y z z w
theorem Equation1602_implies_Equation1597 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1597 G := λ x y z w => h x y z z w
theorem Equation1607_implies_Equation1589 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1589 G := λ x y z w => h x y z z w
theorem Equation1612_implies_Equation1593 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1593 G := λ x y z w => h x y z z w
theorem Equation1617_implies_Equation1597 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1597 G := λ x y z w => h x y z z w
theorem Equation1622_implies_Equation1597 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1597 G := λ x y z w => h x y z z w
theorem Equation1623_implies_Equation1598 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1598 G := λ x y z w => h x y z z w
theorem Equation1624_implies_Equation1599 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1599 G := λ x y z w => h x y z z w
theorem Equation1625_implies_Equation1600 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1600 G := λ x y z w => h x y z z w
theorem Equation1626_implies_Equation1600 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1600 G := λ x y z w => h x y z z w
theorem Equation1627_implies_Equation1601 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1601 G := λ x y z w => h x y z z w
theorem Equation1680_implies_Equation1675 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1675 G := λ x y z w => h x y z z w
theorem Equation1717_implies_Equation1712 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1712 G := λ x y z w => h x y z z w
theorem Equation1754_implies_Equation1749 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1749 G := λ x y z w => h x y z z w
theorem Equation1771_implies_Equation1766 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1766 G := λ x y z w => h x y z z w
theorem Equation1788_implies_Equation1783 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1783 G := λ x y z w => h x y z z w
theorem Equation1805_implies_Equation1800 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1800 G := λ x y z w => h x y z z w
theorem Equation1810_implies_Equation1792 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1792 G := λ x y z w => h x y z z w
theorem Equation1815_implies_Equation1796 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1796 G := λ x y z w => h x y z z w
theorem Equation1820_implies_Equation1800 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1800 G := λ x y z w => h x y z z w
theorem Equation1825_implies_Equation1800 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1800 G := λ x y z w => h x y z z w
theorem Equation1826_implies_Equation1801 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1801 G := λ x y z w => h x y z z w
theorem Equation1827_implies_Equation1802 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1802 G := λ x y z w => h x y z z w
theorem Equation1828_implies_Equation1803 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1803 G := λ x y z w => h x y z z w
theorem Equation1829_implies_Equation1803 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1803 G := λ x y z w => h x y z z w
theorem Equation1830_implies_Equation1804 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1804 G := λ x y z w => h x y z z w
theorem Equation1883_implies_Equation1878 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1878 G := λ x y z w => h x y z z w
theorem Equation1920_implies_Equation1915 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1915 G := λ x y z w => h x y z z w
theorem Equation1957_implies_Equation1952 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1952 G := λ x y z w => h x y z z w
theorem Equation1974_implies_Equation1969 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1969 G := λ x y z w => h x y z z w
theorem Equation1991_implies_Equation1986 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1986 G := λ x y z w => h x y z z w
theorem Equation2008_implies_Equation2003 (G : Type*) [Magma G] (h : Equation2008 G) : Equation2003 G := λ x y z w => h x y z z w
theorem Equation2013_implies_Equation1995 (G : Type*) [Magma G] (h : Equation2013 G) : Equation1995 G := λ x y z w => h x y z z w
theorem Equation2018_implies_Equation1999 (G : Type*) [Magma G] (h : Equation2018 G) : Equation1999 G := λ x y z w => h x y z z w
theorem Equation2023_implies_Equation2003 (G : Type*) [Magma G] (h : Equation2023 G) : Equation2003 G := λ x y z w => h x y z z w
theorem Equation2028_implies_Equation2003 (G : Type*) [Magma G] (h : Equation2028 G) : Equation2003 G := λ x y z w => h x y z z w
theorem Equation2029_implies_Equation2004 (G : Type*) [Magma G] (h : Equation2029 G) : Equation2004 G := λ x y z w => h x y z z w
theorem Equation2030_implies_Equation2005 (G : Type*) [Magma G] (h : Equation2030 G) : Equation2005 G := λ x y z w => h x y z z w
theorem Equation2031_implies_Equation2006 (G : Type*) [Magma G] (h : Equation2031 G) : Equation2006 G := λ x y z w => h x y z z w
theorem Equation2032_implies_Equation2006 (G : Type*) [Magma G] (h : Equation2032 G) : Equation2006 G := λ x y z w => h x y z z w
theorem Equation2033_implies_Equation2007 (G : Type*) [Magma G] (h : Equation2033 G) : Equation2007 G := λ x y z w => h x y z z w
theorem Equation2086_implies_Equation2081 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2081 G := λ x y z w => h x y z z w
theorem Equation2123_implies_Equation2118 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2118 G := λ x y z w => h x y z z w
theorem Equation2160_implies_Equation2155 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2155 G := λ x y z w => h x y z z w
theorem Equation2177_implies_Equation2172 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2172 G := λ x y z w => h x y z z w
theorem Equation2194_implies_Equation2189 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2189 G := λ x y z w => h x y z z w
theorem Equation2211_implies_Equation2206 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2206 G := λ x y z w => h x y z z w
theorem Equation2216_implies_Equation2198 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2198 G := λ x y z w => h x y z z w
theorem Equation2221_implies_Equation2202 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2202 G := λ x y z w => h x y z z w
theorem Equation2226_implies_Equation2206 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2206 G := λ x y z w => h x y z z w
theorem Equation2231_implies_Equation2206 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2206 G := λ x y z w => h x y z z w
theorem Equation2232_implies_Equation2207 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2207 G := λ x y z w => h x y z z w
theorem Equation2233_implies_Equation2208 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2208 G := λ x y z w => h x y z z w
theorem Equation2234_implies_Equation2209 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2209 G := λ x y z w => h x y z z w
theorem Equation2235_implies_Equation2209 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2209 G := λ x y z w => h x y z z w
theorem Equation2236_implies_Equation2210 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2210 G := λ x y z w => h x y z z w
theorem Equation2289_implies_Equation2284 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2284 G := λ x y z w => h x y z z w
theorem Equation2326_implies_Equation2321 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2321 G := λ x y z w => h x y z z w
theorem Equation2363_implies_Equation2358 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2358 G := λ x y z w => h x y z z w
theorem Equation2380_implies_Equation2375 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2375 G := λ x y z w => h x y z z w
theorem Equation2397_implies_Equation2392 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2392 G := λ x y z w => h x y z z w
theorem Equation2414_implies_Equation2409 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2409 G := λ x y z w => h x y z z w
theorem Equation2419_implies_Equation2401 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2401 G := λ x y z w => h x y z z w
theorem Equation2424_implies_Equation2405 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2405 G := λ x y z w => h x y z z w
theorem Equation2429_implies_Equation2409 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2409 G := λ x y z w => h x y z z w
theorem Equation2434_implies_Equation2409 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2409 G := λ x y z w => h x y z z w
theorem Equation2435_implies_Equation2410 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2410 G := λ x y z w => h x y z z w
theorem Equation2436_implies_Equation2411 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2411 G := λ x y z w => h x y z z w
theorem Equation2437_implies_Equation2412 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2412 G := λ x y z w => h x y z z w
theorem Equation2438_implies_Equation2412 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2412 G := λ x y z w => h x y z z w
theorem Equation2439_implies_Equation2413 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2413 G := λ x y z w => h x y z z w
theorem Equation2492_implies_Equation2487 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2487 G := λ x y z w => h x y z z w
theorem Equation2529_implies_Equation2524 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2524 G := λ x y z w => h x y z z w
theorem Equation2566_implies_Equation2561 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2561 G := λ x y z w => h x y z z w
theorem Equation2583_implies_Equation2578 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2578 G := λ x y z w => h x y z z w
theorem Equation2600_implies_Equation2595 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2595 G := λ x y z w => h x y z z w
theorem Equation2617_implies_Equation2612 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2612 G := λ x y z w => h x y z z w
theorem Equation2622_implies_Equation2604 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2604 G := λ x y z w => h x y z z w
theorem Equation2627_implies_Equation2608 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2608 G := λ x y z w => h x y z z w
theorem Equation2632_implies_Equation2612 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2612 G := λ x y z w => h x y z z w
theorem Equation2637_implies_Equation2612 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2612 G := λ x y z w => h x y z z w
theorem Equation2638_implies_Equation2613 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2613 G := λ x y z w => h x y z z w
theorem Equation2639_implies_Equation2614 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2614 G := λ x y z w => h x y z z w
theorem Equation2640_implies_Equation2615 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2615 G := λ x y z w => h x y z z w
theorem Equation2641_implies_Equation2615 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2615 G := λ x y z w => h x y z z w
theorem Equation2642_implies_Equation2616 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2616 G := λ x y z w => h x y z z w
theorem Equation2695_implies_Equation2690 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2690 G := λ x y z w => h x y z z w
theorem Equation2732_implies_Equation2727 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2727 G := λ x y z w => h x y z z w
theorem Equation2769_implies_Equation2764 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2764 G := λ x y z w => h x y z z w
theorem Equation2786_implies_Equation2781 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2781 G := λ x y z w => h x y z z w
theorem Equation2803_implies_Equation2798 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2798 G := λ x y z w => h x y z z w
theorem Equation2820_implies_Equation2815 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2815 G := λ x y z w => h x y z z w
theorem Equation2825_implies_Equation2807 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2807 G := λ x y z w => h x y z z w
theorem Equation2830_implies_Equation2811 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2811 G := λ x y z w => h x y z z w
theorem Equation2835_implies_Equation2815 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2815 G := λ x y z w => h x y z z w
theorem Equation2840_implies_Equation2815 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2815 G := λ x y z w => h x y z z w
theorem Equation2841_implies_Equation2816 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2816 G := λ x y z w => h x y z z w
theorem Equation2842_implies_Equation2817 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2817 G := λ x y z w => h x y z z w
theorem Equation2843_implies_Equation2818 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2818 G := λ x y z w => h x y z z w
theorem Equation2844_implies_Equation2818 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2818 G := λ x y z w => h x y z z w
theorem Equation2845_implies_Equation2819 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2819 G := λ x y z w => h x y z z w
theorem Equation2898_implies_Equation2893 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2893 G := λ x y z w => h x y z z w
theorem Equation2935_implies_Equation2930 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2930 G := λ x y z w => h x y z z w
theorem Equation2972_implies_Equation2967 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2967 G := λ x y z w => h x y z z w
theorem Equation2989_implies_Equation2984 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2984 G := λ x y z w => h x y z z w
theorem Equation3006_implies_Equation3001 (G : Type*) [Magma G] (h : Equation3006 G) : Equation3001 G := λ x y z w => h x y z z w
theorem Equation3023_implies_Equation3018 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3018 G := λ x y z w => h x y z z w
theorem Equation3028_implies_Equation3010 (G : Type*) [Magma G] (h : Equation3028 G) : Equation3010 G := λ x y z w => h x y z z w
theorem Equation3033_implies_Equation3014 (G : Type*) [Magma G] (h : Equation3033 G) : Equation3014 G := λ x y z w => h x y z z w
theorem Equation3038_implies_Equation3018 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3018 G := λ x y z w => h x y z z w
theorem Equation3043_implies_Equation3018 (G : Type*) [Magma G] (h : Equation3043 G) : Equation3018 G := λ x y z w => h x y z z w
theorem Equation3044_implies_Equation3019 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3019 G := λ x y z w => h x y z z w
theorem Equation3045_implies_Equation3020 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3020 G := λ x y z w => h x y z z w
theorem Equation3046_implies_Equation3021 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3021 G := λ x y z w => h x y z z w
theorem Equation3047_implies_Equation3021 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3021 G := λ x y z w => h x y z z w
theorem Equation3048_implies_Equation3022 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3022 G := λ x y z w => h x y z z w
theorem Equation3101_implies_Equation3096 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3096 G := λ x y z w => h x y z z w
theorem Equation3138_implies_Equation3133 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3133 G := λ x y z w => h x y z z w
theorem Equation3175_implies_Equation3170 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3170 G := λ x y z w => h x y z z w
theorem Equation3192_implies_Equation3187 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3187 G := λ x y z w => h x y z z w
theorem Equation3209_implies_Equation3204 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3204 G := λ x y z w => h x y z z w
theorem Equation3226_implies_Equation3221 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3221 G := λ x y z w => h x y z z w
theorem Equation3231_implies_Equation3213 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3213 G := λ x y z w => h x y z z w
theorem Equation3236_implies_Equation3217 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3217 G := λ x y z w => h x y z z w
theorem Equation3241_implies_Equation3221 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3221 G := λ x y z w => h x y z z w
theorem Equation3246_implies_Equation3221 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3221 G := λ x y z w => h x y z z w
theorem Equation3247_implies_Equation3222 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3222 G := λ x y z w => h x y z z w
theorem Equation3248_implies_Equation3223 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3223 G := λ x y z w => h x y z z w
theorem Equation3249_implies_Equation3224 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3224 G := λ x y z w => h x y z z w
theorem Equation3250_implies_Equation3224 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3224 G := λ x y z w => h x y z z w
theorem Equation3251_implies_Equation3225 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3225 G := λ x y z w => h x y z z w
theorem Equation3304_implies_Equation3299 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3299 G := λ x y z w => h x y z z w
theorem Equation3341_implies_Equation3336 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3336 G := λ x y z w => h x y z z w
theorem Equation3378_implies_Equation3373 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3373 G := λ x y z w => h x y z z w
theorem Equation3395_implies_Equation3390 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3390 G := λ x y z w => h x y z z w
theorem Equation3412_implies_Equation3407 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3407 G := λ x y z w => h x y z z w
theorem Equation3429_implies_Equation3424 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3424 G := λ x y z w => h x y z z w
theorem Equation3434_implies_Equation3416 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3416 G := λ x y z w => h x y z z w
theorem Equation3439_implies_Equation3420 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3420 G := λ x y z w => h x y z z w
theorem Equation3444_implies_Equation3424 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3424 G := λ x y z w => h x y z z w
theorem Equation3449_implies_Equation3424 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3424 G := λ x y z w => h x y z z w
theorem Equation3450_implies_Equation3425 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3425 G := λ x y z w => h x y z z w
theorem Equation3451_implies_Equation3426 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3426 G := λ x y z w => h x y z z w
theorem Equation3452_implies_Equation3427 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3427 G := λ x y z w => h x y z z w
theorem Equation3453_implies_Equation3427 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3427 G := λ x y z w => h x y z z w
theorem Equation3454_implies_Equation3428 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3428 G := λ x y z w => h x y z z w
theorem Equation3507_implies_Equation3502 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3502 G := λ x y z w => h x y z z w
theorem Equation3544_implies_Equation3539 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3539 G := λ x y z w => h x y z z w
theorem Equation3581_implies_Equation3576 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3576 G := λ x y z w => h x y z z w
theorem Equation3598_implies_Equation3593 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3593 G := λ x y z w => h x y z z w
theorem Equation3615_implies_Equation3610 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3610 G := λ x y z w => h x y z z w
theorem Equation3632_implies_Equation3627 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3627 G := λ x y z w => h x y z z w
theorem Equation3637_implies_Equation3619 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3619 G := λ x y z w => h x y z z w
theorem Equation3642_implies_Equation3623 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3623 G := λ x y z w => h x y z z w
theorem Equation3647_implies_Equation3627 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3627 G := λ x y z w => h x y z z w
theorem Equation3652_implies_Equation3627 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3627 G := λ x y z w => h x y z z w
theorem Equation3653_implies_Equation3628 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3628 G := λ x y z w => h x y z z w
theorem Equation3654_implies_Equation3629 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3629 G := λ x y z w => h x y z z w
theorem Equation3655_implies_Equation3630 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3630 G := λ x y z w => h x y z z w
theorem Equation3656_implies_Equation3630 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3630 G := λ x y z w => h x y z z w
theorem Equation3657_implies_Equation3631 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3631 G := λ x y z w => h x y z z w
theorem Equation3710_implies_Equation3705 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3705 G := λ x y z w => h x y z z w
theorem Equation3747_implies_Equation3742 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3742 G := λ x y z w => h x y z z w
theorem Equation3784_implies_Equation3779 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3779 G := λ x y z w => h x y z z w
theorem Equation3801_implies_Equation3796 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3796 G := λ x y z w => h x y z z w
theorem Equation3818_implies_Equation3813 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3813 G := λ x y z w => h x y z z w
theorem Equation3835_implies_Equation3830 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3830 G := λ x y z w => h x y z z w
theorem Equation3840_implies_Equation3822 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3822 G := λ x y z w => h x y z z w
theorem Equation3845_implies_Equation3826 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3826 G := λ x y z w => h x y z z w
theorem Equation3850_implies_Equation3830 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3830 G := λ x y z w => h x y z z w
theorem Equation3855_implies_Equation3830 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3830 G := λ x y z w => h x y z z w
theorem Equation3856_implies_Equation3831 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3831 G := λ x y z w => h x y z z w
theorem Equation3857_implies_Equation3832 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3832 G := λ x y z w => h x y z z w
theorem Equation3858_implies_Equation3833 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3833 G := λ x y z w => h x y z z w
theorem Equation3859_implies_Equation3833 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3833 G := λ x y z w => h x y z z w
theorem Equation3860_implies_Equation3834 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3834 G := λ x y z w => h x y z z w
theorem Equation3913_implies_Equation3908 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3908 G := λ x y z w => h x y z z w
theorem Equation3950_implies_Equation3945 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3945 G := λ x y z w => h x y z z w
theorem Equation3987_implies_Equation3982 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3982 G := λ x y z w => h x y z z w
theorem Equation4004_implies_Equation3999 (G : Type*) [Magma G] (h : Equation4004 G) : Equation3999 G := λ x y z w => h x y z z w
theorem Equation4021_implies_Equation4016 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4016 G := λ x y z w => h x y z z w
theorem Equation4038_implies_Equation4033 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4033 G := λ x y z w => h x y z z w
theorem Equation4043_implies_Equation4025 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4025 G := λ x y z w => h x y z z w
theorem Equation4048_implies_Equation4029 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4029 G := λ x y z w => h x y z z w
theorem Equation4053_implies_Equation4033 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4033 G := λ x y z w => h x y z z w
theorem Equation4058_implies_Equation4033 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4033 G := λ x y z w => h x y z z w
theorem Equation4059_implies_Equation4034 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4034 G := λ x y z w => h x y z z w
theorem Equation4060_implies_Equation4035 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4035 G := λ x y z w => h x y z z w
theorem Equation4061_implies_Equation4036 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4036 G := λ x y z w => h x y z z w
theorem Equation4062_implies_Equation4036 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4036 G := λ x y z w => h x y z z w
theorem Equation4063_implies_Equation4037 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4037 G := λ x y z w => h x y z z w
theorem Equation4116_implies_Equation4111 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4111 G := λ x y z w => h x y z z w
theorem Equation4153_implies_Equation4148 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4148 G := λ x y z w => h x y z z w
theorem Equation4190_implies_Equation4185 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4185 G := λ x y z w => h x y z z w
theorem Equation4207_implies_Equation4202 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4202 G := λ x y z w => h x y z z w
theorem Equation4224_implies_Equation4219 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4219 G := λ x y z w => h x y z z w
theorem Equation4241_implies_Equation4236 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4236 G := λ x y z w => h x y z z w
theorem Equation4246_implies_Equation4228 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4228 G := λ x y z w => h x y z z w
theorem Equation4251_implies_Equation4232 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4232 G := λ x y z w => h x y z z w
theorem Equation4256_implies_Equation4236 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4236 G := λ x y z w => h x y z z w
theorem Equation4261_implies_Equation4236 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4236 G := λ x y z w => h x y z z w
theorem Equation4262_implies_Equation4237 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4237 G := λ x y z w => h x y z z w
theorem Equation4263_implies_Equation4238 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4238 G := λ x y z w => h x y z z w
theorem Equation4264_implies_Equation4239 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4239 G := λ x y z w => h x y z z w
theorem Equation4265_implies_Equation4239 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4239 G := λ x y z w => h x y z z w
theorem Equation4266_implies_Equation4240 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4240 G := λ x y z w => h x y z z w
theorem Equation4313_implies_Equation4308 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4308 G := λ x y z w => h x y z z w
theorem Equation4361_implies_Equation4359 (G : Type*) [Magma G] (h : Equation4361 G) : Equation4359 G := λ x y z w => h x y z z w
theorem Equation4368_implies_Equation4365 (G : Type*) [Magma G] (h : Equation4368 G) : Equation4365 G := λ x y z w => h x y z z w
theorem Equation4375_implies_Equation4370 (G : Type*) [Magma G] (h : Equation4375 G) : Equation4370 G := λ x y z w => h x y z z w
theorem Equation4431_implies_Equation4426 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4426 G := λ x y z w => h x y z z w
theorem Equation4468_implies_Equation4463 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4463 G := λ x y z w => h x y z z w
theorem Equation4505_implies_Equation4500 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4500 G := λ x y z w => h x y z z w
theorem Equation4522_implies_Equation4517 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4517 G := λ x y z w => h x y z z w
theorem Equation4539_implies_Equation4534 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4534 G := λ x y z w => h x y z z w
theorem Equation4556_implies_Equation4551 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4551 G := λ x y z w => h x y z z w
theorem Equation4561_implies_Equation4543 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4543 G := λ x y z w => h x y z z w
theorem Equation4566_implies_Equation4547 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4547 G := λ x y z w => h x y z z w
theorem Equation4571_implies_Equation4551 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4551 G := λ x y z w => h x y z z w
theorem Equation4576_implies_Equation4551 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4551 G := λ x y z w => h x y z z w
theorem Equation4577_implies_Equation4552 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4552 G := λ x y z w => h x y z z w
theorem Equation4578_implies_Equation4553 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4553 G := λ x y z w => h x y z z w
theorem Equation4579_implies_Equation4554 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4554 G := λ x y z w => h x y z z w
theorem Equation4580_implies_Equation4554 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4554 G := λ x y z w => h x y z z w
theorem Equation4581_implies_Equation4555 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4555 G := λ x y z w => h x y z z w
theorem Equation4628_implies_Equation4623 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4623 G := λ x y z w => h x y z z w
theorem Equation4676_implies_Equation4674 (G : Type*) [Magma G] (h : Equation4676 G) : Equation4674 G := λ x y z w => h x y z z w
theorem Equation4683_implies_Equation4680 (G : Type*) [Magma G] (h : Equation4683 G) : Equation4680 G := λ x y z w => h x y z z w
theorem Equation4690_implies_Equation4685 (G : Type*) [Magma G] (h : Equation4690 G) : Equation4685 G := λ x y z w => h x y z z w