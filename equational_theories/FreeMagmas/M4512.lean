import equational_theories.Completeness
import equational_theories.Equations.All
import equational_theories.Homomorphisms

variable {α : Type}

@[simp] def NonEmptyList α := {x : List α | x ≠ []}

@[simp] theorem NonEmptyList_mem (xs : NonEmptyList α) : xs.val ≠ [] := xs.prop

instance : Magma (NonEmptyList α) where
  op xs ys := ⟨xs ++ ys, by simp⟩

def singleton (x : α) : NonEmptyList α := ⟨[x], by simp⟩

theorem op_append (xs ys : NonEmptyList α) : (xs ◇ ys).val = xs.val ++ ys.val := by
  simp [Magma.op]

@[elab_as_elim]
theorem singletonAppendInduction {P : NonEmptyList α → Prop}
    (hs : ∀ x, P (singleton x)) (ha : ∀ xs ys, P xs → P ys → P (xs ◇ ys))
    : ∀ xs, P xs
  | ⟨[], h⟩ => False.elim (h rfl)
  | ⟨[x], _⟩ => hs x
  | ⟨x::x'::xs, _⟩ =>
    let tail : NonEmptyList α := ⟨x'::xs, by simp⟩
    ha (singleton x) tail (hs x) (singletonAppendInduction hs ha tail)

theorem op_assoc (x y z : NonEmptyList α) : (x ◇ y) ◇ z = x ◇ (y ◇ z) := by
  simp [Magma.op]

theorem models4512 : NonEmptyList α ⊧ Law4512 := by
  intro
  unfold satisfiesPhi
  simp [FreeMagma.evalInMagma]
  rw [op_assoc]

theorem models4512' : NonEmptyList α ⊧ {Law4512} := by
  simp [satisfiesSet]
  exact models4512

def LfEmbed4512 : α → FreeMagmaWithLaws α {Law4512} := LfEmbed {Law4512}

def foldNonEmpty (f : α → α → α) (xs : List α) (h : xs ≠ []) : α :=
  match xs with
  | [] => False.elim (h rfl)
  | x::xs =>
    match xs with
    | [] => x
    | x'::xs' => f x (foldNonEmpty f (x'::xs') (by simp))

theorem foldNonEmpty_singleton (f : α → α → α) (x : α) (h : [x] ≠ []) : foldNonEmpty f [x] h = x := by
  simp [foldNonEmpty]

theorem foldNonEmpty_cons (f : α → α → α) (x : α) (xs : List α) (h : xs ≠ []) (h2 : x::xs ≠ []) :
    foldNonEmpty f (x::xs) h2 = f x (foldNonEmpty f xs h) :=
  let x'::xs' := xs
  foldNonEmpty.eq_3 f x x' xs' h2

theorem foldNonEmpty_op4512 {G} [Magma G] (h : G ⊧ Law4512) (xs ys : List G) (hx : xs ≠ []) (hy : ys ≠ []) (hxy : xs ++ ys ≠ []) :
    foldNonEmpty Magma.op (xs ++ ys) hxy = foldNonEmpty Magma.op xs hx ◇ foldNonEmpty Magma.op ys hy := by
  have h (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := h λ | 0 => x | 1 => y | _ => z
  induction xs with
  | nil => contradiction
  | cons head tail hi =>
    simp
    cases tail with
    | nil => simp [foldNonEmpty_singleton]; rw [foldNonEmpty_cons]
    | cons head' tail' =>
      rw [foldNonEmpty, ←h]
      -- These two lines have got to be a standard tactic
      have eq_mul (x y z : G) (heq : y = z) : x ◇ y = x ◇ z := by rw [heq]
      apply eq_mul
      apply hi

-- Should go in Completeness.lean?
@[simp] def isModelSingleLaw (E : Law.NatMagmaLaw) : FreeMagmaWithLaws α {E} ⊧ E := by
  apply FreeMagmaWithLaws.isModel
  simp

theorem map_nonEmptyList {α β} (f : α → β) (xs : List α) (h : xs ≠ []) : xs.map f ≠ [] := by
  simp [h]

def inject : NonEmptyList α →◇ FreeMagmaWithLaws α {Law4512} where
  toFun xs :=
    let leaves : List (FreeMagmaWithLaws α {Law4512}) := xs.val.map LfEmbed4512
    foldNonEmpty Magma.op leaves (map_nonEmptyList LfEmbed4512 xs.val xs.prop)
  map_op' xs ys := by
    simp [foldNonEmpty_op4512, op_append xs ys]

theorem inject_singleton (a : α) (xs : NonEmptyList α) (h : xs.val = [a]) : inject xs = LfEmbed4512 a := by
  simp [inject, DFunLike.coe, h, foldNonEmpty]

def toList4512 : FreeMagmaWithLaws α {Law4512} →◇ NonEmptyList α :=
  FreeMagmaWithLaws.evalHom singleton models4512'

theorem toList4512_leaf (a : α) : toList4512 (LfEmbed4512 a) = singleton a := by
  simp [LfEmbed4512, toList4512]

def freeMagmaWith4512 : FreeMagmaWithLaws α {Law4512} ≃◇ NonEmptyList α where
  toFun := toList4512
  invFun := inject
  left_inv x := by
    refine FreeMagmaWithLaws.inductionOn x fun x => ?_
    induction x with
    | Leaf => simp [toList4512]; apply inject_singleton; rfl
    | Fork l r ih1 ih2 =>
      have h : l ⋆ r = l ◇ r := Eq.refl (l ⋆ r)
      rw [h, embed_fork, MagmaHom.map_op, MagmaHom.map_op, ih1, ih2]
  right_inv := by
    intro xs
    induction xs using singletonAppendInduction
    · rw [inject_singleton, toList4512_leaf]; rfl
    · rw [MagmaHom.map_op, MagmaHom.map_op]; simp_all
  map_op' := toList4512.map_op'
