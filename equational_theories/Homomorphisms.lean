import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Equiv.Basic
import equational_theories.Magma


/- # Homomorphisms -/

/-- `MagmaHom G H` is the type of functions `G → H` that preserve the operation. -/
structure MagmaHom (G H : Type*) [Magma G] [Magma H] where
  /-- The underlying function. -/
  toFun : G → H
  /-- The function preserves the operation. -/
  map_op' : ∀ x y : G, toFun (x ◇ y) = toFun x ◇ toFun y

infixr:25 " →◇ " => MagmaHom

instance MagmaHom.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G →◇ H) G H where
  coe := MagmaHom.toFun
  coe_injective' _ _ := (mk.injEq ..).mpr

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G →◇ H) (fun _ ↦ G → H) where
  coe f := f

@[ext]
lemma MagmaHom.ext {G H : Type*} [Magma G] [Magma H] {f₁ f₂ : G →◇ H}
    (hf : ∀ x : G, f₁ x = f₂ x) :
    f₁ = f₂ :=
  DFunLike.ext f₁ f₂ hf

lemma MagmaHom.map_op {G H : Type*} [Magma G] [Magma H] (f : G →◇ H) (x y : G) :
    f (x ◇ y) = f x ◇ f y :=
  f.map_op' x y

/-- Composition of magma homomorphisms. -/
def MagmaHom.comp {G H I : Type*} [Magma G] [Magma H] [Magma I] (f₁ : G →◇ H) (f₂ : H →◇ I) :
    G →◇ I where
  toFun := f₂ ∘ f₁
  map_op' x y := by
    have hxy := f₂.map_op' (f₁.toFun x) (f₁.toFun y)
    rwa [←f₁.map_op'] at hxy

lemma MagmaHom.comp_apply {G H I : Type*} [Magma G] [Magma H] [Magma I]
    (f₁ : G →◇ H) (f₂ : H →◇ I) (x : G) :
    (f₁.comp f₂) x = f₂ (f₁ x) :=
  rfl

/-- The composition of magma homomorphisms is associative. -/
lemma MagmaHom.comp_assoc {G H I J : Type*} [Magma G] [Magma H] [Magma I] [Magma J]
    (f₁ : G →◇ H) (f₂ : H →◇ I) (f₃ : I →◇ J) :
    f₁.comp (f₂.comp f₃) = (f₁.comp f₂).comp f₃ :=
  rfl

lemma MagmaHom.cancel_right {G H I : Type*} [Magma G] [Magma H] [Magma I] {f : G →◇ H}
    (hf : Function.Surjective f) (f₁ f₂ : H →◇ I) :
    f.comp f₁ = f.comp f₂ ↔ f₁ = f₂ :=
  ⟨MagmaHom.ext ∘ hf.forall.2 ∘ DFunLike.ext_iff.1, (· ▸ rfl)⟩

lemma MagmaHom.cancel_left {G H I : Type*} [Magma G] [Magma H] [Magma I] {f : H →◇ I}
    (hf : Function.Injective f) (f₁ f₂ : G →◇ H) :
    f₁.comp f = f₂.comp f ↔ f₁ = f₂ :=
  ⟨fun hf₁₂ ↦ MagmaHom.ext (fun _ ↦ hf (by rw [←MagmaHom.comp_apply, hf₁₂, MagmaHom.comp_apply])),
    (· ▸ rfl)⟩

/-- `MagmaHomClass F G H` states that `F` is a type of operation-preserving homomorphisms. -/
class MagmaHomClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [FunLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ◇ y) = f x ◇ f y

instance MagmaHom.toMagmaHomClass {G H : Type*} [Magma G] [Magma H] :
    MagmaHomClass (G →◇ H) G H where
  map_op := MagmaHom.map_op'

def MagmaHomClass.toMagmaHom {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] (f : F) :
    G →◇ H where
  toFun := f
  map_op' := map_op f

instance {F G H : Type*} [Magma G] [Magma H] [FunLike F G H] [MagmaHomClass F G H] :
    CoeTC F (G →◇ H) :=
  ⟨MagmaHomClass.toMagmaHom⟩

/-- The coercion is injective. -/
lemma MagmaHomClass.toMagmaHom_injective {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] :
    Function.Injective ((↑) : F → (G →◇ H)) :=
  fun _ _ f ↦ DFunLike.ext _ _ (fun x ↦ congr_arg (·.toFun x) f)

/-- The order of coercions does not matter. -/
lemma MagmaHom.coe_coe {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] (f : F) :
    ((f : G →◇ H) : G → H) = f :=
  rfl


/- # Isomorphisms -/

/-- `MagmaEquiv G H` is the type of equivalences `G ≃ H` that preserve the operation.
We call them magma isomorphisms. -/
structure MagmaEquiv (G H : Type*) [Magma G] [Magma H] extends G ≃ H, MagmaHom G H

infixl:25 " ≃◇ " => MagmaEquiv

instance MagmaEquiv.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G ≃◇ H) G H where
  coe := (·.toFun)
  coe_injective' _ _ := (mk.injEq ..).mpr ∘ Equiv.coe_inj.mp

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G ≃◇ H) (fun _ ↦ G → H) where
  coe e := e

@[ext]
lemma MagmaEquiv.ext {G H : Type*} [Magma G] [Magma H] {e₁ e₂ : G ≃◇ H}
    (hf : ∀ x : G, e₁ x = e₂ x) :
    e₁ = e₂ :=
  DFunLike.ext e₁ e₂ hf

/-- Composition of magma isomorphisms. -/
def MagmaEquiv.comp {G H I : Type*} [Magma G] [Magma H] [Magma I] (e₁ : G ≃◇ H) (e₂ : H ≃◇ I) :
    G ≃◇ I where
  toFun := e₂ ∘ e₁
  invFun := e₁.symm ∘ e₂.symm
  left_inv x := show e₁.symm (e₂.symm (e₂.toEquiv (e₁ x))) = x by
    rw [Equiv.symm_apply_apply]
    apply Equiv.symm_apply_apply
  right_inv x := show e₂ (e₁.toEquiv (e₁.symm (e₂.symm x))) = x by
    rw [Equiv.apply_symm_apply]
    apply Equiv.apply_symm_apply
  map_op' x y := by
    have hxy := e₂.map_op' (e₁.toFun x) (e₁.toFun y)
    rwa [←e₁.map_op'] at hxy

/-- The composition of magma isomorphisms is associative. -/
lemma MagmaEquiv.comp_assoc {G H I J : Type*} [Magma G] [Magma H] [Magma I] [Magma J]
    (e₁ : G ≃◇ H) (e₂ : H ≃◇ I) (e₃ : I ≃◇ J) :
    e₁.comp (e₂.comp e₃) = (e₁.comp e₂).comp e₃ :=
  rfl

/-- `MagmaEquivClass F G H` states that `F` is a type of operation-preserving isomorphisms. -/
class MagmaEquivClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [EquivLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ◇ y) = f x ◇ f y

def MagmaEquivClass.toMagmaEquiv {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    G ≃◇ H where
  left_inv := EquivLike.coe_symm_apply_apply f
  right_inv := EquivLike.apply_coe_symm_apply f
  map_op' := map_op f

instance {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H] [MagmaEquivClass F G H] :
    CoeTC F (G ≃◇ H) :=
  ⟨MagmaEquivClass.toMagmaEquiv⟩

/-- The coercion is injective. -/
lemma MagmaEquivClass.toMagmaEquiv_injective {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] :
    Function.Injective ((↑) : F → (G ≃◇ H)) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ congr_arg (·.toFun x) e)

/-- The order of coercions does not matter. -/
lemma MagmaEquiv.toMagmaEquiv_coe {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    ((f : G ≃◇ H) : G → H) = f :=
  rfl

instance (priority := 100) instMagmaHomClass (F : Type*) {G H : Type*} [Magma G] [Magma H]
    [EquivLike F G H] [FGH : MagmaEquivClass F G H] :
    MagmaHomClass F G H :=
  { FGH with }

/-- The order of coercions does not matter. -/
lemma MagmaEquiv.toMagmaHom_coe {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    ((f : G →◇ H) : G → H) = f :=
  rfl

/- Identity -/

/-- The identity is a magma automorphism. -/
def idMagmaEquiv (G : Type*) [Magma G] : G ≃◇ G where
  toFun := id
  invFun := id
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_op' := fun _ _ ↦ rfl

/-- Composing any magma isomorphism with the identity preserves the magma isomorphism. -/
lemma MagmaEquiv.comp_id {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) :
    e.comp (idMagmaEquiv H) = e :=
  rfl

/-- Composing the identity wíth any magma isomorphism preserves the magma isomorphism. -/
lemma MagmaEquiv.id_comp {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) :
    (idMagmaEquiv G).comp e = e :=
  rfl

/-- `MagmaEquiv` out of two `MagmaHom`s.-/
def MagmaHom.toMagmaEquiv {G H : Type*} [Magma G] [Magma H]
    {f₁ : G →◇ H} {f₂ : H →◇ G} (hfH : f₁ ∘ f₂ = idMagmaEquiv H) (hfG : f₂ ∘ f₁ = idMagmaEquiv G) :
    G ≃◇ H where
  toFun := f₁
  invFun := f₂
  left_inv x := show (f₂ ∘ f₁) x = x from hfG ▸ refl x
  right_inv x := show (f₁ ∘ f₂) x = x from hfH ▸ refl x
  map_op' := f₁.map_op'

/- Inverses -/

lemma MagmaEquiv.symm_map_op {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x y : H) :
    e.symm (x ◇ y) = e.symm x ◇ e.symm y := by -- this line refers to `Equiv.symm`
  simpa using (congr_arg e.invFun (e.map_op' (e.invFun x) (e.invFun y))).symm

/-- Inverse magma isomorphism. -/
def MagmaEquiv.symm {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) : H ≃◇ G :=
  ⟨e.toEquiv.symm, e.symm_map_op⟩

-- from now on `.symm` refers to `MagmaEquiv.symm`

lemma MagmaEquiv.symm_apply_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x : G) :
    e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

lemma MagmaEquiv.apply_symm_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (y : H) :
    e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

lemma MagmaEquiv.apply_eq_iff_symm_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x : G) (y : H) :
    e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

lemma MagmaEquiv.symm_apply_eq {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x : G) (y : H) :
    e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

lemma MagmaEquiv.eq_symm_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x : G) (y : H) :
    x = e.symm y ↔ e x = y :=
  e.toEquiv.eq_symm_apply

lemma MagmaEquiv.symm_comp_self {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

lemma MagmaEquiv.self_comp_symm {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

lemma MagmaEquiv.eq_comp_symm {G H I : Type*} [Magma G] [Magma H]
    (e : G ≃◇ H) (f : H → I) (f' : G → I) :
    f = f' ∘ e.symm ↔ f ∘ e = f' :=
  e.toEquiv.eq_comp_symm f f'

lemma MagmaEquiv.comp_symm_eq {G H I : Type*} [Magma G] [Magma H]
    (e : G ≃◇ H) (f : H → I) (f' : G → I) :
    f' ∘ e.symm = f ↔ f' = f ∘ e :=
  e.toEquiv.comp_symm_eq f f'

lemma MagmaEquiv.eq_symm_comp {G H I : Type*} [Magma G] [Magma H]
    (e : G ≃◇ H) (f : I → G) (f' : I → H) :
    f = e.symm ∘ f' ↔ e ∘ f = f' :=
  e.toEquiv.eq_symm_comp f f'

lemma MagmaEquiv.symm_comp_eq {G H I : Type*} [Magma G] [Magma H]
    (e : G ≃◇ H) (f : I → G) (f' : I → H) :
    e.symm ∘ f' = f ↔ f' = e ∘ f :=
  e.toEquiv.symm_comp_eq f f'

/-- Inversing the identity gives the identity. -/
@[simp]
lemma MagmaEquiv.symm_id {G : Type*} [Magma G] : (idMagmaEquiv G).symm = idMagmaEquiv G :=
  rfl

/-- Inversing is idempotent. -/
@[simp]
lemma MagmaEquiv.symm_symm {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) : e.symm.symm = e :=
  rfl

/-- Inverse of composition is equal to the composition of inverses swapped. -/
lemma MagmaEquiv.symm_comp {G H I : Type*} [Magma G] [Magma H] [Magma I]
    (e₁ : G ≃◇ H) (e₂ : H ≃◇ I) :
    (e₁.comp e₂).symm = e₂.symm.comp e₁.symm :=
  rfl

/-- The inversion operation is a bijection between magma isomorphisms there and back. -/
lemma MagmaEquiv.symm_bijective {G H : Type*} [Magma G] [Magma H] :
    Function.Bijective (MagmaEquiv.symm : (G ≃◇ H) → (H ≃◇ G)) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
