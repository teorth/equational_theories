import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Equiv.Basic
import equational_theories.Magma


/- # Homomorphisms -/

/-- `MagmaHom G H` is the type of functions `G → H` that preserve the operation. -/
structure MagmaHom (G H : Type*) [Magma G] [Magma H] where
  /-- The underlying function. -/
  toFun : G → H
  /-- The function preserves the operation. -/
  map_op' : ∀ x y : G, toFun (x ∘ y) = toFun x ∘ toFun y

infixr:25 " →∘ " => MagmaHom

instance MagmaHom.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G →∘ H) G H where
  coe := MagmaHom.toFun
  coe_injective' _ _ := (mk.injEq ..).mpr

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G →∘ H) (fun _ ↦ G → H) where
  coe f := f

@[ext]
lemma MagmaHom.ext {G H : Type*} [Magma G] [Magma H] {f₁ f₂ : G →∘ H}
    (hf : ∀ x : G, f₁ x = f₂ x) :
    f₁ = f₂ :=
  DFunLike.ext f₁ f₂ hf

/-- Composition of magma homomorphisms. -/
def MagmaHom.comp {G H I : Type*} [Magma G] [Magma H] [Magma I] (f₁ : G →∘ H) (f₂ : H →∘ I) :
    G →∘ I where
  toFun := f₂ ∘ f₁
  map_op' x y := by
    have hxy := f₂.map_op' (f₁.toFun x) (f₁.toFun y)
    rwa [←f₁.map_op'] at hxy

lemma MagmaHom.comp_apply {G H I : Type*} [Magma G] [Magma H] [Magma I]
    (f₁ : G →∘ H) (f₂ : H →∘ I) (x : G) :
    (f₁.comp f₂) x = f₂ (f₁ x) :=
  rfl

/-- The composition of magma homomorphisms is associative. -/
lemma MagmaHom.comp_assoc {G H I J : Type*} [Magma G] [Magma H] [Magma I] [Magma J]
    (f₁ : G →∘ H) (f₂ : H →∘ I) (f₃ : I →∘ J) :
    f₁.comp (f₂.comp f₃) = (f₁.comp f₂).comp f₃ :=
  rfl

lemma MagmaHom.cancel_right {G H I : Type*} [Magma G] [Magma H] [Magma I] {f : G →∘ H}
    (hf : Function.Surjective f) (f₁ f₂ : H →∘ I) :
    f.comp f₁ = f.comp f₂ ↔ f₁ = f₂ :=
  ⟨MagmaHom.ext ∘ hf.forall.2 ∘ DFunLike.ext_iff.1, (· ▸ rfl)⟩

lemma MagmaHom.cancel_left {G H I : Type*} [Magma G] [Magma H] [Magma I] {f : H →∘ I}
    (hf : Function.Injective f) (f₁ f₂ : G →∘ H) :
    f₁.comp f = f₂.comp f ↔ f₁ = f₂ :=
  ⟨fun hf₁₂ ↦ MagmaHom.ext (fun _ ↦ hf (by rw [←MagmaHom.comp_apply, hf₁₂, MagmaHom.comp_apply])),
    (· ▸ rfl)⟩

/-- `MagmaHomClass F G H` states that `F` is a type of operation-preserving homomorphisms. -/
class MagmaHomClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [FunLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ∘ y) = f x ∘ f y

instance MagmaHom.toMagmaHomClass {G H : Type*} [Magma G] [Magma H] :
    MagmaHomClass (G →∘ H) G H where
  map_op := MagmaHom.map_op'

def MagmaHomClass.toMagmaHom {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] (f : F) :
    G →∘ H where
  toFun := f
  map_op' := map_op f

instance {F G H : Type*} [Magma G] [Magma H] [FunLike F G H] [MagmaHomClass F G H] :
    CoeTC F (G →∘ H) :=
  ⟨MagmaHomClass.toMagmaHom⟩

/-- The coercion is injective. -/
lemma MagmaHomClass.toMagmaHom_injective {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] :
    Function.Injective ((↑) : F → (G →∘ H)) :=
  fun _ _ f ↦ DFunLike.ext _ _ (fun x ↦ congr_arg (·.toFun x) f)

/-- The order of coercions does not matter. -/
lemma MagmaHom.coe_coe {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] (f : F) :
    ((f : G →∘ H) : G → H) = f :=
  rfl


/- # Isomorphisms -/

/-- `MagmaEquiv G H` is the type of equivalences `G ≃ H` that preserve the operation.
We call them magma isomorphisms. -/
structure MagmaEquiv (G H : Type*) [Magma G] [Magma H] extends G ≃ H, MagmaHom G H

infixl:25 " ≃∘ " => MagmaEquiv

instance MagmaEquiv.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G ≃∘ H) G H where
  coe := (·.toFun)
  coe_injective' _ _ := (mk.injEq ..).mpr ∘ Equiv.coe_inj.mp

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G ≃∘ H) (fun _ ↦ G → H) where
  coe f := f

@[ext]
lemma MagmaEquiv.ext {G H : Type*} [Magma G] [Magma H] {e₁ e₂ : G ≃∘ H}
    (hf : ∀ x : G, e₁ x = e₂ x) :
    e₁ = e₂ :=
  DFunLike.ext e₁ e₂ hf

/-- Composition of magma isomorphisms. -/
def MagmaEquiv.comp {G H I : Type*} [Magma G] [Magma H] [Magma I] (f₁ : G ≃∘ H) (f₂ : H ≃∘ I) :
    G ≃∘ I where
  toFun := f₂ ∘ f₁
  invFun := f₁.symm ∘ f₂.symm
  left_inv x := show f₁.symm (f₂.symm (f₂.toEquiv (f₁ x))) = x by
    rw [Equiv.symm_apply_apply]
    apply Equiv.symm_apply_apply
  right_inv x := show f₂ (f₁.toEquiv (f₁.symm (f₂.symm x))) = x by
    rw [Equiv.apply_symm_apply]
    apply Equiv.apply_symm_apply
  map_op' x y := by
    have hxy := f₂.map_op' (f₁.toFun x) (f₁.toFun y)
    rwa [←f₁.map_op'] at hxy

/-- The composition of magma isomorphisms is associative. -/
lemma MagmaEquiv.comp_assoc {G H I J : Type*} [Magma G] [Magma H] [Magma I] [Magma J]
    (f₁ : G ≃∘ H) (f₂ : H ≃∘ I) (f₃ : I ≃∘ J) :
    f₁.comp (f₂.comp f₃) = (f₁.comp f₂).comp f₃ :=
  rfl

/-- `MagmaEquivClass F G H` states that `F` is a type of operation-preserving isomorphisms. -/
class MagmaEquivClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [EquivLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ∘ y) = f x ∘ f y

def MagmaEquivClass.toMagmaEquiv {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    G ≃∘ H where
  left_inv := EquivLike.coe_symm_apply_apply f
  right_inv := EquivLike.apply_coe_symm_apply f
  map_op' := map_op f

instance {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H] [MagmaEquivClass F G H] :
    CoeTC F (G ≃∘ H) :=
  ⟨MagmaEquivClass.toMagmaEquiv⟩

/-- The coercion is injective. -/
lemma MagmaEquivClass.toMagmaEquiv_injective {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] :
    Function.Injective ((↑) : F → (G ≃∘ H)) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ congr_arg (·.toFun x) e)

/-- The order of coercions does not matter. -/
lemma MagmaEquiv.toMagmaEquiv_coe {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    ((f : G ≃∘ H) : G → H) = f :=
  rfl

instance (priority := 100) instMagmaHomClass (F : Type*) {G H : Type*} [Magma G] [Magma H]
    [EquivLike F G H] [FGH : MagmaEquivClass F G H] :
    MagmaHomClass F G H :=
  { FGH with }

/-- The order of coercions does not matter. -/
lemma MagmaEquiv.toMagmaHom_coe {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    ((f : G →∘ H) : G → H) = f :=
  rfl

/- Identity -/

/-- The identity is a magma automorphism. -/
def idMagmaEquiv (G : Type*) [Magma G] : G ≃∘ G where
  toFun := id
  invFun := id
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_op' := fun _ _ ↦ rfl

/-- Composing any magma isomorphism with the identity preserves the magma isomorphism. -/
lemma MagmaEquiv.comp_id {G H : Type*} [Magma G] [Magma H] (f : G ≃∘ H) :
    f.comp (idMagmaEquiv H) = f :=
  rfl

/-- Composing the identity wíth any magma isomorphism preserves the magma isomorphism. -/
lemma MagmaEquiv.id_comp {G H : Type*} [Magma G] [Magma H] (f : G ≃∘ H) :
    (idMagmaEquiv G).comp f = f :=
  rfl

/-- `MagmaEquiv` out of two `MagmaHom`s.-/
def MagmaHom.toMagmaEquiv {G H : Type*} [Magma G] [Magma H]
    {f₁ : G →∘ H} {f₂ : H →∘ G} (hfH : f₁ ∘ f₂ = idMagmaEquiv H) (hfG : f₂ ∘ f₁ = idMagmaEquiv G) :
    G ≃∘ H where
  toFun := f₁
  invFun := f₂
  left_inv x := show (f₂ ∘ f₁) x = x from hfG ▸ refl x
  right_inv x := show (f₁ ∘ f₂) x = x from hfH ▸ refl x
  map_op' := f₁.map_op'

/- Inverses -/

/-- Inverse magma isomorphism. -/
def MagmaEquiv.symm {G H : Type*} [Magma G] [Magma H] (f : G ≃∘ H) : H ≃∘ G where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  map_op' x y := by simpa using (congr_arg f.invFun (f.map_op' (f.invFun x) (f.invFun y))).symm

/-- Inversing the identity gives the identity. -/
@[simp]
lemma MagmaEquiv.symm_id {G : Type*} [Magma G] : (idMagmaEquiv G).symm = idMagmaEquiv G :=
  rfl

/-- Inversing is idempotent. -/
@[simp]
lemma MagmaEquiv.symm_symm {G H : Type*} [Magma G] [Magma H] (f : G ≃∘ H) : f.symm.symm = f :=
  rfl

/-- Inverse of composition is equal to the composition of inverses swapped. -/
lemma MagmaEquiv.symm_comp {G H I : Type*} [Magma G] [Magma H] [Magma I]
    (f₁ : G ≃∘ H) (f₂ : H ≃∘ I) :
    (f₁.comp f₂).symm = f₂.symm.comp f₁.symm :=
  rfl

/-- The inversion operation is a bijection between magma isomorphisms there and back. -/
lemma MagmaEquiv.symm_bijective {G H : Type*} [Magma G] [Magma H] :
    Function.Bijective (MagmaEquiv.symm : (G ≃∘ H) → (H ≃∘ G)) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
