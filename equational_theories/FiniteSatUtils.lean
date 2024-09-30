import equational_theories.Completeness
import equational_theories.Conjecture
import equational_theories.FreeMagma

theorem UnpackFxnFromFin1
  {α : Type} (f : Fin 1 → α) : ∃ (x : α), f = (fun | 0 => x) :=
  Exists.intro (f 0) $ funext (fun | 0 => refl (f 0))

theorem UnpackFxnFromFin2
  {α : Type} (f : Fin 2 → α) : ∃ (x y : α), f = (fun | 0 => x | 1 => y) :=
  Exists.intro (f 0) $ Exists.intro (f 1) $ funext (fun | 0 => refl (f 0) | 1 => refl (f 1))

theorem ConvertFromSatOneVar
  (law : MagmaLaw (Fin 1)) (G : Type) [Magma G] (sat : G ⊧ law)
  : ∀ (x : G), evalInMagma (fun | 0 => x) law.lhs = evalInMagma (fun | 0 => x) law.rhs :=
  fun x ↦ sat (fun | 0 => x)

theorem ConvertToSatOneVar
  (law : MagmaLaw (Fin 1)) (G : Type) [Magma G] (univ : ∀ (x : G), evalInMagma (fun | 0 => x) law.lhs = evalInMagma (fun | 0 => x) law.rhs)
  : G ⊧ law :=
  fun sub ↦ Exists.elim (UnpackFxnFromFin1 sub)
    (fun sub0 subeq ↦ Eq.ndrecOn (Eq.symm subeq) (univ sub0) (motive := fun f ↦ evalInMagma f law.lhs = evalInMagma f law.rhs))

theorem ConvertFromSatTwoVar
  (law : MagmaLaw (Fin 2)) (G : Type) [Magma G] (sat : G ⊧ law)
  : ∀ (x y : G), evalInMagma (fun | 0 => x | 1 => y) law.lhs = evalInMagma (fun | 0 => x | 1 => y) law.rhs :=
  fun x y ↦ sat (fun | 0 => x | 1 => y)

theorem ConvertToSatTwoVar
  (law : MagmaLaw (Fin 2)) (G : Type) [Magma G] (univ : ∀ (x y : G), evalInMagma (fun | 0 => x | 1 => y) law.lhs = evalInMagma (fun | 0 => x | 1 => y) law.rhs)
  : G ⊧ law :=
  fun sub ↦ Exists.elim (UnpackFxnFromFin2 sub)
    (fun sub0 ex2 ↦ Exists.elim ex2
    (fun sub1 subeq ↦ Eq.ndrecOn (Eq.symm subeq) (univ sub0 sub1) (motive := fun f ↦ evalInMagma f law.lhs = evalInMagma f law.rhs)))
