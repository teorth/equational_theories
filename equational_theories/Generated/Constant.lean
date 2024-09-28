import equational_theories.Magma
import equational_theories.AllEquations
import Mathlib.Tactic

namespace Constant

/- Equational laws that imply the operation is a constant function -/

theorem Equation41_implies_Equation46 (G: Type*) [Magma G] (h: Equation41 G) : Equation46 G :=
  fun _ _ _ _ ↦ by rwa [← h, h]

theorem Equation352_implies_Equation46 (G: Type*) [Magma G] (h: Equation352 G) : Equation46 G :=
  fun a b _ _ ↦ by rw [h a b a, ← h]

theorem Equation353_implies_Equation46 (G: Type*) [Magma G] (h: Equation353 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation356_implies_Equation46 (G: Type*) [Magma G] (h: Equation356 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation357_implies_Equation46 (G: Type*) [Magma G] (h: Equation357 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation358_implies_Equation46 (G: Type*) [Magma G] (h: Equation358 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation404_implies_Equation46 (G: Type*) [Magma G] (h: Equation404 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation405_implies_Equation46 (G: Type*) [Magma G] (h: Equation405 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation408_implies_Equation46 (G: Type*) [Magma G] (h: Equation408 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation409_implies_Equation46 (G: Type*) [Magma G] (h: Equation409 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation410_implies_Equation46 (G: Type*) [Magma G] (h: Equation410 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3423_implies_Equation46 (G: Type*) [Magma G] (h: Equation3423 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation3424_implies_Equation46 (G: Type*) [Magma G] (h: Equation3424 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3427_implies_Equation46 (G: Type*) [Magma G] (h: Equation3427 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3428_implies_Equation46 (G: Type*) [Magma G] (h: Equation3428 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3429_implies_Equation46 (G: Type*) [Magma G] (h: Equation3429 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3442_implies_Equation46 (G: Type*) [Magma G] (h: Equation3442 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3443_implies_Equation46 (G: Type*) [Magma G] (h: Equation3443 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3444_implies_Equation46 (G: Type*) [Magma G] (h: Equation3444 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3447_implies_Equation46 (G: Type*) [Magma G] (h: Equation3447 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3448_implies_Equation46 (G: Type*) [Magma G] (h: Equation3448 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3449_implies_Equation46 (G: Type*) [Magma G] (h: Equation3449 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3452_implies_Equation46 (G: Type*) [Magma G] (h: Equation3452 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3453_implies_Equation46 (G: Type*) [Magma G] (h: Equation3453 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3454_implies_Equation46 (G: Type*) [Magma G] (h: Equation3454 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3455_implies_Equation46 (G: Type*) [Magma G] (h: Equation3455 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a a, ← h]

theorem Equation3626_implies_Equation46 (G: Type*) [Magma G] (h: Equation3626 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation3627_implies_Equation46 (G: Type*) [Magma G] (h: Equation3627 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3630_implies_Equation46 (G: Type*) [Magma G] (h: Equation3630 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3631_implies_Equation46 (G: Type*) [Magma G] (h: Equation3631 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3632_implies_Equation46 (G: Type*) [Magma G] (h: Equation3632 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3645_implies_Equation46 (G: Type*) [Magma G] (h: Equation3645 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3646_implies_Equation46 (G: Type*) [Magma G] (h: Equation3646 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3647_implies_Equation46 (G: Type*) [Magma G] (h: Equation3647 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3650_implies_Equation46 (G: Type*) [Magma G] (h: Equation3650 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3651_implies_Equation46 (G: Type*) [Magma G] (h: Equation3651 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3652_implies_Equation46 (G: Type*) [Magma G] (h: Equation3652 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3655_implies_Equation46 (G: Type*) [Magma G] (h: Equation3655 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3656_implies_Equation46 (G: Type*) [Magma G] (h: Equation3656 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3657_implies_Equation46 (G: Type*) [Magma G] (h: Equation3657 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3658_implies_Equation46 (G: Type*) [Magma G] (h: Equation3658 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a a, ← h]

theorem Equation3829_implies_Equation46 (G: Type*) [Magma G] (h: Equation3829 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation3830_implies_Equation46 (G: Type*) [Magma G] (h: Equation3830 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3833_implies_Equation46 (G: Type*) [Magma G] (h: Equation3833 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3834_implies_Equation46 (G: Type*) [Magma G] (h: Equation3834 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3835_implies_Equation46 (G: Type*) [Magma G] (h: Equation3835 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3848_implies_Equation46 (G: Type*) [Magma G] (h: Equation3848 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3849_implies_Equation46 (G: Type*) [Magma G] (h: Equation3849 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3850_implies_Equation46 (G: Type*) [Magma G] (h: Equation3850 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3853_implies_Equation46 (G: Type*) [Magma G] (h: Equation3853 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3854_implies_Equation46 (G: Type*) [Magma G] (h: Equation3854 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation3855_implies_Equation46 (G: Type*) [Magma G] (h: Equation3855 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3858_implies_Equation46 (G: Type*) [Magma G] (h: Equation3858 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3859_implies_Equation46 (G: Type*) [Magma G] (h: Equation3859 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3860_implies_Equation46 (G: Type*) [Magma G] (h: Equation3860 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation3861_implies_Equation46 (G: Type*) [Magma G] (h: Equation3861 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a a, ← h]

theorem Equation4032_implies_Equation46 (G: Type*) [Magma G] (h: Equation4032 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation4033_implies_Equation46 (G: Type*) [Magma G] (h: Equation4033 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4036_implies_Equation46 (G: Type*) [Magma G] (h: Equation4036 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4037_implies_Equation46 (G: Type*) [Magma G] (h: Equation4037 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4038_implies_Equation46 (G: Type*) [Magma G] (h: Equation4038 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4051_implies_Equation46 (G: Type*) [Magma G] (h: Equation4051 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4052_implies_Equation46 (G: Type*) [Magma G] (h: Equation4052 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4053_implies_Equation46 (G: Type*) [Magma G] (h: Equation4053 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4056_implies_Equation46 (G: Type*) [Magma G] (h: Equation4056 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4057_implies_Equation46 (G: Type*) [Magma G] (h: Equation4057 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4058_implies_Equation46 (G: Type*) [Magma G] (h: Equation4058 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4061_implies_Equation46 (G: Type*) [Magma G] (h: Equation4061 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4062_implies_Equation46 (G: Type*) [Magma G] (h: Equation4062 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4063_implies_Equation46 (G: Type*) [Magma G] (h: Equation4063 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4064_implies_Equation46 (G: Type*) [Magma G] (h: Equation4064 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a a, ← h]

theorem Equation4235_implies_Equation46 (G: Type*) [Magma G] (h: Equation4235 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a, ← h]

theorem Equation4236_implies_Equation46 (G: Type*) [Magma G] (h: Equation4236 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4239_implies_Equation46 (G: Type*) [Magma G] (h: Equation4239 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4240_implies_Equation46 (G: Type*) [Magma G] (h: Equation4240 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4241_implies_Equation46 (G: Type*) [Magma G] (h: Equation4241 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4254_implies_Equation46 (G: Type*) [Magma G] (h: Equation4254 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4255_implies_Equation46 (G: Type*) [Magma G] (h: Equation4255 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4256_implies_Equation46 (G: Type*) [Magma G] (h: Equation4256 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4259_implies_Equation46 (G: Type*) [Magma G] (h: Equation4259 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4260_implies_Equation46 (G: Type*) [Magma G] (h: Equation4260 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a, ← h]

theorem Equation4261_implies_Equation46 (G: Type*) [Magma G] (h: Equation4261 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4264_implies_Equation46 (G: Type*) [Magma G] (h: Equation4264 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4265_implies_Equation46 (G: Type*) [Magma G] (h: Equation4265 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4266_implies_Equation46 (G: Type*) [Magma G] (h: Equation4266 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a, ← h]

theorem Equation4267_implies_Equation46 (G: Type*) [Magma G] (h: Equation4267 G) : Equation46 G :=
  fun a b _ _ => by rw [h a b a a a a, ← h]

end Constant
