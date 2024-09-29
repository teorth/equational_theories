import equational_theories.FreeMagma

namespace MagmaLaw

structure MagmaLaw.{u} (α : Type u) where
  lhs : FreeMagma α
  rhs : FreeMagma α

notation:50(priority:=999) "magma law: " l " ≃ " r => MagmaLaw.mk l r

universe u
variable {α : Type u} {x y z : FreeMagma α}

-- examples to test
def combine (x y : FreeMagma α) := x ⋆ (y ⋆ y)

#check magma law: x ⋆ (combine x y) ⋆ z ≃ z
-- Infoview Output: magma law: x ⋆ combine x y ⋆ z ≃ z : MagmaLaw α

#reduce magma law: x ⋆ (combine x z) ≃ y
-- Infoview Output: magma law: x ⋆ (x ⋆ (z ⋆ z)) ≃ y


end MagmaLaw
