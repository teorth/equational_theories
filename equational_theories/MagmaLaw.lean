import equational_theories.FreeMagma

namespace MagmaLaw

structure MagmaLaw.{u} (α : Type u) where
  lhs : FreeMagma α
  rhs : FreeMagma α

notation:50(priority:=999) l " ≃ " r => MagmaLaw.mk l r

universe u
variable {α : Type u} {x y z : FreeMagma α}

-- examples to test
def combine (x y : FreeMagma α) := x ⋆ (y ⋆ y)
#check x ⋆ (combine x y) ⋆ z ≃ z
#reduce x ⋆ (combine x z)


end MagmaLaw
