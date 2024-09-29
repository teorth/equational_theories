import equational_theories.FreeMagma

namespace MagmaLaw

structure MagmaLaw.{u} (α : Type u) where
  lhs : FreeMagma α
  rhs : FreeMagma α

notation:50(priority:=999) l " ≃ " r => MagmaLaw.mk l r

universe u
variable {α : Type u} {x y z : FreeMagma α}

-- examples to test
def w (x y : FreeMagma α) := x ⋆ y
#check x ⋆ (w x y) ⋆ z ≃ z
#reduce x ⋆ (w x z)


end MagmaLaw
