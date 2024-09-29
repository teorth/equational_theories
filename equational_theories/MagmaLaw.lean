import equational_theories.FreeMagma

namespace MagmaLaw

structure MagmaLaw.{u} (α : Type u) where
  lhs : FreeMagma α
  rhs : FreeMagma α

notation:50(priority:=999) l " ≃ " r => MagmaLaw.mk l r

universe u
variable {α : Type u} {x y z : FreeMagma α}
#check x ⋆ y ⋆ z ≃ z

end MagmaLaw
