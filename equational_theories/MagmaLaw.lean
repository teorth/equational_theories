import equational_theories.FreeMagma

structure MagmaLaw.{u} (α : Type u) where
  lhs : FreeMagma α
  rhs : FreeMagma α

notation:50(priority:=999) "magma law: " l " ≃ " r => MagmaLaw.mk l r
