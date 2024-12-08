import Mathlib.Algebra.Lie.Solvable
variable (R L M : Type*)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)
namespace LieAlgebra
class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥
export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L
class IsSemisimple : Prop where
  sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I
end LieAlgebra