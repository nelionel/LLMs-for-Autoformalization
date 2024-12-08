import Mathlib.Algebra.Category.Grp.Basic
open CategoryTheory
namespace Grp
private instance (X : Grp) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : CommGrp) : MulOneClass X.α := X.str.toMulOneClass
private instance (X : AddGrp) : AddZeroClass X.α := X.str.toAddZeroClass
private instance (X : AddCommGrp) : AddZeroClass X.α := X.str.toAddZeroClass
@[simps]
def toAddGrp : Grp ⥤ AddGrp where
  obj X := AddGrp.of (Additive X)
  map {_} {_} := MonoidHom.toAdditive
end Grp
namespace CommGrp
@[simps]
def toAddCommGrp : CommGrp ⥤ AddCommGrp where
  obj X := AddCommGrp.of (Additive X)
  map {_} {_} := MonoidHom.toAdditive
end CommGrp
namespace AddGrp
@[simps]
def toGrp : AddGrp ⥤ Grp where
  obj X := Grp.of (Multiplicative X)
  map {_} {_} := AddMonoidHom.toMultiplicative
end AddGrp
namespace AddCommGrp
@[simps]
def toCommGrp : AddCommGrp ⥤ CommGrp where
  obj X := CommGrp.of (Multiplicative X)
  map {_} {_} := AddMonoidHom.toMultiplicative
end AddCommGrp
@[simps]
def groupAddGroupEquivalence : Grp ≌ AddGrp where
  functor := Grp.toAddGrp
  inverse := AddGrp.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps]
def commGroupAddCommGroupEquivalence : CommGrp ≌ AddCommGrp where
  functor := CommGrp.toAddCommGrp
  inverse := AddCommGrp.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _