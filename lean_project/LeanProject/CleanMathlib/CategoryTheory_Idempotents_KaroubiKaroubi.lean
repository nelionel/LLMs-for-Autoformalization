import Mathlib.CategoryTheory.Idempotents.Karoubi
open CategoryTheory.Category
open CategoryTheory.Idempotents.Karoubi
namespace CategoryTheory
namespace Idempotents
namespace KaroubiKaroubi
variable (C : Type*) [Category C]
@[reassoc (attr := simp)]
lemma idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f := by
  simpa only [hom_ext_iff, comp_f] using P.idem
@[reassoc]
lemma p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f := by
  simpa only [hom_ext_iff, comp_f] using p_comm f
@[simps]
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj P := ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using f.comm⟩
instance [Preadditive C] : Functor.Additive (inverse C) where
@[simps!]
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by aesop_cat) (by aesop_cat))
attribute [local simp] p_comm_f in
@[simps]
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  hom := { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 }  } }
@[simps]
def equivalence : Karoubi C ≌ Karoubi (Karoubi C) where
  functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C
instance equivalence.additive_functor [Preadditive C] :
  Functor.Additive (equivalence C).functor where
instance equivalence.additive_inverse [Preadditive C] :
  Functor.Additive (equivalence C).inverse where
end KaroubiKaroubi
end Idempotents
end CategoryTheory