import Mathlib.CategoryTheory.Idempotents.Karoubi
open CategoryTheory
open CategoryTheory.Category
open CategoryTheory.Idempotents.Karoubi
open CategoryTheory.Limits
namespace CategoryTheory
namespace Idempotents
variable {J C : Type*} [Category J] [Category C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)
@[reassoc (attr := simp)]
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X
variable {P Q}
@[reassoc (attr := simp)]
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X
@[reassoc (attr := simp)]
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X
@[reassoc]
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X
variable (J C)
instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  refine ⟨fun F p hp => ?_⟩
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  haveI : ∀ j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  let Y : J ⥤ C :=
    { obj := fun j => Limits.equalizer (𝟙 _) (p.app j)
      map := fun {j j'} φ =>
        equalizer.lift (Limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← Limits.equalizer.condition, comp_id]) }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _
      naturality := fun _ _ _ => by rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j =>
        equalizer.lift (p.app j) (by simpa only [comp_id] using (congr_app hp j).symm)
      naturality := fun j j' φ => equalizer.hom_ext (by simp) }
  use Y, i, e
  constructor
  · ext j
    dsimp
    rw [assoc, equalizer.lift_ι, ← equalizer.condition, id_comp, comp_id]
  · ext j
    simp
namespace KaroubiFunctorCategoryEmbedding
variable {J C}
@[simps]
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj j := ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h, reassoc_of% h] }
@[simps]
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  app j := ⟨f.f.app j, congr_app f.comm j⟩
end KaroubiFunctorCategoryEmbedding
@[simps]
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map
instance : (karoubiFunctorCategoryEmbedding J C).Full where
  map_surjective {P Q} f :=
   ⟨{ f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            simp only [comp_f] at h
            dsimp [karoubiFunctorCategoryEmbedding] at h
            erw [← h, assoc, ← P.p.naturality_assoc φ, p_comp (f.app j')] }
      comm := by
        ext j
        exact (f.app j).comm }, rfl⟩
instance : (karoubiFunctorCategoryEmbedding J C).Faithful where
  map_injective h := by
    ext j
    exact hom_ext_iff.mp (congr_app h j)
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C =
      (whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  · intro X Y f
    ext j
    dsimp [toKaroubi]
    simp only [eqToHom_app, eqToHom_refl]
    erw [comp_id, id_comp]
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      dsimp
      simp
    · intro j
      rfl
end Idempotents
end CategoryTheory