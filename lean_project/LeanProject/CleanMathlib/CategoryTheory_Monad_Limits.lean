import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
namespace CategoryTheory
open Category
open CategoryTheory.Limits
universe v u v₁ v₂ u₁ u₂
namespace Monad
variable {C : Type u₁} [Category.{v₁} C]
variable {T : Monad C}
variable {J : Type u} [Category.{v} J]
namespace ForgetCreatesLimits
variable (D : J ⥤ Algebra T) (c : Cone (D ⋙ T.forget)) (t : IsLimit c)
@[simps]
def γ : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j := (D.obj j).a
@[simps! π_app]
def newCone : Cone (D ⋙ forget T) where
  pt := T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D
@[simps]
def conePoint : Algebra T where
  A := c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc, t.fac, newCone_π_app, ← T.η.naturality_assoc, Functor.id_map,
        (D.obj j).unit]
      dsimp; simp
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc, Category.assoc, t.fac (newCone D c), newCone_π_app, ←
        Functor.map_comp_assoc, t.fac (newCone D c), newCone_π_app, ← T.μ.naturality_assoc,
        (D.obj j).assoc, Functor.map_comp, Category.assoc]
      rfl
@[simps]
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }
@[simps]
def liftedConeIsLimit : IsLimit (liftedCone D c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc, Category.assoc, t.fac, newCone_π_app, ← Functor.map_comp_assoc,
            t.fac, Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)
end ForgetCreatesLimits
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize (forget T) where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cones.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }
theorem hasLimit_of_comp_forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)] :
    HasLimit D :=
  hasLimit_of_created D (forget T)
namespace ForgetCreatesColimits
variable {D : J ⥤ Algebra T} (c : Cocone (D ⋙ forget T)) (t : IsColimit c)
@[simps]
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j := (D.obj j).a
@[simps]
def newCocone : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  ι := γ ≫ c.ι
variable [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]
noncomputable abbrev lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt :=
  (isColimitOfPreserves _ t).desc (newCocone c)
theorem commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
  (isColimitOfPreserves _ t).fac (newCocone c) j
variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]
@[simps]
noncomputable def coconePoint : Algebra T where
  A := c.pt
  a := lambda c t
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _,
      commuting, Algebra.unit_assoc (D.obj j)]
    dsimp; simp
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app, Functor.mapCocone_ι_app,
      show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _, ←
      Functor.map_comp_assoc, commuting, Functor.map_comp, Category.assoc, commuting]
    apply (D.obj j).assoc_assoc _
@[simps]
noncomputable def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }
@[simps]
noncomputable def liftedCoconeIsColimit : IsColimit (liftedCocone c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc, ← Category.assoc, t.fac, commuting, Category.assoc, t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)
end ForgetCreatesColimits
open ForgetCreatesColimits
noncomputable instance forgetCreatesColimit (D : J ⥤ Algebra T)
    [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesColimit D (forget T) :=
  createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                dsimp
                erw [comp_id, c.w] } }
      validLift := Cocones.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }
noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] :
    CreatesColimitsOfShape J (forget T) where CreatesColimit := by infer_instance
noncomputable instance forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape := by infer_instance
theorem forget_creates_colimits_of_monad_preserves [PreservesColimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Algebra T) [HasColimit (D ⋙ forget T)] : HasColimit D :=
  hasColimit_of_created D (forget T)
end Monad
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type u} [Category.{v} J]
instance comp_comparison_forget_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] :
    HasLimit ((F ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _) :=
  @hasLimitOfIso _ _ _ _ (F ⋙ R) _ _
    (isoWhiskerLeft F (Monad.comparisonForget (monadicAdjunction R)).symm)
instance comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (monadicAdjunction R)) :=
  Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))
noncomputable def monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] :
    CreatesLimitsOfSize.{v, u} R :=
  createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))
noncomputable def monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D)
    [MonadicRightAdjoint R] [PreservesColimit (K ⋙ R) (monadicLeftAdjoint R ⋙ R)]
    [PreservesColimit ((K ⋙ R) ⋙ monadicLeftAdjoint R ⋙ R) (monadicLeftAdjoint R ⋙ R)] :
      CreatesColimit K R := by
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e
noncomputable def monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C)
    [MonadicRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R :=
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjoint_preservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩
noncomputable def monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint R]
    [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R where
  CreatesColimitsOfShape :=
    monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _
section
theorem hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] :
    HasLimit F :=
  haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R
theorem hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_reflective F R⟩
theorem hasLimits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_reflective R⟩
theorem hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D where
  has_colimit := fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      letI : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjoint_preservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) : _) ≪≫ F.rightUnitor
theorem hasColimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_reflective R⟩
lemma leftAdjoint_preservesTerminal_of_reflective (R : D ⥤ C) [Reflective R] :
    PreservesLimitsOfShape (Discrete.{v} PEmpty) (monadicLeftAdjoint R) where
  preservesLimit {K} := by
    let F := Functor.empty.{v} D
    letI : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      haveI : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      haveI : HasLimit F := hasLimit_of_reflective F R
      constructor
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit F R
      apply (isLimitOfPreserves _ (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)
end
namespace Comonad
variable {T : Comonad C}
namespace ForgetCreatesColimits'
variable (D : J ⥤ Coalgebra T) (c : Cocone (D ⋙ T.forget)) (t : IsColimit c)
@[simps]
def γ : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T  where app j := (D.obj j).a
@[simps! ι_app]
def newCocone : Cocone (D ⋙ forget T) where
  pt := T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom
@[simps]
def coconePoint : Coalgebra T where
  A := c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj, Functor.const_obj_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc, (D.obj j).counit, Category.id_comp]
  coassoc := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc, (D.obj j).coassoc, ← Functor.map_comp, t.fac (newCocone D c) j,
      newCocone_ι_app, Functor.map_comp, assoc]
@[simps]
def liftedCocone : Cocone D where
  pt := coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }
@[simps]
def liftedCoconeIsColimit : IsColimit (liftedCocone D c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc, ← Category.assoc, t.fac, newCocone_ι_app, t.fac,
            Functor.mapCocone_ι_app, Category.assoc, ← Functor.map_comp, t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)
end ForgetCreatesColimits'
noncomputable instance forgetCreatesColimit : CreatesColimitsOfSize (forget T) where
  CreatesColimitsOfShape := {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocones.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }
theorem hasColimit_of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)] :
    HasColimit D :=
  hasColimit_of_created D (forget T)
namespace ForgetCreatesLimits'
variable {D : J ⥤ Coalgebra T} (c : Cone (D ⋙ forget T)) (t : IsLimit c)
@[simps]
def γ : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j := (D.obj j).a
@[simps]
def newCone : Cone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  π := c.π ≫ γ
variable [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
noncomputable abbrev lambda : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt :=
  (isLimitOfPreserves _ t).lift (newCone c)
theorem commuting (j : J) : lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a :=
  (isLimitOfPreserves _ t).fac (newCone c) j
variable [PreservesLimit ((D ⋙ forget T) ⋙ T.toFunctor) T.toFunctor]
variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]
@[simps]
noncomputable def conePoint : Coalgebra T where
  A := c.pt
  a := lambda c t
  counit := t.hom_ext fun j ↦ by
    rw [assoc, ← show _ = _ ≫ c.π.app j from T.ε.naturality _, ← assoc, commuting, assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app, Functor.mapCone_π_app, assoc,
      ← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _, assoc, ← Functor.map_comp, commuting,
      Functor.map_comp, ← assoc, commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc,  ← assoc, ← assoc, commuting]
@[simps]
noncomputable def liftedCone : Cone D where
  pt := conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp, ← c.w]
        rfl }
@[simps]
noncomputable def liftedConeIsLimit : IsLimit (liftedCone c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc, ← t.fac, Category.assoc, t.fac, commuting, ← assoc, ← assoc, t.fac,
            assoc, ← Functor.map_comp, t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)
end ForgetCreatesLimits'
open ForgetCreatesLimits'
noncomputable instance forgetCreatesLimit (D : J ⥤ Coalgebra T)
    [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesLimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesLimit D (forget T) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                dsimp
                erw [id_comp, c.w] } }
      validLift := Cones.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }
noncomputable instance forgetCreatesLimitsOfShape [PreservesLimitsOfShape J (T : C ⥤ C)] :
    CreatesLimitsOfShape J (forget T) where CreatesLimit := by infer_instance
noncomputable instance forgetCreatesLimits [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesLimitsOfSize.{v, u} (forget T) where CreatesLimitsOfShape := by infer_instance
theorem forget_creates_limits_of_comonad_preserves [PreservesLimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Coalgebra T) [HasLimit (D ⋙ forget T)] : HasLimit D :=
  hasLimit_of_created D (forget T)
end Comonad
instance comp_comparison_forget_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] :
    HasColimit ((F ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _) :=
  @hasColimitOfIso _ _ _ _ (F ⋙ R) _ _
    (isoWhiskerLeft F (Comonad.comparisonForget (comonadicAdjunction R)).symm)
instance comp_comparison_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] : HasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R)) :=
  Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))
noncomputable def comonadicCreatesColimits (R : D ⥤ C) [ComonadicLeftAdjoint R] :
    CreatesColimitsOfSize.{v, u} R :=
  createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))
noncomputable def comonadicCreatesLimitOfPreservesLimit (R : D ⥤ C) (K : J ⥤ D)
    [ComonadicLeftAdjoint R] [PreservesLimit (K ⋙ R) (comonadicRightAdjoint R ⋙ R)]
    [PreservesLimit ((K ⋙ R) ⋙ comonadicRightAdjoint R ⋙ R) (comonadicRightAdjoint R ⋙ R)] :
      CreatesLimit K R := by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e
noncomputable def comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape (R : D ⥤ C)
    [ComonadicLeftAdjoint R] [PreservesLimitsOfShape J R] : CreatesLimitsOfShape J R :=
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjoint_preservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩
noncomputable def comonadicCreatesLimitsOfPreservesLimits (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [PreservesLimitsOfSize.{v, u} R] : CreatesLimitsOfSize.{v, u} R where
  CreatesLimitsOfShape :=
    comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _
section
theorem hasColimit_of_coreflective (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] :
    HasColimit F :=
  haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R
theorem hasColimitsOfShape_of_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R] :
    HasColimitsOfShape J D :=
  ⟨fun F => hasColimit_of_coreflective F R⟩
theorem hasColimits_of_coreflective (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Coreflective R] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩
theorem hasLimitsOfShape_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D where
  has_limit := fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      letI : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjoint_preservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) : _) )).symm
theorem hasLimits_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩
lemma rightAdjoint_preservesInitial_of_coreflective (R : D ⥤ C) [Coreflective R] :
    PreservesColimitsOfShape (Discrete.{v} PEmpty) (comonadicRightAdjoint R) where
  preservesColimit {K} := by
    let F := Functor.empty.{v} D
    letI : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      haveI : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      haveI : HasColimit F := hasColimit_of_coreflective F R
      constructor
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit F R
      apply (isColimitOfPreserves _ (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)
end
end CategoryTheory