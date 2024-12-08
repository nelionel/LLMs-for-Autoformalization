import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Ring.Subring.Basic
library_note "change elaboration strategy with `by apply`"
open CategoryTheory
open CategoryTheory.Limits
universe v u w
noncomputable section
namespace SemiRingCat
variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u})
instance semiringObj (j) : Semiring ((F ⋙ forget SemiRingCat).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
def sectionsSubsemiring : Subsemiring (∀ j, F.obj j) :=
  letI f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  letI g : J ⥤ MonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} MonCat.{u}
  { (MonCat.sectionsSubmonoid (J := J) g),
    (AddMonCat.sectionsAddSubmonoid (J := J) f) with
    carrier := (F ⋙ forget SemiRingCat).sections }
instance sectionsSemiring : Semiring (F ⋙ forget SemiRingCat.{u}).sections :=
  (sectionsSubsemiring F).toSemiring
variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]
instance limitSemiring :
    Semiring (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat.{u})).pt :=
  letI : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
  inferInstanceAs <| Semiring (Shrink (F ⋙ forget SemiRingCat).sections)
def limitπRingHom (j) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  letI f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  letI : Small.{u} (Functor.sections (f ⋙ forget AddMonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{u}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget SemiRingCat)).π.app j }
namespace HasLimits
def limitCone : Cone F where
  pt := SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπRingHom.{v, u} F
      naturality := fun {_ _} f => RingHom.coe_inj
        ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_})
    (fun s => rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [Functor.comp_obj, Equiv.toFun_as_coe, Functor.mapCone_pt, Functor.mapCone_π_app,
          forget_map, map_mul]
    rw [← equivShrink_mul]
    rfl
  · simp only [Functor.mapCone_π_app, forget_map, map_zero]
    rfl
  · intro x y
    simp only [Functor.comp_obj, Equiv.toFun_as_coe, Functor.mapCone_pt, Functor.mapCone_π_app,
      forget_map, map_add]
    rw [← equivShrink_add]
    rfl
end HasLimits
open HasLimits
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J SemiRingCat.{u} where
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} SemiRingCat.{u} where
  has_limits_of_shape _ _ := { }
instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}
def forget₂AddCommMonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}
instance forget₂AddCommMon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat AddCommMonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }
instance forget₂AddCommMon_preservesLimits :
    PreservesLimits (forget₂ SemiRingCat AddCommMonCat.{u}) :=
  SemiRingCat.forget₂AddCommMon_preservesLimitsOfSize.{u, u}
def forget₂MonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat MonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }
instance forget₂Mon_preservesLimits : PreservesLimits (forget₂ SemiRingCat MonCat.{u}) :=
  SemiRingCat.forget₂Mon_preservesLimitsOfSize.{u, u}
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }
instance forget_preservesLimits : PreservesLimits (forget SemiRingCat.{u}) :=
  SemiRingCat.forget_preservesLimitsOfSize.{u, u}
end SemiRingCat
@[nolint checkUnivs]
abbrev CommSemiRingCatMax.{u1, u2} := CommSemiRingCat.{max u1 u2}
namespace CommSemiRingCat
variable {J : Type v} [Category.{w} J] (F : J ⥤ CommSemiRingCat.{u})
instance commSemiringObj (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) :=
  inferInstanceAs <| CommSemiring (F.obj j)
variable [Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))]
instance limitCommSemiring :
    CommSemiring (Types.Small.limitCone.{v, u} (F ⋙ forget CommSemiRingCat.{u})).pt :=
  letI : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (∀ j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
  inferInstanceAs <| CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)
instance :
    CreatesLimit F (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) :=
  letI : (forget CommSemiRingCat.{u}).ReflectsIsomorphisms :=
    CommSemiRingCat.forgetReflectIsos.{u}
  letI : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))
  let c : Cone F :=
    { pt := CommSemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun j => CommSemiRingCat.ofHom <| SemiRingCat.limitπRingHom.{v, u} (J := J)
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) j
          naturality := (SemiRingCat.HasLimits.limitCone.{v, u}
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u})).π.naturality } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit := by
        refine IsLimit.ofFaithful (forget₂ CommSemiRingCat.{u} SemiRingCat.{u})
          (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) (fun s => _) fun s => rfl }
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommSemiRingCat.{u} where
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommSemiRingCat.{u} where
instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }
instance forget₂SemiRing_preservesLimits :
    PreservesLimits (forget₂ CommSemiRingCat SemiRingCat.{u}) :=
  CommSemiRingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
instance forget_preservesLimits : PreservesLimits (forget CommSemiRingCat.{u}) :=
  CommSemiRingCat.forget_preservesLimitsOfSize.{u, u}
end CommSemiRingCat
@[nolint checkUnivs]
abbrev RingCatMax.{u1, u2} := RingCat.{max u1 u2}
namespace RingCat
variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})
instance ringObj (j) : Ring ((F ⋙ forget RingCat).obj j) :=
  inferInstanceAs <| Ring (F.obj j)
def sectionsSubring : Subring (∀ j, F.obj j) :=
  letI f : J ⥤ AddGrp.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrp.{u} ⋙
    forget₂ AddCommGrp.{u} AddGrp.{u}
  letI g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrp.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carrier := (F ⋙ forget RingCat.{u}).sections }
variable [Small.{u} (Functor.sections (F ⋙ forget RingCat.{u}))]
instance limitRing : Ring.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget RingCat.{u})).pt :=
  letI : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
  inferInstanceAs <| Ring (Shrink _)
instance : CreatesLimit F (forget₂ RingCat.{u} SemiRingCat.{u}) :=
  have : (forget₂ RingCat SemiRingCat).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  let c : Cone F :=
  { pt := RingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
      { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} (F ⋙ forget₂ _ SemiRingCat) x
        naturality := fun _ _ f => RingHom.coe_inj
          ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := by apply IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun _ => _) fun _ => rfl }
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
instance hasLimit : HasLimit F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J RingCat.{u} where
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} RingCat.{u} where
instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ RingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
      { preservesLimit := fun {F} =>
          preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }
instance forget₂SemiRing_preservesLimits : PreservesLimits (forget₂ RingCat SemiRingCat.{u}) :=
  RingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}
def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ RingCat.{u} AddCommGrp).mapCone (limitCone.{v, u} F)) := by
  letI f := F ⋙ forget₂ RingCat.{u} AddCommGrp.{u}
  letI : Small.{u} (Functor.sections (f ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrp.limitConeIsLimit.{v, u} f
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat.{u} AddCommGrp.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }
instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGrp.{u}) :=
  RingCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u}
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
instance forget_preservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forget_preservesLimitsOfSize.{u, u}
end RingCat
@[nolint checkUnivs]
abbrev CommRingCatMax.{u1, u2} := CommRingCat.{max u1 u2}
namespace CommRingCat
variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})
instance commRingObj (j) : CommRing ((F ⋙ forget CommRingCat).obj j) :=
  inferInstanceAs <| CommRing (F.obj j)
variable [Small.{u} (Functor.sections (F ⋙ forget CommRingCat))]
instance limitCommRing :
    CommRing.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget CommRingCat.{u})).pt :=
  letI : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
  inferInstanceAs <| CommRing (Shrink _)
instance :
   CreatesLimit F (forget₂ CommRingCat.{u} RingCat.{u}) :=
    have : (forget₂ CommRingCat.{u} RingCat.{u}).ReflectsIsomorphisms :=
      CategoryTheory.reflectsIsomorphisms_forget₂ _ _
    have : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
      inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
    let F' := F ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
    have : Small.{u} (Functor.sections (F' ⋙ forget _)) :=
      inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
    let c : Cone F :=
    { pt := CommRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} F' x
          naturality :=
            fun _ _ f => RingHom.coe_inj
              ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
    createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (RingCat.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{u})
          (RingCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (fun s : Cone F => ofHom <|
              (RingCat.limitConeIsLimit.{v, u}
                (F ⋙ forget₂ CommRingCat.{u} RingCat.{u})).lift
                ((forget₂ _ RingCat.{u}).mapCone s)) fun _ => rfl }
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
instance hasLimit : HasLimit F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommRingCat.{u} where
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommRingCat.{u} where
instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂Ring_preservesLimitsOfSize.{u, u}
def forget₂CommSemiRingPreservesLimitsAux :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  letI : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
    inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})
instance forget₂CommSemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }
instance forget₂CommSemiRing_preservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRingCat.{u}) :=
  CommRingCat.forget₂CommSemiRing_preservesLimitsOfSize.{u, u}
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
instance forget_preservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forget_preservesLimitsOfSize.{u, u}
end CommRingCat