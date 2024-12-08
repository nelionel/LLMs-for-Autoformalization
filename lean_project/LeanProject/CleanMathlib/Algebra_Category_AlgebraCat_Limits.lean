import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits
open CategoryTheory Limits
universe v w u t
noncomputable section
namespace AlgebraCat
variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgebraCat.{w} R)
instance semiringObj (j) : Semiring ((F ⋙ forget (AlgebraCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }
instance (F : J ⥤ AlgebraCat.{w} R) : Ring (F ⋙ forget _).sections :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)
instance (F : J ⥤ AlgebraCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)
variable [Small.{w} (F ⋙ forget (AlgebraCat.{w} R)).sections]
instance : Small.{w} (sectionsSubalgebra F) :=
  inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgebraCat.{w} R))).pt :=
  inferInstanceAs <| Ring (Shrink (sectionsSubalgebra F))
instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgebraCat.{w} R))).pt :=
  inferInstanceAs <| Algebra R (Shrink (sectionsSubalgebra F))
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgebraCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgebraCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgebraCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Types.Small.limitCone_π_app, ← Shrink.algEquiv_apply _ R,
        Types.Small.limitCone_pt, AlgEquiv.commutes]
      rfl
    }
namespace HasLimits
def limitCone : Cone F where
  pt := AlgebraCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext : 1
        exact AlgHom.coe_fn_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgebraCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp only [Functor.mapCone_π_app, forget_map, map_one, Pi.one_apply]
  · intro x y
    ext j
    simp only [Functor.comp_obj, forget_obj, Equiv.toFun_as_coe, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      Types.Small.limitCone_pt, equivShrink_symm_mul]
    apply map_mul
  · ext j
    simp only [Functor.comp_obj, forget_obj, Equiv.toFun_as_coe, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      equivShrink_symm_zero]
    apply map_zero
  · intro x y
    ext j
    simp only [Functor.comp_obj, forget_obj, Equiv.toFun_as_coe, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      Types.Small.limitCone_pt, equivShrink_symm_add]
    apply map_add
  · intro r
    simp only [← Shrink.algEquiv_symm_apply _ R, limitCone, Equiv.algebraMap_def, Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).hom.commutes r
end HasLimits
open HasLimits
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgebraCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }
instance hasLimits : HasLimits (AlgebraCat.{w} R) :=
  AlgebraCat.hasLimitsOfSize.{w, w, u}
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgebraCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgebraCat.{w} R) RingCat.{w})) }
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ (AlgebraCat R) RingCat.{w}) :=
  AlgebraCat.forget₂Ring_preservesLimitsOfSize.{w, w}
instance forget₂Module_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgebraCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgebraCat.{w} R) (ModuleCat.{w} R))) }
instance forget₂Module_preservesLimits :
    PreservesLimits (forget₂ (AlgebraCat R) (ModuleCat.{w} R)) :=
  AlgebraCat.forget₂Module_preservesLimitsOfSize.{w, w}
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgebraCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }
instance forget_preservesLimits : PreservesLimits (forget (AlgebraCat.{w} R)) :=
  AlgebraCat.forget_preservesLimitsOfSize.{w, w}
end AlgebraCat