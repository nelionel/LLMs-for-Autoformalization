import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.DirectLimit
open CategoryTheory
open CategoryTheory.Limits
universe t v w u
noncomputable section
namespace ModuleCat
variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)
instance addCommGroupObj (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| AddCommGroup (F.obj j)
instance moduleObj (j) :
    Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| Module R (F.obj j)
def sectionsSubmodule : Submodule R (∀ j, F.obj j) :=
  { AddGrp.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{w} ⋙
          forget₂ AddCommGrp AddGrp.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simp only [forget_map, Functor.comp_map, Pi.smul_apply, map_smul]
      dsimp [Functor.sections] at sh
      rw [sh f] }
instance : AddCommMonoid (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| AddCommMonoid (sectionsSubmodule F)
instance : Module R (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| Module R (sectionsSubmodule F)
section
variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]
instance : Small.{w} (sectionsSubmodule F) :=
  inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
instance limitAddCommMonoid :
    AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommMonoid (Shrink (sectionsSubmodule F))
instance limitAddCommGroup :
    AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommGroup (Shrink.{w} (sectionsSubmodule F))
instance limitModule :
    Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| Module R (Shrink (sectionsSubmodule F))
def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt →ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by
    simp only [Types.Small.limitCone_π_app,
      ← Shrink.linearEquiv_apply (F ⋙ forget (ModuleCat R)).sections R, map_smul]
    simp only [Shrink.linearEquiv_apply]
    rfl
  map_add' _ _ := by
    simp only [Types.Small.limitCone_π_app, ← Equiv.addEquiv_apply, map_add]
    rfl
namespace HasLimits
def limitCone : Cone F where
  pt := ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app := limitπLinearMap F
      naturality := fun _ _ f =>
        LinearMap.coe_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
def limitConeIsLimit : IsLimit (limitCone.{t, v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_add]
    rw [← equivShrink_add]
    rfl
  · intro r x
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_smul]
    rw [← equivShrink_smul]
    rfl
end HasLimits
open HasLimits
instance hasLimit : HasLimit F := HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }
lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape
instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, w, u}
instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}
def forget₂AddCommGroup_preservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrp).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrp) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrp.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrp.{w})
instance forget₂AddCommGroup_preservesLimit :
    PreservesLimit F (forget₂ (ModuleCat R) AddCommGrp) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (ModuleCat.{w} R) AddCommGrp.{w}) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }
instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGrp.{w}) :=
  ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦ preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }
instance forget_preservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forget_preservesLimitsOfSize.{w, w}
end
instance forget₂AddCommGroup_reflectsLimit :
    ReflectsLimit F (forget₂ (ModuleCat.{w} R) AddCommGrp) where
  reflects {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrp) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrp.hasLimit_iff_small_sections] using this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) AddCommGrp)
    exact isLimitOfReflects _ hc⟩
instance forget₂AddCommGroup_reflectsLimitOfShape :
    ReflectsLimitsOfShape J (forget₂ (ModuleCat.{w} R) AddCommGrp) where
instance forget₂AddCommGroup_reflectsLimitOfSize :
    ReflectsLimitsOfSize.{t, v} (forget₂ (ModuleCat.{w} R) AddCommGrp) where
section DirectLimit
open Module
variable {ι : Type v}
variable [dec_ι : DecidableEq ι] [Preorder ι]
variable (G : ι → Type v)
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h => f i j h]
@[simps]
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj i := ModuleCat.of R (G i)
  map hij := f _ _ hij.le
  map_id i := by
    apply LinearMap.ext
    intro x
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    apply LinearMap.ext
    intro x
    symm
    apply Module.DirectedSystem.map_map
variable [DecidableEq ι]
@[simps]
def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := Module.DirectLimit.of R ι G f
      naturality := fun _ _ hij => by
        apply LinearMap.ext
        intro x
        exact DirectLimit.of_f }
@[simps]
def directLimitIsColimit [IsDirected ι (· ≤ ·)] : IsColimit (directLimitCocone G f) where
  desc s :=
    DirectLimit.lift R ι G f s.ι.app fun i j h x => by
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    apply LinearMap.ext
    intro x
    dsimp only [directLimitCocone, CategoryStruct.comp]
    rw [LinearMap.comp_apply]
    apply DirectLimit.lift_of
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        LinearMap.comp m (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i) := by
      funext i
      rw [← h]
      rfl
    apply LinearMap.ext
    intro x
    simp only [this]
    apply Module.DirectLimit.lift_unique
end DirectLimit
end ModuleCat