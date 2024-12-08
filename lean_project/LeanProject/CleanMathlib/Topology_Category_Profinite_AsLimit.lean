import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.DiscreteQuotient
noncomputable section
open CategoryTheory
namespace Profinite
universe u
variable (X : Profinite.{u})
def fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where
  obj S := @FintypeCat.of S (Fintype.ofFinite S)
  map f := DiscreteQuotient.ofLE f.le
  map_comp _ _ := by ext; aesop_cat
abbrev diagram : DiscreteQuotient X ⥤ Profinite :=
  X.fintypeDiagram ⋙ FintypeCat.toProfinite
def asLimitCone : CategoryTheory.Limits.Cone X.diagram :=
  { pt := X
    π := { app := fun S => ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }
instance isIso_asLimitCone_lift : IsIso ((limitConeIsLimit.{u, u} X.diagram).lift X.asLimitCone) :=
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine DiscreteQuotient.eq_of_forall_proj_eq fun S => ?_
        apply_fun fun f : (limitCone.{u, u} X.diagram).pt => f.val S at h
        exact h
      · obtain ⟨b, hb⟩ :=
          DiscreteQuotient.exists_of_compat (fun S => a.val S) fun _ _ h => a.prop (homOfLE h)
        use b
        apply Subtype.ext
        apply funext
        rintro S
        apply hb
    )
def isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt :=
  asIso <| (limitConeIsLimit.{u, u} _).lift X.asLimitCone
def asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _ :=
  Limits.Cones.ext (isoAsLimitConeLift _) fun _ => rfl
def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm
def lim : Limits.LimitCone X.diagram :=
  ⟨X.asLimitCone, X.asLimit⟩
end Profinite