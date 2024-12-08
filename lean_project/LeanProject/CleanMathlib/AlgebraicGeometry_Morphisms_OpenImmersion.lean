import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
universe u
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
theorem isOpenImmersion_iff_stalk {f : X ⟶ Y} : IsOpenImmersion f ↔
    IsOpenEmbedding f.base ∧ ∀ x, IsIso (f.stalkMap x) := by
  constructor
  · intro h; exact ⟨h.1, inferInstance⟩
  · rintro ⟨h₁, h₂⟩; exact IsOpenImmersion.of_stalk_iso f h₁
theorem isOpenImmersion_eq_inf :
    @IsOpenImmersion = (topologically IsOpenEmbedding) ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  ext
  exact isOpenImmersion_iff_stalk.trans
    (and_congr Iff.rfl (forall_congr' fun x ↦ ConcreteCategory.isIso_iff_bijective _))
instance : IsLocalAtTarget (stalkwise (fun f ↦ Function.Bijective f)) := by
  apply stalkwiseIsLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert (inferInstanceAs (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  exact (ConcreteCategory.isIso_iff_bijective (C := CommRingCat) _).symm
instance isOpenImmersion_isLocalAtTarget : IsLocalAtTarget @IsOpenImmersion :=
  isOpenImmersion_eq_inf ▸ inferInstance
end AlgebraicGeometry