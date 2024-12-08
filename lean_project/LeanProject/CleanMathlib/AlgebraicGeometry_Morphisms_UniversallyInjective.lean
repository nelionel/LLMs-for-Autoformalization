import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.LocalAtTarget
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe v u
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
open CategoryTheory.MorphismProperty Function
@[mk_iff]
class UniversallyInjective (f : X ⟶ Y) : Prop where
  universally_injective : universally (topologically (Injective ·)) f
theorem Scheme.Hom.injective (f : X.Hom Y) [UniversallyInjective f] :
    Function.Injective f.base :=
  UniversallyInjective.universally_injective _ _ _ .of_id_snd
theorem universallyInjective_eq :
    @UniversallyInjective = universally (topologically (Injective ·)) := by
  ext X Y f; rw [universallyInjective_iff]
theorem universallyInjective_eq_diagonal :
    @UniversallyInjective = diagonal @Surjective := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x ↦ ⟨(pullback.fst f f).base x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.comp_base_apply, pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstanceAs (IsStableUnderBaseChange (diagonal @Surjective))),
      universallyInjective_eq]
    apply universally_mono
    intro X Y f hf x₁ x₂ e
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    obtain ⟨t, rfl⟩ := hf.1 t
    rw [← ht₁, ← ht₂, ← Scheme.comp_base_apply, ← Scheme.comp_base_apply, pullback.diagonal_fst,
      pullback.diagonal_snd]
theorem UniversallyInjective.iff_diagonal :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) := by
  rw [universallyInjective_eq_diagonal]; rfl
instance (priority := 900) [Mono f] : UniversallyInjective f :=
  have := (pullback.isIso_diagonal_iff f).mpr inferInstance
  (UniversallyInjective.iff_diagonal f).mpr inferInstance
theorem UniversallyInjective.respectsIso : RespectsIso @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance
instance UniversallyInjective.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance
instance universallyInjective_isStableUnderComposition :
    IsStableUnderComposition @UniversallyInjective :=
  universallyInjective_eq ▸ inferInstance
instance : MorphismProperty.IsMultiplicative @UniversallyInjective where
  id_mem _ := inferInstance
instance universallyInjective_isLocalAtTarget : IsLocalAtTarget @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance
end AlgebraicGeometry