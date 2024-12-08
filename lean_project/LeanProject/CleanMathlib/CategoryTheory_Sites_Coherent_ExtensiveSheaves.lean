import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Preserves
universe w
namespace CategoryTheory
open Limits Presieve Opposite
variable {C : Type*} [Category C] {D : Type*} [Category D]
variable [FinitaryPreExtensive C]
class Presieve.Extensive {X : C} (R : Presieve X) : Prop where
  arrows_nonempty_isColimit : ∃ (α : Type) (_ : Finite α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))
instance {X : C} (S : Presieve X) [S.Extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.Extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive]
    (F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.IsSheafFor F  := by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).hasPullbacks :=
    (inferInstance : (ofArrows Z π).hasPullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct _ _ hc
instance {α : Type} [Finite α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).Extensive :=
  ⟨⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩
theorem extensiveTopology.isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (extensiveTopology C)
    (yoneda.obj W) := by
  rw [extensiveTopology, isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _
instance extensiveTopology.subcanonical : (extensiveTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj
variable [FinitaryExtensive C]
theorem Presieve.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (extensiveTopology C) F ↔
    Nonempty (PreservesFiniteProducts F) := by
  refine ⟨fun hF ↦ ⟨⟨fun α _ ↦ ⟨fun {K} ↦ ?_⟩⟩⟩, fun hF ↦ ?_⟩
  · rw [extensiveTopology, isSheaf_coverage] at hF
    let Z : α → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).hasPullbacks :=
      inferInstanceAs (ofArrows Z (Sigma.ι Z)).hasPullbacks
    have : ∀ (i : α), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      inferInstanceAs <| ∀ (i : α), Mono (Sigma.ι Z i)
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimit_of_iso_diagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · refine ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ?_⟩
      suffices Sigma.desc (fun i ↦ Sigma.ι Z i) = 𝟙 _ by rw [this]; infer_instance
      ext
      simp
  · let _ := hF.some
    rw [extensiveTopology, Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
    have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F
theorem Presheaf.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ D) :
    IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProducts F := by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨fun J _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
    constructor
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    have : PreservesLimit K (F.comp (coyoneda.obj ⟨E⟩)) := (h.some.preserves J).preservesLimit
    exact isLimitOfPreserves (F.comp (coyoneda.obj ⟨E⟩)) hc
  · intro _ E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts]
    exact ⟨inferInstance⟩
instance (F : Sheaf (extensiveTopology C) D) : PreservesFiniteProducts F.val :=
  (Presheaf.isSheaf_iff_preservesFiniteProducts F.val).mp F.cond
end CategoryTheory