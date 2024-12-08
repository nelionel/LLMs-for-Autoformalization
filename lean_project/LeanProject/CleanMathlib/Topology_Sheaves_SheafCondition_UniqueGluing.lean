import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.CategoryTheory.Limits.Shapes.Types
noncomputable section
open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
  TopologicalSpace TopologicalSpace.Opens Opposite
universe v u x
variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]
namespace TopCat
namespace Presheaf
section
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
variable {X : TopCat.{x}} (F : Presheaf C X) {ι : Type x} (U : ι → Opens X)
def IsCompatible (sf : ∀ i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)
def IsGluing (sf : ∀ i : ι, F.obj (op (U i))) (s : F.obj (op (iSup U))) : Prop :=
  ∀ i : ι, F.map (Opens.leSupr U i).op s = sf i
def IsSheafUniqueGluing : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X) (sf : ∀ i : ι, F.obj (op (U i))),
    IsCompatible F U sf → ∃! s : F.obj (op (iSup U)), IsGluing F U sf s
end
section TypeValued
variable {X : TopCat.{x}} {F : Presheaf (Type u) X} {ι : Type x} {U : ι → Opens X}
def objPairwiseOfFamily (sf : ∀ i, F.obj (op (U i))) :
    ∀ i, ((Pairwise.diagram U).op ⋙ F).obj i
  | ⟨Pairwise.single i⟩ => sf i
  | ⟨Pairwise.pair i j⟩ => F.map (infLELeft (U i) (U j)).op (sf i)
def IsCompatible.sectionPairwise {sf} (h : IsCompatible F U sf) :
    ((Pairwise.diagram U).op ⋙ F).sections := by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i|⟨i,j⟩) (i'|⟨i',j'⟩) (_|_|_|_)
  · exact congr_fun (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact congr_fun (G.map_id <| op <| Pairwise.pair i j) _
theorem isGluing_iff_pairwise {sf s} : IsGluing F U sf s ↔
    ∀ i, (F.mapCone (Pairwise.cocone U).op).π.app i s = objPairwiseOfFamily sf i := by
  refine ⟨fun h ↦ ?_, fun h i ↦ h (op <| Pairwise.single i)⟩
  rintro (i|⟨i,j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)
variable (F)
theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing := by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U ↦ ⟨fun h sf cpt ↦ ?_, fun h s hs ↦ ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i ↦ s <| op <| Pairwise.single i) fun i j ↦
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert h; ext (i|⟨i,j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm
theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf :=
  (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh
end TypeValued
section
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
variable [HasLimits C] [(forget C).ReflectsIsomorphisms] [PreservesLimits (forget C)]
variable {X : TopCat.{v}} (F : Presheaf C X)
theorem isSheaf_iff_isSheafUniqueGluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.trans (isSheaf_iff_isSheaf_comp (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))
end
end Presheaf
namespace Sheaf
open Presheaf
open CategoryTheory
section
attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
variable [HasLimits C] [(ConcreteCategory.forget (C := C)).ReflectsIsomorphisms]
variable [PreservesLimits (ConcreteCategory.forget (C := C))]
variable {X : TopCat.{v}} (F : Sheaf C X) {ι : Type v} (U : ι → Opens X)
theorem existsUnique_gluing (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op (iSup U)), IsGluing F.1 U sf s :=
  (isSheaf_iff_isSheafUniqueGluing F.1).mp F.cond U sf h
theorem existsUnique_gluing' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op V), ∀ i : ι, F.1.map (iUV i).op s = sf i := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← comp_apply, ← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← comp_apply, ← F.1.map_comp]
    · rw [eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl, F.1.map_id, id_apply]
    · convert gl'_spec i
@[ext]
theorem eq_of_locally_eq (s t : F.1.obj (op (iSup U)))
    (h : ∀ i, F.1.map (Opens.leSupr U i).op s = F.1.map (Opens.leSupr U i).op t) : s = t := by
  let sf : ∀ i : ι, F.1.obj (op (U i)) := fun i => F.1.map (Opens.leSupr U i).op s
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [sf, ← comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
  · symm
    apply gl_uniq
    intro i
    rw [← h]
theorem eq_of_locally_eq' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (s t : F.1.obj (op V)) (h : ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) : s = t := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← comp_apply, ← F.1.map_comp, eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl,
      F.1.map_id, id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← comp_apply, ← comp_apply, ← F.1.map_comp]
  convert h i
theorem eq_of_locally_eq₂ {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V ≤ U₁ ⊔ U₂)
    (s t : F.1.obj (op V)) (h₁ : F.1.map i₁.op s = F.1.map i₁.op t)
    (h₂ : F.1.map i₂.op s = F.1.map i₂.op t) : s = t := by
  classical
    fapply F.eq_of_locally_eq' fun t : ULift Bool => if t.1 then U₁ else U₂
    · exact fun i => if h : i.1 then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
    · refine le_trans hcover ?_
      rw [sup_le_iff]
      constructor
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up true)
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up false)
    · rintro ⟨_ | _⟩
      any_goals exact h₁
      any_goals exact h₂
end
end Sheaf
end TopCat