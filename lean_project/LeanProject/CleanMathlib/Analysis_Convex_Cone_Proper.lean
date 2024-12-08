import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.InnerProductSpace.Adjoint
open ContinuousLinearMap Filter Set
structure ProperCone (𝕜 : Type*) (E : Type*) [OrderedSemiring 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [Module 𝕜 E] extends Submodule {c : 𝕜 // 0 ≤ c} E where
  isClosed' : IsClosed (carrier : Set E)
namespace ProperCone
section Module
variable {𝕜 : Type*} [OrderedSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
abbrev toPointedCone (C : ProperCone 𝕜 E) := C.toSubmodule
attribute [coe] toPointedCone
instance : Coe (ProperCone 𝕜 E) (PointedCone 𝕜 E) :=
  ⟨toPointedCone⟩
theorem toPointedCone_injective : Function.Injective ((↑) : ProperCone 𝕜 E → PointedCone 𝕜 E) :=
  fun S T h => by cases S; cases T; congr
instance : SetLike (ProperCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := ProperCone.toPointedCone_injective (SetLike.coe_injective h)
@[ext]
theorem ext {S T : ProperCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
@[simp]
theorem mem_coe {x : E} {K : ProperCone 𝕜 E} : x ∈ (K : PointedCone 𝕜 E) ↔ x ∈ K :=
  Iff.rfl
instance instZero (K : ProperCone 𝕜 E) : Zero K := PointedCone.instZero (K.toSubmodule)
protected theorem nonempty (K : ProperCone 𝕜 E) : (K : Set E).Nonempty :=
  ⟨0, by { simp_rw [SetLike.mem_coe, ← ProperCone.mem_coe, Submodule.zero_mem] }⟩
protected theorem isClosed (K : ProperCone 𝕜 E) : IsClosed (K : Set E) :=
  K.isClosed'
end Module
section PositiveCone
variable (𝕜 E)
variable [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]
  [TopologicalSpace E] [OrderClosedTopology E]
def positive : ProperCone 𝕜 E where
  toSubmodule := PointedCone.positive 𝕜 E
  isClosed' := isClosed_Ici
@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl
@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl
end PositiveCone
section Module
variable {𝕜 : Type*} [OrderedSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T1Space E] [Module 𝕜 E]
instance : Zero (ProperCone 𝕜 E) :=
  ⟨{ toSubmodule := 0
     isClosed' := isClosed_singleton }⟩
instance : Inhabited (ProperCone 𝕜 E) :=
  ⟨0⟩
@[simp]
theorem mem_zero (x : E) : x ∈ (0 : ProperCone 𝕜 E) ↔ x = 0 :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_zero : ↑(0 : ProperCone 𝕜 E) = (0 : ConvexCone 𝕜 E) :=
  rfl
theorem pointed_zero : ((0 : ProperCone 𝕜 E) : ConvexCone 𝕜 E).Pointed := by
  simp [ConvexCone.pointed_zero]
end Module
section InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
protected theorem pointed (K : ProperCone ℝ E) : (K : ConvexCone ℝ E).Pointed :=
  (K : ConvexCone ℝ E).pointed_of_nonempty_of_isClosed K.nonempty K.isClosed
noncomputable def map (f : E →L[ℝ] F) (K : ProperCone ℝ E) : ProperCone ℝ F where
  toSubmodule := PointedCone.closure (PointedCone.map (f : E →ₗ[ℝ] F) ↑K)
  isClosed' := isClosed_closure
@[simp, norm_cast]
theorem coe_map (f : E →L[ℝ] F) (K : ProperCone ℝ E) :
    ↑(K.map f) = (PointedCone.map (f : E →ₗ[ℝ] F) ↑K).closure :=
  rfl
@[simp]
theorem mem_map {f : E →L[ℝ] F} {K : ProperCone ℝ E} {y : F} :
    y ∈ K.map f ↔ y ∈ (PointedCone.map (f : E →ₗ[ℝ] F) ↑K).closure :=
  Iff.rfl
@[simp]
theorem map_id (K : ProperCone ℝ E) : K.map (ContinuousLinearMap.id ℝ E) = K :=
  ProperCone.toPointedCone_injective <| by simpa using IsClosed.closure_eq K.isClosed
def dual (K : ProperCone ℝ E) : ProperCone ℝ E where
  toSubmodule := PointedCone.dual (K : PointedCone ℝ E)
  isClosed' := isClosed_innerDualCone _
@[simp, norm_cast]
theorem coe_dual (K : ProperCone ℝ E) : K.dual = (K : Set E).innerDualCone :=
  rfl
open scoped InnerProductSpace in
@[simp]
theorem mem_dual {K : ProperCone ℝ E} {y : E} : y ∈ dual K ↔ ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop
noncomputable def comap (f : E →L[ℝ] F) (S : ProperCone ℝ F) : ProperCone ℝ E where
  toSubmodule := PointedCone.comap (f : E →ₗ[ℝ] F) S
  isClosed' := by
    rw [PointedCone.comap]
    apply IsClosed.preimage f.2 S.isClosed
@[simp]
theorem coe_comap (f : E →L[ℝ] F) (S : ProperCone ℝ F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl
@[simp]
theorem comap_id (S : ConvexCone ℝ E) : S.comap LinearMap.id = S :=
  SetLike.coe_injective preimage_id
theorem comap_comap (g : F →L[ℝ] G) (f : E →L[ℝ] F) (S : ProperCone ℝ G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| by congr
@[simp]
theorem mem_comap {f : E →L[ℝ] F} {S : ProperCone ℝ F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
end InnerProductSpace
section CompleteSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
@[simp]
theorem dual_dual (K : ProperCone ℝ E) : K.dual.dual = K :=
  ProperCone.toPointedCone_injective <| PointedCone.toConvexCone_injective <|
    (K : ConvexCone ℝ E).innerDualCone_of_innerDualCone_eq_self K.nonempty K.isClosed
theorem hyperplane_separation (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F} :
    b ∈ K.map f ↔ ∀ y : F, adjoint f y ∈ K.dual → 0 ≤ ⟪y, b⟫_ℝ :=
  Iff.intro
    (by
      simp_rw [mem_map, PointedCone.mem_closure, PointedCone.coe_map, coe_coe,
        mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, mem_coe, mem_dual,
        adjoint_inner_right, forall_exists_index, and_imp]
      rintro seq hmem htends y hinner
      suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ from
        ge_of_tendsto'
          (Continuous.seqContinuous (Continuous.inner (@continuous_const _ _ _ _ y) continuous_id)
            htends)
          h
      intro n
      obtain ⟨_, h, hseq⟩ := hmem n
      simpa only [← hseq, real_inner_comm] using hinner h)
    (by
      intro h
      contrapose! h
      let C := @PointedCone.toConvexCone ℝ F _ _ _ (K.map f)
      obtain ⟨y, hxy, hyb⟩ :=
        @ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem
        _ _ _ _ C (K.map f).nonempty (K.map f).isClosed b h
      refine ⟨y, ?_, hyb⟩
      simp_rw [ProperCone.mem_dual, adjoint_inner_right]
      intro x hxK
      apply hxy (f x)
      simp_rw [C, coe_map]
      apply subset_closure
      simp_rw [PointedCone.toConvexCone_map, ConvexCone.coe_map, coe_coe, mem_image,
        SetLike.mem_coe]
      exact ⟨x, hxK, rfl⟩)
theorem hyperplane_separation_of_nmem (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) : ∃ y : F, adjoint f y ∈ K.dual ∧ ⟪y, b⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.hyperplane_separation]
end CompleteSpace
end ProperCone