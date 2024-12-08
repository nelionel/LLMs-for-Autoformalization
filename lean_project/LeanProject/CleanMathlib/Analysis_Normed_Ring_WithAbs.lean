import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
open Topology
noncomputable section
variable {R S K : Type*} [Semiring R] [OrderedSemiring S] [Field K]
@[nolint unusedArguments]
def WithAbs : AbsoluteValue R S → Type _ := fun _ => R
namespace WithAbs
variable (v : AbsoluteValue R ℝ)
def equiv : WithAbs v ≃ R := Equiv.refl (WithAbs v)
instance instNonTrivial [Nontrivial R] : Nontrivial (WithAbs v) := inferInstanceAs (Nontrivial R)
instance instUnique [Unique R] : Unique (WithAbs v) := inferInstanceAs (Unique R)
instance instSemiring : Semiring (WithAbs v) := inferInstanceAs (Semiring R)
instance instRing [Ring R] : Ring (WithAbs v) := inferInstanceAs (Ring R)
instance instInhabited : Inhabited (WithAbs v) := ⟨0⟩
instance normedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  v.toNormedRing
instance normedField (v : AbsoluteValue K ℝ) : NormedField (WithAbs v) :=
  v.toNormedField
variable (x y : WithAbs v) (r s : R)
@[simp]
theorem equiv_zero : WithAbs.equiv v 0 = 0 := rfl
@[simp]
theorem equiv_symm_zero : (WithAbs.equiv v).symm 0 = 0 := rfl
@[simp]
theorem equiv_add : WithAbs.equiv v (x + y) = WithAbs.equiv v x + WithAbs.equiv v y := rfl
@[simp]
theorem equiv_symm_add :
    (WithAbs.equiv v).symm (r + s) = (WithAbs.equiv v).symm r + (WithAbs.equiv v).symm s :=
  rfl
@[simp]
theorem equiv_sub [Ring R] : WithAbs.equiv v (x - y) = WithAbs.equiv v x - WithAbs.equiv v y := rfl
@[simp]
theorem equiv_symm_sub [Ring R] :
    (WithAbs.equiv v).symm (r - s) = (WithAbs.equiv v).symm r - (WithAbs.equiv v).symm s :=
  rfl
@[simp]
theorem equiv_neg [Ring R] : WithAbs.equiv v (-x) = - WithAbs.equiv v x := rfl
@[simp]
theorem equiv_symm_neg [Ring R] : (WithAbs.equiv v).symm (-r) = - (WithAbs.equiv v).symm r := rfl
@[simp]
theorem equiv_mul : WithAbs.equiv v (x * y) = WithAbs.equiv v x * WithAbs.equiv v y := rfl
@[simp]
theorem equiv_symm_mul :
    (WithAbs.equiv v).symm (x * y) = (WithAbs.equiv v).symm x * (WithAbs.equiv v).symm y :=
  rfl
def ringEquiv : WithAbs v ≃+* R := RingEquiv.refl _
variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [NormedField L] {f : WithAbs v →+* L}
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x) : Isometry f :=
  Isometry.of_dist_eq <| fun x y => by simp only [‹NormedField L›.dist_eq, ← f.map_sub, h]; rfl
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x) :
    PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact isometry_of_comp h |>.dist_eq _ _
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace := by
  simp only [← pseudoMetricSpace_induced_of_comp h, PseudoMetricSpace.toUniformSpace]
theorem isUniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x) : IsUniformInducing f :=
  isUniformInducing_iff_uniformSpace.2 <| uniformSpace_comap_eq_of_comp h
end WithAbs
namespace AbsoluteValue
open WithAbs
variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
abbrev completion := UniformSpace.Completion (WithAbs v)
namespace Completion
instance : Coe K v.completion :=
  inferInstanceAs <| Coe (WithAbs v) (UniformSpace.Completion (WithAbs v))
variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}
abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) : v.completion →+* L :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous
theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x) (x : K) :
    extensionEmbedding_of_comp h x = f x := by
  rw [← UniformSpace.Completion.extensionHom_coe f
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous]
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x) (x y : v.completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · simp only [extensionEmbedding_of_comp_coe]
    exact UniformSpace.Completion.dist_eq x y ▸ (WithAbs.isometry_of_comp h).dist_eq _ _
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h
theorem isClosedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    IsClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).isClosedEmbedding
theorem locallyCompactSpace [LocallyCompactSpace L] (h : ∀ x, ‖f x‖ = v x)  :
    LocallyCompactSpace (v.completion) :=
  (isClosedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace
end AbsoluteValue.Completion