import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Tactic.Module
open RCLike
open scoped ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
variable (𝕜) {E}
theorem InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm 𝕜⟩
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm ℝ⟩
variable [NormedSpace 𝕜 E]
local notation "𝓚" => algebraMap ℝ 𝕜
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)
namespace InnerProductSpaceable
variable {𝕜} (E)
private def innerProp' (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y
variable {E}
theorem _root_.Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold _root_.inner_
  fun_prop
theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add, map_zero, map_mul,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x using 2; module
  rw [h₁, h₂]
  ring
theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x, norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y) using 2
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm using 2
    linear_combination (norm := module) -hI' • y
  rw [h₁, h₂]
  ring
variable [InnerProductSpaceable E]
private theorem add_left_aux1 (x y z : E) :
    ‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖
    = 2 * (‖x + y + z‖ * ‖x + y + z‖ + ‖x - z‖ * ‖x - z‖) := by
  convert parallelogram_identity (x + y + z) (x - z) using 4 <;> abel
private theorem add_left_aux2 (x y z : E) : ‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖
    = 2 * (‖x + y - z‖ * ‖x + y - z‖ + ‖x + z‖ * ‖x + z‖) := by
  convert parallelogram_identity (x + y - z) (x + z) using 4 <;> abel
private theorem add_left_aux3 (y z : E) :
    ‖2 • z + y‖ * ‖2 • z + y‖ + ‖y‖ * ‖y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity (y + z) z using 4 <;> abel
private theorem add_left_aux4 (y z : E) :
    ‖y‖ * ‖y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity (y - z) z using 4 <;> abel
variable (𝕜)
private theorem add_left_aux5 (x y z : E) :
    ‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖
    + ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖
    = 2 * (‖(I : 𝕜) • (x + y) + z‖ * ‖(I : 𝕜) • (x + y) + z‖
    + ‖(I : 𝕜) • x - z‖ * ‖(I : 𝕜) • x - z‖) := by
  convert parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z) using 4 <;> module
private theorem add_left_aux6 (x y z : E) :
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
    ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖)
    = 2 * (‖(I : 𝕜) • (x + y) - z‖ * ‖(I : 𝕜) • (x + y) - z‖ +
    ‖(I : 𝕜) • x + z‖ * ‖(I : 𝕜) • x + z‖) := by
  convert parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z) using 4 <;> module
private theorem add_left_aux7 (y z : E) :
    ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖ + ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ =
    2 * (‖(I : 𝕜) • y + z‖ * ‖(I : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity ((I : 𝕜) • y + z) z using 4 <;> module
private theorem add_left_aux8 (y z : E) :
    ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ + ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖ =
    2 * (‖(I : 𝕜) • y - z‖ * ‖(I : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) := by
  convert parallelogram_identity ((I : 𝕜) • y - z) z using 4 <;> module
variable {𝕜}
theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  have H_re := congr(- $(add_left_aux1 x y z) + $(add_left_aux2 x y z)
    + $(add_left_aux3 y z) - $(add_left_aux4 y z))
  have H_im := congr(- $(add_left_aux5 𝕜 x y z) + $(add_left_aux6 𝕜 x y z)
      + $(add_left_aux7 𝕜 y z) - $(add_left_aux8 𝕜 y z))
  have H := congr(𝓚 $H_re + I * 𝓚 $H_im)
  simp only [inner_, map_add, map_sub, map_neg, map_mul, map_ofNat] at H ⊢
  linear_combination H / 8
private theorem rat_prop (r : ℚ) : innerProp' E (r : 𝕜) := by
  intro x y
  let hom : 𝕜 →ₗ[ℚ] 𝕜 := AddMonoidHom.toRatLinearMap <|
    AddMonoidHom.mk' (fun r ↦ inner_ 𝕜 (r • x) y) <| fun a b ↦ by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1
private theorem real_prop (r : ℝ) : innerProp' E (r : 𝕜) := by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]
private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I, inner_, inner_, mul_left_comm, smul_smul, hI', neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁, h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4
theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring
end InnerProductSpaceable
open InnerProductSpaceable
noncomputable def InnerProductSpace.ofNorm
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_inner := inner_.norm_sq
    conj_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }
variable (E)
variable [InnerProductSpaceable E]
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{  inner := inner_ 𝕜
      norm_sq_eq_inner := inner_.norm_sq
      conj_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩
variable {𝕜 E}
variable [NormedSpace ℝ E]
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance