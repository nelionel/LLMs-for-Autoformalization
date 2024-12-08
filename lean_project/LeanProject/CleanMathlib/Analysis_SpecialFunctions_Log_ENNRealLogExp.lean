import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
open EReal ENNReal Topology
section LogExp
@[simp] lemma EReal.log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp
@[simp] lemma ENNReal.exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]
end LogExp
section Exp
namespace EReal
lemma exp_nmul (x : EReal) (n : ℕ) : exp (n * x) = (exp x) ^ n := by
  simp_rw [← log_eq_iff, log_pow, log_exp]
lemma exp_mul (x : EReal) (y : ℝ) : exp (x * y) = (exp x) ^ y := by
  rw [← log_eq_iff, log_rpow, log_exp, log_exp, mul_comm]
end EReal
end Exp
namespace ENNReal
section OrderIso
noncomputable
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]
@[simp] lemma logOrderIso_apply (x : ℝ≥0∞) : logOrderIso x = log x := rfl
noncomputable
def _root_.EReal.expOrderIso := logOrderIso.symm
@[simp] lemma _root_.EReal.expOrderIso_apply (x : EReal) : expOrderIso x = exp x := rfl
@[simp] lemma logOrderIso_symm : logOrderIso.symm = expOrderIso := rfl
@[simp] lemma _root_.EReal.expOrderIso_symm : expOrderIso.symm = logOrderIso := rfl
end OrderIso
section Continuity
noncomputable def logHomeomorph : ℝ≥0∞ ≃ₜ EReal := logOrderIso.toHomeomorph
@[simp] lemma logHomeomorph_apply (x : ℝ≥0∞) : logHomeomorph x = log x := rfl
noncomputable def _root_.EReal.expHomeomorph : EReal ≃ₜ ℝ≥0∞ := expOrderIso.toHomeomorph
@[simp] lemma _root_.EReal.expHomeomorph_apply (x : EReal) : expHomeomorph x = exp x := rfl
@[simp] lemma logHomeomorph_symm : logHomeomorph.symm = expHomeomorph := rfl
@[simp] lemma _root_.EReal.expHomeomorph_symm : expHomeomorph.symm = logHomeomorph := rfl
@[continuity, fun_prop]
lemma continuous_log : Continuous log := logOrderIso.continuous
@[continuity, fun_prop]
lemma continuous_exp : Continuous exp := expOrderIso.continuous
end Continuity
section Measurability
@[measurability, fun_prop]
lemma measurable_log : Measurable log := continuous_log.measurable
@[measurability, fun_prop]
lemma _root_.EReal.measurable_exp : Measurable exp := continuous_exp.measurable
@[measurability, fun_prop]
lemma _root_.Measurable.ennreal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ log (f x) := measurable_log.comp hf
@[measurability, fun_prop]
lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x ↦ exp (f x) := measurable_exp.comp hf
end Measurability
end ENNReal
instance : PolishSpace EReal := ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace