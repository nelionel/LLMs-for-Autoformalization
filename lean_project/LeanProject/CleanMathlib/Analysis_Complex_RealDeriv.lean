import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.Basic
assert_not_exists IsConformalMap
assert_not_exists Conformal
section RealDerivOfComplex
open Complex
variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasStrictFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars ℝ
  have C : HasStrictFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasStrictFDerivAt
  convert (C.comp z (B.comp z A)).hasStrictDerivAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasFDerivAt
  convert (C.comp z (B.comp z A)).hasDerivAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp
theorem ContDiffAt.real_of_complex {n : WithTop ℕ∞} (h : ContDiffAt ℂ n e z) :
    ContDiffAt ℝ n (fun x : ℝ => (e x).re) z := by
  have A : ContDiffAt ℝ n ((↑) : ℝ → ℂ) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt ℝ n e z := h.restrict_scalars ℝ
  have C : ContDiffAt ℝ n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)
theorem ContDiff.real_of_complex {n : WithTop ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem HasStrictDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasStrictFDerivAt.restrictScalars ℝ
theorem HasDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using h.hasFDerivAt.restrictScalars ℝ
theorem HasDerivWithinAt.complexToReal_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reCLM.smulRight f' + I • imCLM.smulRight f') s x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasFDerivWithinAt.restrictScalars ℝ
theorem HasStrictDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasStrictFDerivAt.restrictScalars ℝ
theorem HasDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivAt.restrictScalars ℝ
theorem HasDerivWithinAt.complexToReal_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivWithinAt.restrictScalars ℝ
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using hf.comp z ofRealCLM.hasDerivAt
theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using
    ofRealCLM.hasDerivAt.scomp z hf
end RealDerivOfComplex