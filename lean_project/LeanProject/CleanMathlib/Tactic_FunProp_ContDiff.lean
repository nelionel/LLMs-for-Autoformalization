import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FunProp.Differentiable
section Missing
section lambda_rules
variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
variable {f : E → F} {x} {s} {n}
theorem contDiff_id' : ContDiff K n (fun x : E => x) := contDiff_id
theorem contDiffAt_id' : ContDiffAt K n (fun x : E => x) x := contDiffAt_id
theorem contDiffOn_id' : ContDiffOn K n (fun x : E => x) s :=
  contDiff_id.contDiffOn
theorem ContDiff.comp' {g : F → G} (hg : ContDiff K n g) (hf : ContDiff K n f) :
    ContDiff K n (fun x => g (f x)) := ContDiff.comp hg hf
theorem ContDiffAt.comp' {f : E → F} {g : F → G} (hg : ContDiffAt K n g (f x))
    (hf : ContDiffAt K n f x) : ContDiffAt K n (fun x => g (f x)) x := ContDiffAt.comp x hg hf
variable {ι : Type*} [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace K (F' i)] {Φ : E → ∀ i, F' i}
theorem contDiff_pi' (hΦ : ∀ i, ContDiff K n fun x => Φ x i) : ContDiff K n Φ :=
  contDiff_pi.2 hΦ
theorem contDiffOn_pi' (hΦ : ∀ i, ContDiffOn K n (fun x => Φ x i) s) : ContDiffOn K n Φ s :=
  contDiffOn_pi.2 hΦ
theorem contDiffAt_pi' (hΦ : ∀ i, ContDiffAt K n (fun x => Φ x i) x) : ContDiffAt K n Φ x :=
  contDiffAt_pi.2 hΦ
end lambda_rules
section div
variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {s}
theorem ContDiffOn.div' {f g : E → K} {n} (hf : ContDiffOn K n f s)
    (hg : ContDiffOn K n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn K n (fun x => f x / g x) s :=
  ContDiffOn.div hf hg h₀
end div
section deriv
variable {K : Type*} [NontriviallyNormedField K]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
theorem ContDiff.differentiable_iteratedDeriv' {m : ℕ} {f : K → F}
    (hf : ContDiff K (m+1) f) : Differentiable K (iteratedDeriv m f) :=
  ContDiff.differentiable_iteratedDeriv m hf (Nat.cast_lt.mpr m.lt_succ_self)
end deriv
end Missing
attribute [fun_prop]
  ContDiff
  ContDiffAt
  ContDiffOn
attribute [fun_prop]
  contDiff_id'
  contDiff_const
  ContDiff.comp'
  contDiff_apply
  contDiff_pi'
  contDiffAt_id'
  contDiffAt_const
  ContDiffAt.comp'
  contDiffAt_pi'
  contDiffOn_id'
  contDiffOn_const
  ContDiffOn.comp'
  contDiffOn_pi'
attribute [fun_prop]
  ContDiff.prod
  ContDiff.fst
  ContDiff.snd
  ContDiffAt.prod
  ContDiffAt.fst
  ContDiffAt.snd
  ContDiffOn.prod
  ContDiffOn.fst
  ContDiffOn.snd
attribute [fun_prop]
  ContDiff.contDiffAt
  ContDiff.contDiffOn
  ContDiffAt.differentiableAt
  ContDiffOn.differentiableOn
  ContDiffAt.continuousAt
  ContDiffOn.continuousOn
  ContDiff.of_le
attribute [fun_prop]
  ContDiff.add
  ContDiff.sub
  ContDiff.neg
  ContDiff.mul
  ContDiff.smul
  ContDiff.div
  ContDiff.inv
  ContDiffAt.add
  ContDiffAt.sub
  ContDiffAt.neg
  ContDiffAt.mul
  ContDiffAt.smul
  ContDiffAt.div
  ContDiffAt.inv
  ContDiffOn.add
  ContDiffOn.sub
  ContDiffOn.neg
  ContDiffOn.mul
  ContDiffOn.smul
  ContDiffOn.div'
  ContDiffOn.inv
attribute [fun_prop]
  ContDiff.exp
  ContDiff.log
  ContDiff.pow
  ContDiffAt.exp
  ContDiffAt.log
  ContDiffAt.pow
  ContDiffOn.exp
  ContDiffOn.log
  ContDiffOn.pow
  ContDiff.differentiable_iteratedDeriv'