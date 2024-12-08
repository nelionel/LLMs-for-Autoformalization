import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.Algebra.Algebra
open ContinuousMap Filter
open scoped unitInterval
theorem polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  refine Filter.Frequently.mem_closure ?_
  refine Filter.Tendsto.frequently (bernsteinApproximation_uniform f) ?_
  apply Frequently.of_forall
  intro n
  simp only [SetLike.mem_coe]
  apply Subalgebra.sum_mem
  rintro n -
  apply Subalgebra.smul_mem
  dsimp [bernstein, polynomialFunctions]
  simp
theorem polynomialFunctions_closure_eq_top (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  cases' lt_or_le a b with h h
  · 
    let W : C(Set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) :=
      compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm
    let W' : C(Set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := (iccHomeoI a b h).arrowCongr (.refl _)
    have w : (W : C(Set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl
    have p := polynomialFunctions_closure_eq_top'
    apply_fun fun s => s.comap W at p
    simp only [Algebra.comap_top] at p
    rw [Subalgebra.topologicalClosure_comap_homeomorph _ W W' w] at p
    rw [polynomialFunctions.comap_compRightAlgHom_iccHomeoI] at p
    exact p
  · 
    subsingleton [(Set.subsingleton_Icc_of_ge h).coe_sort]
theorem continuousMap_mem_polynomialFunctions_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp
open scoped Polynomial
theorem exists_polynomial_near_continuousMap (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ)
    (pos : 0 < ε) : ∃ p : ℝ[X], ‖p.toContinuousMapOn _ - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩
theorem exists_polynomial_near_of_continuousOn (a b : ℝ) (f : ℝ → ℝ)
    (c : ContinuousOn f (Set.Icc a b)) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩