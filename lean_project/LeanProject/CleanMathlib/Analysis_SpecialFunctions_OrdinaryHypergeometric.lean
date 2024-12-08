import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecificLimits.RCLike
open Nat FormalMultilinearSeries
section Field
variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]
noncomputable abbrev ordinaryHypergeometricCoefficient (a b c : 𝕂) (n : ℕ) := ((n !⁻¹ : 𝕂) *
    (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹)
noncomputable def ordinaryHypergeometricSeries (a b c : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (ordinaryHypergeometricCoefficient a b c)
variable {𝔸} (a b c : 𝕂)
noncomputable def ordinaryHypergeometric (x : 𝔸) : 𝔸 :=
  (ordinaryHypergeometricSeries 𝔸 a b c).sum x
@[inherit_doc]
notation "₂F₁" => ordinaryHypergeometric
theorem ordinaryHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq]
theorem ordinaryHypergeometricSeries_apply_eq' (x : 𝔸) :
    (fun n => ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq']
theorem ordinaryHypergeometric_sum_eq (x : 𝔸) : (ordinaryHypergeometricSeries 𝔸 a b c).sum x =
    ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
      ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  tsum_congr fun n => ordinaryHypergeometricSeries_apply_eq a b c x n
theorem ordinaryHypergeometric_eq_tsum : ₂F₁ a b c =
    fun (x : 𝔸) => ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
      (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  funext (ordinaryHypergeometric_sum_eq a b c)
theorem ordinaryHypergeometricSeries_apply_zero (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => 0) = Pi.single (f := fun _ => 𝔸) 0 1 n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq, ordinaryHypergeometricCoefficient]
  cases n <;> simp
@[simp]
theorem ordinaryHypergeometric_zero : ₂F₁ a b c (0 : 𝔸) = 1 := by
  simp [ordinaryHypergeometric_eq_tsum, ← ordinaryHypergeometricSeries_apply_eq,
    ordinaryHypergeometricSeries_apply_zero]
theorem ordinaryHypergeometricSeries_symm :
    ordinaryHypergeometricSeries 𝔸 a b c = ordinaryHypergeometricSeries 𝔸 b a c := by
  unfold ordinaryHypergeometricSeries ordinaryHypergeometricCoefficient
  simp [mul_assoc, mul_left_comm]
lemma ordinaryHypergeometricSeries_eq_zero_of_neg_nat {n k : ℕ} (habc : k = -a ∨ k = -b ∨ k = -c)
    (hk : k < n) : ordinaryHypergeometricSeries 𝔸 a b c n = 0 := by
  rw [ordinaryHypergeometricSeries, ofScalars]
  rcases habc with h | h | h
  all_goals
    ext
    simp [(ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]
end Field
section RCLike
open Asymptotics Filter Real Set Nat
open scoped Topology
variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b c : 𝕂)
theorem ordinaryHypergeometric_radius_top_of_neg_nat₁ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 (-(k : 𝕂)) b c).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat (-(k : 𝕂)) b c (by aesop) (by omega)
theorem ordinaryHypergeometric_radius_top_of_neg_nat₂ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a (-(k : 𝕂)) c).radius = ⊤ := by
  rw [ordinaryHypergeometricSeries_symm]
  exact ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝔸 a c
theorem ordinaryHypergeometric_radius_top_of_neg_nat₃ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a b (-(k : 𝕂))).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b (-(k : 𝕂)) (by aesop) (by omega)
lemma ordinaryHypergeometricSeries_eq_zero_iff (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c n = 0 ↔ ∃ k < n, k = -a ∨ k = -b ∨ k = -c := by
  refine ⟨fun h ↦ ?_, fun zero ↦ ?_⟩
  · rw [ordinaryHypergeometricSeries, ofScalars_eq_zero] at h
    simp only [_root_.mul_eq_zero, inv_eq_zero] at h
    rcases h with ((hn | h) | h) | h
    · simp [Nat.factorial_ne_zero] at hn
    all_goals
      obtain ⟨kn, hkn, hn⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h
      exact ⟨kn, hkn, by tauto⟩
  · obtain ⟨_, h, hn⟩ := zero
    exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b c hn h
theorem ordinaryHypergeometricSeries_norm_div_succ_norm (n : ℕ)
    (habc : ∀ kn < n, (↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c)) :
      ‖ordinaryHypergeometricCoefficient a b c n‖ / ‖ordinaryHypergeometricCoefficient a b c n.succ‖
      = ‖a + n‖⁻¹ * ‖b + n‖⁻¹ * ‖c + n‖ * ‖1 + (n : 𝕂)‖ := by
  simp only [mul_inv_rev, factorial_succ, cast_mul, cast_add,
    cast_one, ascPochhammer_succ_eval, norm_mul, norm_inv]
  calc
    _ = ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ * ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖(n ! : 𝕂)‖⁻¹⁻¹ * ‖(n ! : 𝕂)‖⁻¹ * ‖a + n‖⁻¹ * ‖b + n‖⁻¹ * ‖c + n‖⁻¹⁻¹ *
        ‖1 + (n : 𝕂)‖⁻¹⁻¹ := by ring_nf
    _ = _ := by
      simp only [inv_inv]
      repeat rw [DivisionRing.mul_inv_cancel, one_mul]
      all_goals
        rw [norm_ne_zero_iff]
      any_goals
        apply (ascPochhammer_eval_eq_zero_iff n _).not.2
        push_neg
        exact fun kn hkn ↦ by simp [habc kn hkn]
      exact cast_ne_zero.2 (factorial_ne_zero n)
theorem ordinaryHypergeometricSeries_radius_eq_one
    (habc : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c) :
      (ordinaryHypergeometricSeries 𝔸 a b c).radius = 1 := by
  convert ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero ?_
  suffices Tendsto (fun k : ℕ ↦ (a + k)⁻¹ * (b + k)⁻¹ * (c + k) * ((1 : 𝕂) + k)) atTop (𝓝 1) by
    simp_rw [ordinaryHypergeometricSeries_norm_div_succ_norm a b c _ (fun n _ ↦ habc n)]
    simp [← norm_mul, ← norm_inv]
    convert Filter.Tendsto.norm this
    exact norm_one.symm
  have (k : ℕ) : (a + k)⁻¹ * (b + k)⁻¹ * (c + k) * ((1 : 𝕂) + k) =
        (c + k) / (a + k) * ((1 + k) / (b + k)) := by field_simp
  simp_rw [this]
  apply (mul_one (1 : 𝕂)) ▸ Filter.Tendsto.mul <;>
  convert RCLike.tendsto_add_mul_div_add_mul_atTop_nhds _ _ (1 : 𝕂) one_ne_zero <;> simp
end RCLike