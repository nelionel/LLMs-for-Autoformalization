import Mathlib.Analysis.Seminorm
open Set Filter Metric
open scoped Topology Pointwise ENNReal NNReal
section SMul
noncomputable def egauge (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ (c : 𝕜) (_ : x ∈ c • s), ‖c‖₊
variable (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] {c : 𝕜} {s t : Set E} {x : E} {r : ℝ≥0∞}
@[mono, gcongr]
lemma egauge_anti (h : s ⊆ t) (x : E) : egauge 𝕜 t x ≤ egauge 𝕜 s x :=
  iInf_mono fun _c ↦ iInf_mono' fun hc ↦ ⟨smul_set_mono h hc, le_rfl⟩
@[simp] lemma egauge_empty (x : E) : egauge 𝕜 ∅ x = ∞ := by simp [egauge]
variable {𝕜}
lemma egauge_le_of_mem_smul (h : x ∈ c • s) : egauge 𝕜 s x ≤ ‖c‖₊ := iInf₂_le c h
lemma le_egauge_iff : r ≤ egauge 𝕜 s x ↔ ∀ c : 𝕜, x ∈ c • s → r ≤ ‖c‖₊ := le_iInf₂_iff
lemma egauge_eq_top : egauge 𝕜 s x = ∞ ↔ ∀ c : 𝕜, x ∉ c • s := by simp [egauge]
lemma egauge_lt_iff : egauge 𝕜 s x < r ↔ ∃ c : 𝕜, x ∈ c • s ∧ ‖c‖₊ < r := by
  simp [egauge, iInf_lt_iff]
end SMul
section SMulZero
variable (𝕜 : Type*) [NNNorm 𝕜] [Nonempty 𝕜] {E : Type*} [Zero E] [SMulZeroClass 𝕜 E] {x : E}
@[simp] lemma egauge_zero_left_eq_top : egauge 𝕜 0 x = ∞ ↔ x ≠ 0 := by
  simp [egauge_eq_top]
@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top
end SMulZero
section Module
variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {c : 𝕜} {s : Set E} {x : E}
lemma egauge_le_of_smul_mem_of_ne (h : c • x ∈ s) (hc : c ≠ 0) :
    egauge 𝕜 s x ≤ ↑(‖c‖₊⁻¹ : ℝ≥0) := by
  rw [← nnnorm_inv]
  exact egauge_le_of_mem_smul <| (mem_inv_smul_set_iff₀ hc _ _).2 h
lemma egauge_le_of_smul_mem (h : c • x ∈ s) : egauge 𝕜 s x ≤ (‖c‖₊ : ℝ≥0∞)⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le
lemma mem_of_egauge_lt_one (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) : x ∈ s :=
  let ⟨c, hxc, hc⟩ := egauge_lt_iff.1 hx
  hs c (mod_cast hc.le) hxc
lemma egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ ∃ᶠ c : 𝕜 in 𝓝 0, x ∈ c • s := by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]
variable (𝕜)
@[simp]
lemma egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 0 := by
  have : 0 ∈ (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this
lemma egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0 := by simp
lemma egauge_le_one (h : x ∈ s) : egauge 𝕜 s x ≤ 1 := by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h
variable {𝕜}
lemma le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) :
    egauge 𝕜 s x / ‖c‖₊ ≤ egauge 𝕜 (c • s) x := by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.coe_mul, ← nnnorm_mul]
  exact egauge_le_of_mem_smul <| smul_mem_smul_set hx
lemma egauge_smul_left (hc : c ≠ 0) (s : Set E) (x : E) :
    egauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖₊ := by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖₊ = egauge 𝕜 (c • s) x / ‖c⁻¹‖₊ := by
      rw [nnnorm_inv, ENNReal.coe_inv (by simpa), div_eq_mul_inv, inv_inv]
    _ ≤ egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_smul_left _ _ _
    _ = egauge 𝕜 s x := by rw [inv_smul_smul₀ hc]
lemma le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) :
    ‖c‖₊ * egauge 𝕜 s x ≤ egauge 𝕜 s (c • x) := by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine ENNReal.mul_le_of_le_div' <| le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul, ← nnnorm_inv, ← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_smul_smul₀ hc]
lemma egauge_smul_right (h : c = 0 → s.Nonempty) (x : E) :
    egauge 𝕜 s (c • x) = ‖c‖₊ * egauge 𝕜 s x := by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl ENNReal.coe_ne_top),
      ENNReal.div_eq_inv_mul, ← ENNReal.coe_inv (by simpa), ← nnnorm_inv]
    refine (le_egauge_smul_right _ _ _).trans_eq ?_
    rw [inv_smul_smul₀ hc]
end Module
section SeminormedAddCommGroup
variable (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma div_le_egauge_closedBall (r : ℝ≥0) (x : E) : ‖x‖₊ / r ≤ egauge 𝕜 (closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff, ← coe_nnnorm, NNReal.coe_le_coe] at hy
  simp only [nnnorm_smul, ENNReal.coe_mul]
  apply ENNReal.div_le_of_le_mul
  gcongr
lemma le_egauge_closedBall_one (x : E) : ‖x‖₊ ≤ egauge 𝕜 (closedBall 0 1) x := by
  simpa using div_le_egauge_closedBall 𝕜 1 x
lemma div_le_egauge_ball (r : ℝ≥0) (x : E) : ‖x‖₊ / r ≤ egauge 𝕜 (ball 0 r) x :=
  (div_le_egauge_closedBall 𝕜 r x).trans <| egauge_anti _ ball_subset_closedBall _
lemma le_egauge_ball_one (x : E) : ‖x‖₊ ≤ egauge 𝕜 (ball 0 1) x := by
  simpa using div_le_egauge_ball 𝕜 1 x
variable {𝕜}
variable {c : 𝕜} {x : E} {r : ℝ≥0}
lemma egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r ≠ 0 ∨ ‖x‖ ≠ 0) :
    egauge 𝕜 (ball 0 r) x ≤ ‖c‖₊ * ‖x‖₊ / r := by
  letI : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases (zero_le r).eq_or_lt with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · have hx' : ‖x‖₊ = 0 := by rwa [← coe_nnnorm, NNReal.coe_eq_zero] at hx
      simp [egauge_eq_zero_iff, hx']
      refine (frequently_iff_neBot.2 (inferInstance : NeBot (𝓝[≠] (0 : 𝕜)))).mono fun c hc ↦ ?_
      simp [mem_smul_set_iff_inv_smul_mem₀ hc, norm_smul, hx, hr]
    · rcases rescale_to_shell_semi_normed hc hr hx with ⟨a, ha₀, har, -, hainv⟩
      calc
        egauge 𝕜 (ball 0 r) x ≤ ↑(‖a‖₊⁻¹) :=
          egauge_le_of_smul_mem_of_ne (mem_ball_zero_iff.2 har) ha₀
        _ ≤ ↑(‖c‖₊ * ‖x‖₊ / r) := by rwa [ENNReal.coe_le_coe, div_eq_inv_mul, ← mul_assoc]
        _ ≤ ‖c‖₊ * ‖x‖₊ / r := ENNReal.coe_div_le.trans <| by rw [ENNReal.coe_mul]
lemma egauge_ball_one_le_of_one_lt_norm (hc : 1 < ‖c‖) (x : E) :
    egauge 𝕜 (ball 0 1) x ≤ ‖c‖₊ * ‖x‖₊ := by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)
end SeminormedAddCommGroup