import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.WithDensity
open MeasureTheory Set Filter ENNReal
open scoped NNReal MeasureTheory Topology ProbabilityTheory
namespace ProbabilityTheory.Kernel
variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Kernel α γ}
  [hαγ : MeasurableSpace.CountableOrCountablyGenerated α γ]
open Classical in
noncomputable
def rnDerivAux (κ η : Kernel α γ) (a : α) (x : γ) : ℝ :=
  if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a ↦ (a, ()))) η a x univ
lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x := by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _
lemma rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ ≤ η) {a : α} :
    rnDerivAux κ η a ≤ᵐ[η a] 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _
lemma measurable_rnDerivAux (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ Kernel.rnDerivAux κ η p.1 p.2) := by
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine Measurable.ennreal_toReal ?_
    change Measurable ((fun q : γ × α ↦ (κ q.2).rnDeriv (η q.2) q.1) ∘ Prod.swap)
    refine (measurable_from_prod_countable' (fun a ↦ ?_) ?_).comp measurable_swap
    · exact Measure.measurable_rnDeriv (κ a) (η a)
    · intro a a' c ha'_mem_a
      have h_eq : ∀ κ : Kernel α γ, κ a' = κ a := fun κ ↦ by
        ext s hs
        exact mem_of_mem_measurableAtom ha'_mem_a
          (Kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
      rw [h_eq κ, h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ
lemma measurable_rnDerivAux_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDerivAux κ η a x) := by
  change Measurable ((fun p : α × γ ↦ rnDerivAux κ η p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDerivAux _ _).comp measurable_prod_mk_left
lemma setLIntegral_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.setLIntegral_rnDeriv h_ac]
    refine setLIntegral_congr_fun hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [setLIntegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs, map_apply' _ (by fun_prop) _ (hs.prod MeasurableSet.univ)]
    congr with x
    simp
@[deprecated (since := "2024-06-29")]
alias set_lintegral_rnDerivAux := setLIntegral_rnDerivAux
lemma withDensity_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)) = κ := by
  ext a s hs
  rw [Kernel.withDensity_apply']
  swap
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  simp_rw [ofNNReal_toNNReal]
  exact setLIntegral_rnDerivAux κ η a hs
lemma withDensity_one_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) = η := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [coe_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx
def mutuallySingularSet (κ η : Kernel α γ) : Set (α × γ) := {p | 1 ≤ rnDerivAux κ (κ + η) p.1 p.2}
def mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : Set γ :=
  {x | 1 ≤ rnDerivAux κ (κ + η) a x}
lemma mem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x ∈ mutuallySingularSetSlice κ η a ↔ 1 ≤ rnDerivAux κ (κ + η) a x := by
  rw [mutuallySingularSetSlice]; rfl
lemma not_mem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x ∉ mutuallySingularSetSlice κ η a ↔ rnDerivAux κ (κ + η) a x < 1 := by
  simp [mutuallySingularSetSlice]
lemma measurableSet_mutuallySingularSet (κ η : Kernel α γ) :
    MeasurableSet (mutuallySingularSet κ η) :=
  measurable_rnDerivAux κ (κ + η) measurableSet_Ici
lemma measurableSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) :
    MeasurableSet (mutuallySingularSetSlice κ η a) :=
  measurable_prod_mk_left (measurableSet_mutuallySingularSet κ η)
lemma measure_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    η a (mutuallySingularSetSlice κ η a) = 0 := by
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 ≤ rnDerivAux κ (κ + η) a x} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
  simp_rw [ofNNReal_toNNReal]
  rw [Kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq, ae_restrict_iff]
  rotate_left
  · exact (measurable_const.sub
      ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
      (measurableSet_singleton _)
  · exact (measurable_const.sub
      ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_setOf_eq] at hx
  simp [hx]
noncomputable
irreducible_def rnDeriv (κ η : Kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)
lemma rnDeriv_def' (κ η : Kernel α γ) :
    rnDeriv κ η = fun a x ↦ ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
      / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x) := by ext; rw [rnDeriv_def]
lemma measurable_rnDeriv (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ rnDeriv κ η p.1 p.2) := by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal
lemma measurable_rnDeriv_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDeriv κ η a x) := by
  change Measurable ((fun p : α × γ ↦ rnDeriv κ η p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDeriv _ _).comp measurable_prod_mk_left
lemma rnDeriv_eq_top_iff (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ (a, x) ∈ mutuallySingularSet κ η := by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_setOf_eq, and_iff_right_iff_imp]
  exact fun h ↦ zero_lt_one.trans_le h
lemma rnDeriv_eq_top_iff' (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ x ∈ mutuallySingularSetSlice κ η a := by
  rw [rnDeriv_eq_top_iff, mutuallySingularSet, mutuallySingularSetSlice, mem_setOf, mem_setOf]
noncomputable
irreducible_def singularPart (κ η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    Kernel α γ :=
  withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
    - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x)
lemma measurable_singularPart_fun (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) p.1 p.2)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) p.1 p.2) * rnDeriv κ η p.1 p.2) :=
  (measurable_rnDerivAux _ _).ennreal_ofReal.sub
    ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul (measurable_rnDeriv _ _))
lemma measurable_singularPart_fun_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x) := by
  change Measurable ((Function.uncurry fun a b ↦
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b ↦ (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prod_mk_left
lemma singularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [singularPart, Kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
    ae_restrict_iff]
  all_goals simp_rw [ofNNReal_toNNReal]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_compl_iff, mutuallySingularSetSlice, mem_setOf, not_le] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
    mul_inv_cancel₀, one_mul, tsub_self, Pi.zero_apply]
  · simp only [ne_eq, sub_eq_zero, hx.ne', not_false_eq_true]
  · simp only [sub_nonneg, hx.le]
  · simp only [sub_pos, hx]
lemma singularPart_of_subset_compl_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 :=
  measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)
lemma singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    singularPart κ η a s = κ a s := by
  have hs' : ∀ x ∈ s, 1 ≤ rnDerivAux κ (κ + η) a x := fun _ hx ↦ hs hx
  rw [singularPart, Kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine setLIntegral_congr_fun hsm ?_
        have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)
lemma withDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η
lemma withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    withDensity η (rnDeriv κ η) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)
lemma withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    withDensity η (rnDeriv κ η) a s = κ a s := by
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this, ← withDensity_mul, Kernel.withDensity_apply']
  rotate_left
  · exact ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul
    (measurable_rnDeriv _ _))
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).real_toNNReal
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : ∀ x ∈ s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← not_mem_mutuallySingularSetSlice]
    exact fun x hx hx_mem ↦ hs hx hx_mem
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine setLIntegral_congr_fun hsm (ae_of_all _ fun x hx ↦ ?_)
      rw [ofNNReal_toNNReal, ← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul,
        ← mul_assoc, mul_inv_cancel₀, one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := setLIntegral_rnDerivAux κ η a hsm
lemma mutuallySingular_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    singularPart κ η a ⟂ₘ η a := by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩
lemma rnDeriv_add_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity η (rnDeriv κ η) + singularPart κ η = κ := by
  ext a s hs
  rw [← inter_union_diff s (mutuallySingularSetSlice κ η a)]
  simp only [coe_add, Pi.add_apply, Measure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono inter_subset_right le_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) inter_subset_right,
    singularPart_of_subset_compl_mutuallySingularSetSlice (diff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_of_subset_mutuallySingularSetSlice inter_subset_right,
    zero_add, withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (diff_subset_iff.mpr (by simp)), add_comm]
section EqZeroIff
lemma singularPart_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ singularPart κ η a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    singularPart_compl_mutuallySingularSetSlice, add_zero]
lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0
      ↔ withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    withDensity_rnDeriv_mutuallySingularSetSlice, zero_add]
lemma singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a ≪ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, coe_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)
lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, coe_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)
lemma singularPart_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [coe_add, Pi.add_apply, Measure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a
lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [coe_add, Pi.add_apply, Measure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a
end EqZeroIff
@[measurability]
lemma measurableSet_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≪ η a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)
@[measurability]
lemma measurableSet_mutuallySingular (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ⟂ₘ η a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)
@[simp]
lemma singularPart_self (κ : Kernel α γ) [IsFiniteKernel κ] : κ.singularPart κ = 0 := by
  ext : 1; rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]
section Unique
variable {ξ : Kernel α γ} {f : α → γ → ℝ≥0∞} [IsFiniteKernel η]
omit hαγ in
lemma eq_rnDeriv_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] ∂(κ a)/∂(η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coe_add, Pi.add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prod_mk_left).aemeasurable hξ this
omit hαγ in
lemma eq_singularPart_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = (κ a).singularPart (η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, coe_add, Pi.add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prod_mk_left) hξ this
variable [IsFiniteKernel κ] {a : α}
lemma rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)
lemma singularPart_eq_singularPart_measure : singularPart κ η a = (κ a).singularPart (η a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)
lemma eq_rnDeriv (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] rnDeriv κ η a :=
  (eq_rnDeriv_measure h hf a hξ).trans rnDeriv_eq_rnDeriv_measure.symm
lemma eq_singularPart (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = singularPart κ η a :=
  (eq_singularPart_measure h hf a hξ).trans singularPart_eq_singularPart_measure.symm
end Unique
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (withDensity η (rnDeriv κ η)) := by
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  rw [Kernel.withDensity_apply', setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae rnDeriv_eq_rnDeriv_measure]
  exact Measure.lintegral_rnDeriv_le.trans (measure_le_bound _ _ _)
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (singularPart κ η) := by
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))
lemma measurable_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ (κ a).singularPart (η a)) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs ↦ ?_)
  simp_rw [← κ.singularPart_eq_singularPart_measure, κ.singularPart_def η]
  exact Kernel.measurable_coe _ hs
lemma rnDeriv_self (κ : Kernel α γ) [IsFiniteKernel κ] (a : α) : rnDeriv κ κ a =ᵐ[κ a] 1 :=
  (κ.rnDeriv_eq_rnDeriv_measure).trans (κ a).rnDeriv_self
lemma rnDeriv_singularPart (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0 := by
  filter_upwards [(singularPart κ ν).rnDeriv_eq_rnDeriv_measure,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1, h2]
lemma rnDeriv_lt_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    ∀ᵐ x ∂(η a), rnDeriv κ η a x < ∞ := by
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_ne_top _]
    with x heq htop using heq ▸ htop.lt_top
lemma rnDeriv_ne_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    ∀ᵐ x ∂(η a), rnDeriv κ η a x ≠ ∞ := by
  filter_upwards [κ.rnDeriv_lt_top η] with a h using h.ne
lemma rnDeriv_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < rnDeriv κ η a x := by
  filter_upwards [ha.ae_le κ.rnDeriv_eq_rnDeriv_measure, Measure.rnDeriv_pos ha]
    with x heq hpos using heq ▸ hpos
lemma rnDeriv_toReal_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < (rnDeriv κ η a x).toReal := by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true, and_self]
lemma rnDeriv_add (κ ν η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
    (a : α) :
    rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν η a := by
  filter_upwards [(κ + ν).rnDeriv_eq_rnDeriv_measure, κ.rnDeriv_eq_rnDeriv_measure,
    ν.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_add (ν a) (η a)] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, coe_add, Pi.add_apply, h4, Pi.add_apply]
lemma withDensity_rnDeriv_le (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    η.withDensity (κ.rnDeriv η) a ≤ κ a := by
  refine Measure.le_intro (fun s hs _ ↦ ?_)
  rw [Kernel.withDensity_apply']
  swap; · exact κ.measurable_rnDeriv _
  rw [setLIntegral_congr_fun hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ ↦ hx)),
    ← withDensity_apply _ hs]
  exact (κ a).withDensity_rnDeriv_le _ _
lemma withDensity_rnDeriv_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) a = κ a := by
  rw [Kernel.withDensity_apply]
  swap; · exact κ.measurable_rnDeriv _
  have h_ae := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [MeasureTheory.withDensity_congr_ae h_ae, (κ a).withDensity_rnDeriv_eq _ h]
lemma rnDeriv_withDensity [IsFiniteKernel κ] {f : α → γ → ℝ≥0∞} [IsFiniteKernel (withDensity κ f)]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    (κ.withDensity f).rnDeriv κ a =ᵐ[κ a] f a := by
  have h_ae := (κ.withDensity f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := a)
  have hf' : ∀ a, Measurable (f a) := fun _ ↦ hf.of_uncurry_left
  filter_upwards [h_ae, (κ a).rnDeriv_withDensity (hf' a)] with x hx1 hx2
  rw [hx1, κ.withDensity_apply hf, hx2]
end ProbabilityTheory.Kernel