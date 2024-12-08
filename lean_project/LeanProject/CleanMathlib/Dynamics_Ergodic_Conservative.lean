import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Combinatorics.Pigeonhole
noncomputable section
open Set Filter MeasureTheory Finset Function TopologicalSpace Topology
variable {α : Type*} [MeasurableSpace α] {f : α → α} {s : Set α} {μ : Measure α}
namespace MeasureTheory
open Measure
structure Conservative (f : α → α) (μ : Measure α) extends QuasiMeasurePreserving f μ μ : Prop where
  exists_mem_iterate_mem' : ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s
protected theorem MeasurePreserving.conservative [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ) :
    Conservative f μ :=
  ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm.nullMeasurableSet h0⟩
namespace Conservative
protected theorem id (μ : Measure α) : Conservative id μ :=
  { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem' := fun _ _ h0 => by
      simpa [exists_ne] using nonempty_of_measure_ne_zero h0 }
theorem of_absolutelyContinuous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ)
    (h' : QuasiMeasurePreserving f ν ν) : Conservative f ν :=
  ⟨h', fun _ hsm h0 ↦ h.exists_mem_iterate_mem' hsm (mt (@hν _) h0)⟩
theorem measureRestrict (h : Conservative f μ) (hs : MapsTo f s s) :
    Conservative f (μ.restrict s) :=
  .of_absolutelyContinuous h (absolutelyContinuous_of_le restrict_le_self) <|
    h.toQuasiMeasurePreserving.restrict hs
theorem exists_mem_iterate_mem (hf : Conservative f μ)
    (hsm : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) :
    ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  rcases hsm.exists_measurable_subset_ae_eq with ⟨t, hsub, htm, hts⟩
  rcases hf.exists_mem_iterate_mem' htm (by rwa [measure_congr hts]) with ⟨x, hxt, m, hm₀, hmt⟩
  exact ⟨x, hsub hxt, m, hm₀, hsub hmt⟩
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) : ∃ᶠ m in atTop, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 := by
  set t : ℕ → Set α := fun n ↦ s ∩ f^[n] ⁻¹' s
  by_contra H
  obtain ⟨N, hN, hmax⟩ : ∃ N, μ (t N) ≠ 0 ∧ ∀ n > N, μ (t n) = 0 := by
    rw [Nat.frequently_atTop_iff_infinite, not_infinite] at H
    convert exists_max_image _ (·) H ⟨0, by simpa⟩ using 4
    rw [gt_iff_lt, ← not_le, not_imp_comm, mem_setOf]
  have htm {n : ℕ} : NullMeasurableSet (t n) μ :=
    hs.inter <| hs.preimage <| hf.toQuasiMeasurePreserving.iterate n
  set T := t N \ ⋃ n > N, t n with hT
  have hμT : μ T ≠ 0 := by
    rwa [hT, measure_diff_null]
    exact (measure_biUnion_null_iff {n | N < n}.to_countable).2 hmax
  have hTm : NullMeasurableSet T μ := htm.diff <| .biUnion {n | N < n}.to_countable fun _ _ ↦ htm
  rcases hf.exists_mem_iterate_mem hTm hμT with ⟨x, hxt, m, hm₀, hmt⟩
  refine hxt.2 <| mem_iUnion₂.2 ⟨N + m, ?_, hxt.1.1, ?_⟩
  · simpa [pos_iff_ne_zero]
  · simpa only [iterate_add] using hmt.1.2
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) (N : ℕ) : ∃ m > N, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩
theorem measure_mem_forall_ge_image_not_mem_eq_zero (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (n : ℕ) :
    μ ({ x ∈ s | ∀ m ≥ n, f^[m] x ∉ s }) = 0 := by
  by_contra H
  have : NullMeasurableSet (s ∩ { x | ∀ m ≥ n, f^[m] x ∉ s }) μ := by
    simp only [setOf_forall, ← compl_setOf]
    exact hs.inter <| .biInter (to_countable _) fun m _ ↦
      (hs.preimage <| hf.toQuasiMeasurePreserving.iterate m).compl
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  simp only [frequently_atTop, @forall_swap (_ ∈ s), ae_all_iff]
  intro n
  filter_upwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)]
  simp
theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventuallyEq_left.2 <| hf.ae_mem_imp_frequently_image_mem hs
theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    μ (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ, ∀ k, f^[k] x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k, frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (h0 : μ s ≠ 0) : ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in atTop, f^[n] x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → α} {μ : Measure α} (h : Conservative f μ) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, f^[n] x ∈ s := by
  have : ∀ s ∈ countableBasis α, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn
protected theorem iterate (hf : Conservative f μ) (n : ℕ) : Conservative f^[n] μ := by
  cases' n with n
  · exact Conservative.id μ
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
    with ⟨x, _, hx⟩
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm, mul_zero, eq_comm, tsub_eq_zero_iff_le] at this
    exact this.not_lt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le
end Conservative
end MeasureTheory