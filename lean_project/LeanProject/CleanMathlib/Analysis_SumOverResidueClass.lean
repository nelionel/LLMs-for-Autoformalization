import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ENNReal
lemma Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : ℕ) [NeZero m] (f : ℕ → R) :
    f = ∑ a : ZMod m, {n : ℕ | (n : ZMod m) = a}.indicator f := by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
open Set in
lemma summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [TopologicalSpace R]
    [TopologicalAddGroup R] (m : ℕ) [hm : NeZero m] (k : ℕ) (f : ℕ → R) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable fun n ↦ f (m * n + k) := by
  trans Summable ({n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : ℕ | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, setOf_and,
      compl_setOf, not_lt]
  · let g : ℕ → ℕ := fun n ↦ m * n + k
    have hg : Function.Injective g := fun m n hmn ↦ by simpa [g, hm.ne] using hmn
    have hg' : ∀ n ∉ range g, {n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f n = 0 := by
      intro n hn
      contrapose! hn
      exact (Nat.range_mul_add m k).symm ▸ mem_of_indicator_ne_zero hn
    convert (Function.Injective.summable_iff hg hg').symm using 3
    simp only [Function.comp_apply, mem_setOf_eq, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero,
      zero_mul, zero_add, le_add_iff_nonneg_left, zero_le, and_self, indicator_of_mem, g]
lemma not_summable_of_antitone_of_neg {f : ℕ → ℝ} (hf : Antitone f) {n : ℕ} (hn : f n < 0) :
    ¬ Summable f := by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) ≤ f n := hf (n.le_max_left N)
  rwa [abs_of_neg hn, abs_of_neg (H.trans_lt hn), neg_le_neg_iff]
lemma not_summable_indicator_mod_of_antitone_of_neg {m : ℕ} [hm : NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {n : ℕ} (hn : f n < 0) (k : ZMod m) :
    ¬ Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) := by
  rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
    (hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val) <|
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn
lemma summable_indicator_mod_iff_summable_indicator_mod {m : ℕ} [NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {k : ZMod m} (l : ZMod m)
    (hs : Summable ({n : ℕ | (n : ZMod m) = k}.indicator f)) :
    Summable ({n : ℕ | (n : ZMod m) = l}.indicator f) := by
  by_cases hf₀ : ∀ n, 0 ≤ f n 
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl, ← Nat.cast_add, summable_indicator_mod_iff_summable]
    exact hs.of_nonneg_of_le (fun _ ↦ hf₀ _)
      fun _ ↦ hf <| Nat.add_le_add Nat.le.refl (k.val_lt.trans_le <| m.le_add_left l.val).le
  · push_neg at hf₀
    obtain ⟨n, hn⟩ := hf₀
    exact (not_summable_indicator_mod_of_antitone_of_neg hf hn k hs).elim
lemma summable_indicator_mod_iff {m : ℕ} [NeZero m] {f : ℕ → ℝ} (hf : Antitone f) (k : ZMod m) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable f := by
  refine ⟨fun H ↦ ?_, fun H ↦ Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert summable_sum (s := Finset.univ)
    fun a _ ↦ summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]
open ZMod
lemma Nat.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R] [UniformAddGroup R]
    [CompleteSpace R] [T0Space R] {f : ℕ → R} (hf : Summable f) (N : ℕ) [NeZero N] :
    ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m) := by
  rw [← (residueClassesEquiv N).symm.tsum_eq f, tsum_prod, tsum_fintype, residueClassesEquiv,
    Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective