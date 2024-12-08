import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
variable {σ M : Type*} (w : σ → M)
namespace Finsupp
section AddCommMonoid
variable [AddCommMonoid M]
noncomputable def weight : (σ →₀ ℕ) →+ M :=
  (Finsupp.linearCombination ℕ w).toAddMonoidHom
@[deprecated weight (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree := weight
theorem weight_apply (f : σ →₀ ℕ) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl
@[deprecated weight_apply (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_apply := weight_apply
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {n : ℕ} {s : σ} (h : n • w s = 0)  : n = 0
theorem nonTorsionWeight_of [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)
theorem NonTorsionWeight.ne_zero [NonTorsionWeight w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul ℕ (w s)] at h
  apply Nat.zero_ne_one.symm
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h
variable {w} in
lemma weight_sub_single_add {f : σ →₀ ℕ} {i : σ} (hi : f i ≠ 0) :
    (f - single i 1).weight w + w i = f.weight w := by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index', sum_single_index, one_smul, weight_apply]
  exacts [zero_smul .., fun _ ↦ zero_smul .., fun _ _ _ ↦ add_smul ..]
end AddCommMonoid
section OrderedAddCommMonoid
theorem le_weight (w : σ → ℕ) {s : σ} (hs : w s ≠ 0) (f : σ →₀ ℕ) :
    f s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s ∈ f.support
  · rw [Finset.sum_eq_add_sum_diff_singleton h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [not_mem_support_iff] at h
    rw [h]
    apply zero_le
variable [OrderedAddCommMonoid M] (w : σ → M)
instance : SMulPosMono ℕ M :=
  ⟨fun b hb m m' h ↦ by
    rw [← Nat.add_sub_of_le h, add_smul]
    exact le_add_of_nonneg_right (nsmul_nonneg hb (m' - m))⟩
variable {w} in
theorem le_weight_of_ne_zero (hw : ∀ s, 0 ≤ w s) {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_diff_singleton hs]
    exact le_add_of_nonneg_right <| Finset.sum_nonneg <|
      fun i _ ↦ nsmul_nonneg (hw i) (f i)
end OrderedAddCommMonoid
section CanonicallyOrderedAddCommMonoid
variable {M : Type*} [CanonicallyOrderedAddCommMonoid M] (w : σ → M)
theorem le_weight_of_ne_zero' {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f :=
  le_weight_of_ne_zero (fun _ ↦ zero_le _) hs
theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero w s
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]
theorem finite_of_nat_weight_le [Finite σ] (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d ≤ n}.Finite := by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ →₀ ℕ | weight w d ≤ n} ⊆ ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_antidiagonal, Prod.exists, exists_and_right, exists_eq_right]
  use Finsupp.equivFunOnFinite.symm (Function.const σ n) - d
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.equivFunOnFinite_symm_apply_toFun, Function.const_apply]
  rw [add_comm]
  apply Nat.sub_add_cancel
  apply le_trans (le_weight w (hw x) d)
  simpa only [Set.mem_setOf_eq] using hd
end CanonicallyOrderedAddCommMonoid
def degree (d : σ →₀ ℕ) := ∑ i ∈ d.support, d i
@[deprecated degree (since := "2024-07-20")]
alias _root_.MvPolynomial.degree := degree
@[simp]
theorem degree_add (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree :=
  sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl
@[simp]
theorem degree_single (a : σ) (m : ℕ) : (Finsupp.single a m).degree = m := by
  rw [degree, Finset.sum_eq_single a]
  · simp only [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne hba.symm
  · intro ha
    simp only [mem_support_iff, single_eq_same, ne_eq, Decidable.not_not] at ha
    rw [single_eq_same, ha]
lemma degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq, Decidable.not_imp_self,
    DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply]
@[deprecated degree_eq_zero_iff (since := "2024-07-20")]
alias _root_.MvPolynomial.degree_eq_zero_iff := degree_eq_zero_iff
@[simp]
theorem degree_zero : degree (0 : σ →₀ ℕ) = 0 := by rw [degree_eq_zero_iff]
theorem degree_eq_weight_one :
    degree (σ := σ) = weight 1 := by
  ext d
  simp only [degree, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]
@[deprecated degree_eq_weight_one (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_one := degree_eq_weight_one
theorem le_degree (s : σ) (f : σ →₀ ℕ) : f s ≤ degree f  := by
  rw [degree_eq_weight_one]
  apply le_weight
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]
theorem finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]
end Finsupp