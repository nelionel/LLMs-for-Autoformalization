import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.DirectSum.Finsupp
universe u
variable (R : Type u) [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
open DirectSum LinearMap Function Submodule Finsupp
namespace TensorProduct
variable {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N}
variable (m n) in
abbrev VanishesTrivially : Prop :=
  ∃ (κ : Type u) (_ : Fintype κ) (a : ι → κ → R) (y : κ → N),
    (∀ i, n i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, a i j • m i = 0
theorem sum_tmul_eq_zero_of_vanishesTrivially (hmn : VanishesTrivially R m n) :
    ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) := by
  obtain ⟨κ, _, a, y, h₁, h₂⟩ := hmn
  simp_rw [h₁, tmul_sum, tmul_smul]
  rw [Finset.sum_comm]
  simp_rw [← tmul_smul, ← smul_tmul, ← sum_tmul, h₂, zero_tmul, Finset.sum_const_zero]
theorem vanishesTrivially_of_sum_tmul_eq_zero (hm : Submodule.span R (Set.range m) = ⊤)
    (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) : VanishesTrivially R m n := by
  set G : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R m with hG
  have G_basis_eq (i : ι) : G (Finsupp.single i 1) = m i := by simp [hG, toModule_lof]
  have G_surjective : Surjective G := by
    apply LinearMap.range_eq_top.mp
    apply top_le_iff.mp
    rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    use Finsupp.single i 1, G_basis_eq i
  set en : (ι →₀ R) ⊗[R] N := ∑ i, Finsupp.single i 1 ⊗ₜ n i with hen
  have en_mem_ker : en ∈ ker (rTensor N G) := by simp [hen, G_basis_eq, hmn]
  have exact_ker_subtype : Exact (ker G).subtype G := G.exact_subtype_ker_map
  have exact_rTensor_ker_subtype : Exact (rTensor N (ker G).subtype) (rTensor N G) :=
    rTensor_exact (M := ↥(ker G)) N exact_ker_subtype G_surjective
  have en_mem_range : en ∈ range (rTensor N (ker G).subtype) :=
    exact_rTensor_ker_subtype.linearMap_ker_eq ▸ en_mem_ker
  obtain ⟨kn, hkn⟩ := en_mem_range
  obtain ⟨ma, rfl : kn = ∑ kj ∈ ma, kj.1 ⊗ₜ[R] kj.2⟩ := exists_finset kn
  use ↑↑ma, FinsetCoe.fintype ma
  use fun i ⟨⟨kj, _⟩, _⟩ ↦ (kj : ι →₀ R) i
  use fun ⟨⟨_, yj⟩, _⟩ ↦ yj
  constructor
  · intro i
    classical
    apply_fun finsuppScalarLeft R N ι at hkn
    apply_fun (· i) at hkn
    symm at hkn
    simp only [map_sum, finsuppScalarLeft_apply_tmul, zero_smul, Finsupp.single_zero,
      Finsupp.sum_single_index, one_smul, Finsupp.finset_sum_apply, Finsupp.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, rTensor_tmul, coe_subtype, Finsupp.sum_apply,
      Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, en] at hkn
    simp only [Finset.univ_eq_attach, Finset.sum_attach ma (fun x ↦ (x.1 : ι →₀ R) i • x.2)]
    convert hkn using 2 with x _
    split
    · next h'x => rw [h'x, zero_smul]
    · rfl
  · rintro ⟨⟨⟨k, hk⟩, _⟩, _⟩
    simpa only [hG, linearCombination_apply, zero_smul, implies_true, Finsupp.sum_fintype] using
      mem_ker.mp hk
theorem vanishesTrivially_iff_sum_tmul_eq_zero (hm : Submodule.span R (Set.range m) = ⊤) :
    VanishesTrivially R m n ↔ ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) :=
  ⟨sum_tmul_eq_zero_of_vanishesTrivially R, vanishesTrivially_of_sum_tmul_eq_zero R hm⟩
theorem vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective
    (hm : Injective (rTensor N (span R (Set.range m)).subtype))
    (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) : VanishesTrivially R m n := by
  have mem_M' i : m i ∈ span R (Set.range m) := subset_span ⟨i, rfl⟩
  set m' : ι → span R (Set.range m) := Subtype.coind m mem_M' with m'_eq
  have hm' : span R (Set.range m') = ⊤ := by
    apply map_injective_of_injective (injective_subtype (span R (Set.range m)))
    rw [Submodule.map_span, Submodule.map_top, range_subtype, coe_subtype, ← Set.range_comp]
    rfl
  have hm'n : ∑ i, m' i ⊗ₜ n i = (0 : span R (Set.range m) ⊗[R] N) := by
    apply hm
    simp only [m'_eq, map_sum, rTensor_tmul, coe_subtype, Subtype.coind_coe, _root_.map_zero, hmn]
  have : VanishesTrivially R m' n := vanishesTrivially_of_sum_tmul_eq_zero R hm' hm'n
  unfold VanishesTrivially at this ⊢
  convert this with κ _ a y j
  convert (injective_iff_map_eq_zero' _).mp (injective_subtype (span R (Set.range m))) _
  simp [m'_eq]
theorem vanishesTrivially_iff_sum_tmul_eq_zero_of_rTensor_injective
    (hm : Injective (rTensor N (span R (Set.range m)).subtype)) :
    VanishesTrivially R m n ↔ ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) :=
  ⟨sum_tmul_eq_zero_of_vanishesTrivially R,
    vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R hm⟩
theorem rTensor_injective_of_forall_vanishesTrivially
    (hMN : ∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n)
    (M' : Submodule R M) : Injective (rTensor N M'.subtype) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro x hx
  obtain ⟨s, rfl⟩ := exists_finset x
  rw [← Finset.sum_attach]
  apply sum_tmul_eq_zero_of_vanishesTrivially
  simp only [map_sum, rTensor_tmul, coe_subtype] at hx
  have := hMN ((Finset.sum_attach s _).trans hx)
  unfold VanishesTrivially at this ⊢
  convert this with κ _ a y j
  symm
  convert (injective_iff_map_eq_zero' _).mp (injective_subtype M') _
  simp
theorem forall_vanishesTrivially_iff_forall_rTensor_injective :
    (∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n) ↔
    ∀ M' : Submodule R M, Injective (rTensor N M'.subtype) := by
  constructor
  · intro h
    exact rTensor_injective_of_forall_vanishesTrivially R h
  · intro h ι _ m n hmn
    exact vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R (h _) hmn
theorem forall_vanishesTrivially_iff_forall_FG_rTensor_injective :
    (∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n) ↔
    ∀ (M' : Submodule R M) (_ : M'.FG), Injective (rTensor N M'.subtype) := by
  constructor
  · intro h M' _
    exact rTensor_injective_of_forall_vanishesTrivially R h M'
  · intro h ι _ m n hmn
    exact vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
      (h _ (fg_span (Set.finite_range _))) hmn
theorem rTensor_injective_of_forall_FG_rTensor_injective
    (hMN : ∀ (M' : Submodule R M) (_ : M'.FG), Injective (rTensor N M'.subtype))
    (M' : Submodule R M) : Injective (rTensor N M'.subtype) :=
  (forall_vanishesTrivially_iff_forall_rTensor_injective R).mp
    ((forall_vanishesTrivially_iff_forall_FG_rTensor_injective R).mpr hMN) M'
end TensorProduct