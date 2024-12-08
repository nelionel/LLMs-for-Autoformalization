import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.LinearAlgebra.RootSystem.RootPositive
open Set Function
open Module hiding reflection
open Submodule (span)
noncomputable section
variable {ι R M N : Type*}
namespace RootPairing
section CommRing
variable [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)
instance : Module.Finite R P.rootSpan := Finite.span_of_finite R <| finite_range P.root
instance : Module.Finite R P.corootSpan := Finite.span_of_finite R <| finite_range P.coroot
def Polarization : M →ₗ[R] N :=
  ∑ i, LinearMap.toSpanSingleton R N (P.coroot i) ∘ₗ P.coroot' i
@[simp]
lemma Polarization_apply (x : M) :
    P.Polarization x = ∑ i, P.coroot' i x • P.coroot i := by
  simp [Polarization]
def CoPolarization : N →ₗ[R] M :=
  ∑ i, LinearMap.toSpanSingleton R M (P.root i) ∘ₗ P.root' i
@[simp]
lemma CoPolarization_apply (x : N) :
    P.CoPolarization x = ∑ i, P.root' i x • P.root i := by
  simp [CoPolarization]
lemma CoPolarization_eq : P.CoPolarization = P.flip.Polarization :=
  rfl
def RootForm : LinearMap.BilinForm R M :=
  ∑ i, (P.coroot' i).smulRight (P.coroot' i)
def CorootForm : LinearMap.BilinForm R N :=
  ∑ i, (P.root' i).smulRight (P.root' i)
lemma rootForm_apply_apply (x y : M) : P.RootForm x y =
    ∑ i, P.coroot' i x * P.coroot' i y := by
  simp [RootForm]
lemma corootForm_apply_apply (x y : N) : P.CorootForm x y =
    ∑ i, P.root' i x * P.root' i y := by
  simp [CorootForm]
lemma toPerfectPairing_apply_apply_Polarization (x y : M) :
    P.toPerfectPairing y (P.Polarization x) = P.RootForm x y := by
  simp [RootForm]
lemma toPerfectPairing_apply_CoPolarization (x : N) :
    P.toPerfectPairing (P.CoPolarization x) = P.CorootForm x := by
  ext y
  exact P.flip.toPerfectPairing_apply_apply_Polarization x y
lemma flip_comp_polarization_eq_rootForm :
    P.flip.toLin ∘ₗ P.Polarization = P.RootForm := by
  ext; simp [rootForm_apply_apply, RootPairing.flip]
lemma self_comp_coPolarization_eq_corootForm :
    P.toLin ∘ₗ P.CoPolarization = P.CorootForm := by
  ext; simp [corootForm_apply_apply]
lemma polarization_apply_eq_zero_iff (m : M) :
    P.Polarization m = 0 ↔ P.RootForm m = 0 := by
  rw [← flip_comp_polarization_eq_rootForm]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  change P.toDualRight (P.Polarization m) = 0 at h
  simp only [EmbeddingLike.map_eq_zero_iff] at h
  exact h
lemma coPolarization_apply_eq_zero_iff (n : N) :
    P.CoPolarization n = 0 ↔ P.CorootForm n = 0 :=
  P.flip.polarization_apply_eq_zero_iff n
lemma rootForm_symmetric :
    LinearMap.IsSymm P.RootForm := by
  simp [LinearMap.IsSymm, mul_comm, rootForm_apply_apply]
@[simp]
lemma rootForm_reflection_reflection_apply (i : ι) (x y : M) :
    P.RootForm (P.reflection i x) (P.reflection i y) = P.RootForm x y := by
  simp only [rootForm_apply_apply, coroot'_reflection]
  exact Fintype.sum_equiv (P.reflection_perm i)
    (fun j ↦ (P.coroot' (P.reflection_perm i j) x) * (P.coroot' (P.reflection_perm i j) y))
    (fun j ↦ P.coroot' j x * P.coroot' j y) (congrFun rfl)
lemma rootForm_self_smul_coroot (i : ι) :
    (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root i) := by
  have hP : P.Polarization (P.root i) =
      ∑ j : ι, P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j) := by
    simp_rw [Polarization_apply, root_coroot'_eq_pairing]
    exact (Fintype.sum_equiv (P.reflection_perm i)
          (fun j ↦ P.pairing i (P.reflection_perm i j) • P.coroot (P.reflection_perm i j))
          (fun j ↦ P.pairing i j • P.coroot j) (congrFun rfl)).symm
  rw [two_nsmul]
  nth_rw 2 [hP]
  rw [Polarization_apply]
  simp only [root_coroot'_eq_pairing, pairing_reflection_perm, pairing_reflection_perm_self_left,
    ← reflection_perm_coroot, smul_sub, neg_smul, sub_neg_eq_add]
  rw [Finset.sum_add_distrib, ← add_assoc, ← sub_eq_iff_eq_add]
  simp only [rootForm_apply_apply, LinearMap.coe_comp, comp_apply, Polarization_apply,
    root_coroot_eq_pairing, map_sum, LinearMapClass.map_smul, Finset.sum_neg_distrib, ← smul_assoc]
  rw [Finset.sum_smul, add_neg_eq_zero.mpr rfl]
  exact sub_eq_zero_of_eq rfl
lemma four_smul_rootForm_sq_eq_coxeterWeight_smul (i j : ι) :
    4 • (P.RootForm (P.root i) (P.root j)) ^ 2 = P.coxeterWeight i j •
      (P.RootForm (P.root i) (P.root i) * P.RootForm (P.root j) (P.root j)) := by
  have hij : 4 • (P.RootForm (P.root i)) (P.root j) =
      2 • P.toPerfectPairing (P.root j) (2 • P.Polarization (P.root i)) := by
    rw [← toPerfectPairing_apply_apply_Polarization, LinearMap.map_smul_of_tower, ← smul_assoc,
      Nat.nsmul_eq_mul]
  have hji : 2 • (P.RootForm (P.root i)) (P.root j) =
      P.toPerfectPairing (P.root i) (2 • P.Polarization (P.root j)) := by
    rw [show (P.RootForm (P.root i)) (P.root j) = (P.RootForm (P.root j)) (P.root i) by
      apply rootForm_symmetric, ← toPerfectPairing_apply_apply_Polarization,
      LinearMap.map_smul_of_tower]
  rw [sq, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul, hij, ← rootForm_self_smul_coroot,
    smul_mul_assoc 2, ← mul_smul_comm, hji, ← rootForm_self_smul_coroot, map_smul, ← pairing,
    map_smul, ← pairing, smul_eq_mul, smul_eq_mul, smul_eq_mul, coxeterWeight]
  ring
lemma corootForm_self_smul_root (i : ι) :
    (P.CorootForm (P.coroot i) (P.coroot i)) • P.root i = 2 • P.CoPolarization (P.coroot i) :=
  rootForm_self_smul_coroot (P.flip) i
lemma rootForm_self_sum_of_squares (x : M) :
    IsSumSq (P.RootForm x x) :=
  P.rootForm_apply_apply x x ▸ isSumSq_sum_mul_self Finset.univ _
lemma rootForm_root_self (j : ι) :
    P.RootForm (P.root j) (P.root j) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [rootForm_apply_apply]
theorem range_polarization_domRestrict_le_span_coroot :
    LinearMap.range (P.Polarization.domRestrict P.rootSpan) ≤ P.corootSpan := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx, LinearMap.domRestrict_apply, Polarization_apply]
  refine (mem_span_range_iff_exists_fun R).mpr ?_
  use fun i => (P.toPerfectPairing x) (P.coroot i)
  simp
lemma prod_rootForm_smul_coroot_mem_range_domRestrict (i : ι) :
    (∏ a : ι, P.RootForm (P.root a) (P.root a)) • P.coroot i ∈
      LinearMap.range (P.Polarization.domRestrict (P.rootSpan)) := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ P.RootForm (P.root a) (P.root a))
    (Finset.mem_univ i)
  rw [hc, mul_comm, mul_smul, rootForm_self_smul_coroot]
  refine LinearMap.mem_range.mpr ?_
  use ⟨(c • 2 • P.root i), by aesop⟩
  simp
section IsCrystallographic
variable [CharZero R] (h : P.IsCrystallographic) (i : ι)
include h
lemma rootForm_apply_root_self_ne_zero :
    P.RootForm (P.root i) (P.root i) ≠ 0 := by
  choose z hz using P.isCrystallographic_iff.mp h i
  simp only [rootForm_apply_apply, PerfectPairing.flip_apply_apply, root_coroot_eq_pairing, ← hz]
  suffices 0 < ∑ i, z i * z i by norm_cast; exact this.ne'
  refine Finset.sum_pos' (fun i _ ↦ mul_self_nonneg (z i)) ⟨i, Finset.mem_univ i, ?_⟩
  have hzi : z i = 2 := by
    specialize hz i
    rw [pairing_same] at hz
    norm_cast at hz
  simp [hzi]
lemma corootForm_apply_coroot_self_ne_zero :
    P.CorootForm (P.coroot i) (P.coroot i) ≠ 0 :=
  P.flip.rootForm_apply_root_self_ne_zero h.flip i
end IsCrystallographic
end CommRing
section LinearOrderedCommRing
variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)
theorem rootForm_self_non_neg (x : M) : 0 ≤ P.RootForm x x :=
  IsSumSq.nonneg (P.rootForm_self_sum_of_squares x)
theorem rootForm_self_zero_iff (x : M) :
    P.RootForm x x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  simp only [rootForm_apply_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert Finset.sum_mul_self_eq_zero_iff Finset.univ fun i => P.coroot' i x
  simp
lemma rootForm_root_self_pos (j : ι) :
    0 < P.RootForm (P.root j) (P.root j) := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    rootForm_apply_apply, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  simp
lemma coxeterWeight_le_four (i j : ι) : P.coxeterWeight i j ≤ 4 := by
  set li := P.RootForm (P.root i) (P.root i)
  set lj := P.RootForm (P.root j) (P.root j)
  set lij := P.RootForm (P.root i) (P.root j)
  have hi := P.rootForm_root_self_pos i
  have hj := P.rootForm_root_self_pos j
  have cs : 4 * lij ^ 2 ≤ 4 * (li * lj) := by
    rw [mul_le_mul_left four_pos]
    exact LinearMap.BilinForm.apply_sq_le_of_symm P.RootForm P.rootForm_self_non_neg
      P.rootForm_symmetric (P.root i) (P.root j)
  have key : 4 • lij ^ 2 = _ • (li * lj) := P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_right (by positivity)] at cs
instance instIsRootPositiveRootForm : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply
lemma coxeterWeight_mem_set_of_isCrystallographic (i j : ι) (hP : P.IsCrystallographic) :
    P.coxeterWeight i j ∈ ({0, 1, 2, 3, 4} : Set R) := by
  obtain ⟨n, hcn⟩ : ∃ n : ℕ, P.coxeterWeight i j = n := by
    obtain ⟨z, hz⟩ := P.exists_int_eq_coxeterWeight hP i j
    have hz₀ : 0 ≤ z := by simpa [hz] using P.coxeterWeight_non_neg P.RootForm i j
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz₀
    exact ⟨n, by simp [hz]⟩
  have : P.coxeterWeight i j ≤ 4 := P.coxeterWeight_le_four i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  omega
lemma prod_rootForm_root_self_pos :
    0 < ∏ i, P.RootForm (P.root i) (P.root i) :=
  Finset.prod_pos fun i _ => rootForm_root_self_pos P i
end LinearOrderedCommRing
end RootPairing