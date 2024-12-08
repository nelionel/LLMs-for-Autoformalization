import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Projection
open Set LinearMap
open scoped Classical
open Pointwise
section Dual
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (s t : Set H)
open RealInnerProductSpace
def Set.innerDualCone (s : Set H) : ConvexCone ℝ H where
  carrier := { y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫ }
  smul_mem' c hc y hy x hx := by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' u hu v hv x hx := by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)
@[simp]
theorem mem_innerDualCone (y : H) (s : Set H) : y ∈ s.innerDualCone ↔ ∀ x ∈ s, 0 ≤ ⟪x, y⟫ :=
  Iff.rfl
@[simp]
theorem innerDualCone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => False.elim
@[simp]
theorem innerDualCone_zero : (0 : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ y (hy : y = 0) => hy.symm ▸ (inner_zero_left _).ge
@[simp]
theorem innerDualCone_univ : (univ : Set H).innerDualCone = 0 := by
  suffices ∀ x : H, x ∈ (univ : Set H).innerDualCone → x = 0 by
    apply SetLike.coe_injective
    exact eq_singleton_iff_unique_mem.mpr ⟨fun x _ => (inner_zero_right _).ge, this⟩
  exact fun x hx => by simpa [← real_inner_self_nonpos] using hx (-x) (mem_univ _)
theorem innerDualCone_le_innerDualCone (h : t ⊆ s) : s.innerDualCone ≤ t.innerDualCone :=
  fun _ hy x hx => hy x (h hx)
theorem pointed_innerDualCone : s.innerDualCone.Pointed := fun x _ => by rw [inner_zero_right]
theorem innerDualCone_singleton (x : H) :
    ({x} : Set H).innerDualCone = (ConvexCone.positive ℝ ℝ).comap (innerₛₗ ℝ x) :=
  ConvexCone.ext fun _ => forall_eq
theorem innerDualCone_union (s t : Set H) :
    (s ∪ t).innerDualCone = s.innerDualCone ⊓ t.innerDualCone :=
  le_antisymm (le_inf (fun _ hx _ hy => hx _ <| Or.inl hy) fun _ hx _ hy => hx _ <| Or.inr hy)
    fun _ hx _ => Or.rec (hx.1 _) (hx.2 _)
theorem innerDualCone_insert (x : H) (s : Set H) :
    (insert x s).innerDualCone = Set.innerDualCone {x} ⊓ s.innerDualCone := by
  rw [insert_eq, innerDualCone_union]
theorem innerDualCone_iUnion {ι : Sort*} (f : ι → Set H) :
    (⋃ i, f i).innerDualCone = ⨅ i, (f i).innerDualCone := by
  refine le_antisymm (le_iInf fun i x hx y hy => hx _ <| mem_iUnion_of_mem _ hy) ?_
  intro x hx y hy
  rw [ConvexCone.mem_iInf] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact hx _ _ hj
theorem innerDualCone_sUnion (S : Set (Set H)) :
    (⋃₀ S).innerDualCone = sInf (Set.innerDualCone '' S) := by
  simp_rw [sInf_image, sUnion_eq_biUnion, innerDualCone_iUnion]
theorem innerDualCone_eq_iInter_innerDualCone_singleton :
    (s.innerDualCone : Set H) = ⋂ i : s, (({↑i} : Set H).innerDualCone : Set H) := by
  rw [← ConvexCone.coe_iInf, ← innerDualCone_iUnion, iUnion_of_singleton_coe]
theorem isClosed_innerDualCone : IsClosed (s.innerDualCone : Set H) := by
  rw [innerDualCone_eq_iInter_innerDualCone_singleton]
  apply isClosed_iInter
  intro x
  have h : ({↑x} : Set H).innerDualCone = (inner x : H → ℝ) ⁻¹' Set.Ici 0 := by
    rw [innerDualCone_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')
theorem ConvexCone.pointed_of_nonempty_of_isClosed (K : ConvexCone ℝ H) (ne : (K : Set H).Nonempty)
    (hc : IsClosed (K : Set H)) : K.Pointed := by
  obtain ⟨x, hx⟩ := ne
  let f : ℝ → H := (· • x)
  have fI : f '' Set.Ioi 0 ⊆ (K : Set H) := by
    rintro _ ⟨_, h, rfl⟩
    exact K.smul_mem (Set.mem_Ioi.1 h) hx
  have clf : closure (f '' Set.Ioi 0) ⊆ (K : Set H) := hc.closure_subset_iff.2 fI
  have fc : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 :=
    (continuous_id.smul continuous_const).continuousWithinAt
  have mem₀ := fc.mem_closure_image (by rw [closure_Ioi (0 : ℝ), mem_Ici])
  have f₀ : f 0 = 0 := zero_smul ℝ x
  simpa only [f₀, ConvexCone.Pointed, ← SetLike.mem_coe] using mem_of_subset_of_mem clf mem₀
section CompleteSpace
variable [CompleteSpace H]
open scoped InnerProductSpace in
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) {b : H} (disj : b ∉ K) :
    ∃ y : H, (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 := by
  obtain ⟨z, hzK, infi⟩ := exists_norm_eq_iInf_of_complete_convex ne hc.isComplete K.convex b
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero K.convex hzK).1 infi
  use z - b
  constructor
  · 
    rintro x hxK
    specialize hinner _ (K.add_mem hxK hzK)
    rwa [add_sub_cancel_right, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul,
      ← real_inner_smul_right, neg_smul, one_smul, neg_sub] at hinner
  · 
    have hinner₀ := hinner 0 (K.pointed_of_nonempty_of_isClosed ne hc)
    rw [zero_sub, inner_neg_right, Right.neg_nonpos_iff] at hinner₀
    have hbz : b - z ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! hzK
      rwa [← hzK]
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul]
    calc
      0 < ⟪b - z, b - z⟫_ℝ := lt_of_not_le ((Iff.not real_inner_self_nonpos).2 hbz)
      _ = ⟪b - z, b - z⟫_ℝ + 0 := (add_zero _).symm
      _ ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ := add_le_add rfl.ge hinner₀
      _ = ⟪b - z, b - z + z⟫_ℝ := (inner_add_right _ _ _).symm
      _ = ⟪b - z, b⟫_ℝ := by rw [sub_add_cancel]
theorem ConvexCone.innerDualCone_of_innerDualCone_eq_self (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDualCone : Set H).innerDualCone = K := by
  ext x
  constructor
  · rw [mem_innerDualCone, ← SetLike.mem_coe]
    contrapose!
    exact K.hyperplane_separation_of_nonempty_of_isClosed_of_nmem ne hc
  · rintro hxK y h
    specialize h x hxK
    rwa [real_inner_comm]
end CompleteSpace
end Dual