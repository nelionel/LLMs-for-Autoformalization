import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.Reflection
open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)
noncomputable section
variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
structure RootPairing extends PerfectPairing R M N where
  root : ι ↪ M
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    root j - toPerfectPairing (root j) (coroot i) • root i = root (reflection_perm i j)
  reflection_perm_coroot : ∀ i j,
    coroot j - toPerfectPairing (root i) (coroot j) • coroot i = coroot (reflection_perm i j)
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂
structure RootSystem extends RootPairing ι R M N where
  span_eq_top : span R (range root) = ⊤
attribute [simp] RootSystem.span_eq_top
namespace RootPairing
variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)
lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h, map_zero] using P.root_coroot_two i
lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i
@[simp]
lemma toLin_toPerfectPairing (x : M) (y : N) : P.toLin x y = P.toPerfectPairing x y :=
  rfl
protected def flip : RootPairing ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    reflection_perm := P.reflection_perm
    reflection_perm_root := P.reflection_perm_coroot
    reflection_perm_coroot := P.reflection_perm_root }
@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl
abbrev root' (i : ι) : Dual R N := P.toPerfectPairing (P.root i)
abbrev coroot' (i : ι) : Dual R M := P.toPerfectPairing.flip (P.coroot i)
def pairing : R := P.root' i (P.coroot j)
@[simp]
lemma root_coroot_eq_pairing : P.toPerfectPairing (P.root i) (P.coroot j) = P.pairing i j :=
  rfl
@[simp]
lemma root'_coroot_eq_pairing : P.root' i (P.coroot j) = P.pairing i j :=
  rfl
@[simp]
lemma root_coroot'_eq_pairing : P.coroot' i (P.root j) = P.pairing j i :=
  rfl
lemma coroot_root_eq_pairing : P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp
@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i
lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)
@[simp]
lemma root_reflection_perm (j : ι) :
    P.root (P.reflection_perm i j) = (P.reflection i) (P.root j) :=
  (P.reflection_perm_root i j).symm
theorem mapsTo_reflection_root :
    MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)
lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.coroot' i x) • P.root i :=
  rfl
lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl
@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)
@[simp]
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x
@[simp]
lemma reflection_inv :
    (P.reflection i)⁻¹ = P.reflection i :=
  rfl
@[simp]
lemma reflection_sq :
    P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl
@[simp]
lemma reflection_perm_sq :
    P.reflection_perm i ^ 2 = 1 := by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflection_perm, reflection_same, Equiv.Perm.one_apply]
@[simp]
lemma reflection_perm_inv :
    (P.reflection_perm i)⁻¹ = P.reflection_perm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflection_perm_sq i).symm
@[simp]
lemma reflection_perm_self : P.reflection_perm i (P.reflection_perm i j) = j := by
  apply P.root.injective
  simp only [root_reflection_perm, reflection_same]
lemma reflection_perm_involutive : Involutive (P.reflection_perm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)
@[simp]
lemma reflection_perm_symm : (P.reflection_perm i).symm = P.reflection_perm i :=
  Involutive.symm_eq_self_of_involutive (P.reflection_perm i) <| P.reflection_perm_involutive i
lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  Module.bijOn_reflection_of_mapsTo _ <| P.mapsTo_reflection_root i
@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)
@[simp]
lemma coroot_reflection_perm (j : ι) :
    P.coroot (P.reflection_perm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflection_perm_coroot i j).symm
theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)
lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.root' i) f • P.coroot i :=
  rfl
lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl
@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)
@[simp]
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x
@[simp]
lemma coreflection_inv :
    (P.coreflection i)⁻¹ = P.coreflection i :=
  rfl
@[simp]
lemma coreflection_sq :
    P.coreflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl
lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i
@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq
lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl
lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toPerfectPairing m (P.coroot i))]
lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflection_perm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflection_perm, hk]
lemma coroot'_reflection_perm {i j : ι} :
    P.coroot' (P.reflection_perm i j) = P.coroot' j ∘ₗ P.reflection i := by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]
lemma coroot'_reflection {i j : ι} (y : M) :
    P.coroot' j (P.reflection i y) = P.coroot' (P.reflection_perm i j) y :=
  (LinearMap.congr_fun P.coroot'_reflection_perm y).symm
lemma pairing_reflection_perm (i j k : ι) :
    P.pairing j (P.reflection_perm i k) = P.pairing (P.reflection_perm i j) k := by
  simp only [pairing, root', coroot_reflection_perm, root_reflection_perm]
  simp only [coreflection_apply_coroot, map_sub, map_smul, smul_eq_mul,
    reflection_apply_root]
  simp only [← toLin_toPerfectPairing, map_smul, LinearMap.smul_apply, map_sub, map_smul,
    LinearMap.sub_apply, smul_eq_mul]
  simp only [PerfectPairing.toLin_apply, root'_coroot_eq_pairing, sub_right_inj, mul_comm]
@[simp]
lemma pairing_reflection_perm_self_left (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflection_perm i i) j = - P.pairing i j := by
  rw [pairing, root', ← reflection_perm_root, root'_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, ← toLin_toPerfectPairing, LinearMap.map_neg₂, toLin_toPerfectPairing,
    root'_coroot_eq_pairing]
@[simp]
lemma pairing_reflection_perm_self_right (i j : ι) :
    P.pairing i (P.reflection_perm j j) = - P.pairing i j := by
  rw [pairing, ← reflection_perm_coroot, root_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, ← toLin_toPerfectPairing, map_neg, toLin_toPerfectPairing,
    root_coroot_eq_pairing]
def IsCrystallographic : Prop :=
  ∀ i, MapsTo (P.root' i) (range P.coroot) (zmultiples (1 : R))
lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j := by
  rw [IsCrystallographic]
  refine ⟨fun h i j ↦ ?_, fun h i _ ⟨j, hj⟩ ↦ ?_⟩
  · simpa [AddSubgroup.mem_zmultiples_iff] using h i (mem_range_self j)
  · simpa [← hj, AddSubgroup.mem_zmultiples_iff] using h i j
variable {P} in
lemma IsCrystallographic.flip (h : P.IsCrystallographic) :
    P.flip.IsCrystallographic := by
  rw [isCrystallographic_iff, forall_comm]
  exact P.isCrystallographic_iff.mp h
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)
lemma isReduced_iff : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg P.root h')
    · exact Or.inr (h i j h' hLin)
abbrev rootSpan := span R (range P.root)
abbrev corootSpan := span R (range P.coroot)
def weylGroup : Subgroup (M ≃ₗ[R] M) :=
  Subgroup.closure (range P.reflection)
lemma reflection_mem_weylGroup : P.reflection i ∈ P.weylGroup :=
  Subgroup.subset_closure <| mem_range_self i
lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r ∈ range P.reflection) (hα : α ∈ range P.root) :
    r • α ∈ range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.root_reflection_perm i j⟩
lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r ∈ range P.coreflection) (hα : α ∈ range P.coroot) :
    r • α ∈ range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.coroot_reflection_perm i j⟩
lemma exists_root_eq_smul_of_mem_weylGroup {w : M ≃ₗ[R] M} (hw : w ∈ P.weylGroup) (i : ι) :
    ∃ j, P.root j = w • P.root i :=
  Subgroup.smul_mem_of_mem_closure_of_mem (by simp)
    (fun _ h _ ↦ P.mem_range_root_of_mem_range_reflection_of_mem_range_root h) hw (mem_range_self i)
def weylGroupToPerm : P.weylGroup →* Equiv.Perm ι where
  toFun w :=
  { toFun := fun i => (P.exists_root_eq_smul_of_mem_weylGroup w.2 i).choose
    invFun := fun i => (P.exists_root_eq_smul_of_mem_weylGroup w⁻¹.2 i).choose
    left_inv := fun i => by
      obtain ⟨w, hw⟩ := w
      apply P.root.injective
      rw [(P.exists_root_eq_smul_of_mem_weylGroup ((Subgroup.inv_mem_iff P.weylGroup).mpr hw)
          ((P.exists_root_eq_smul_of_mem_weylGroup hw i).choose)).choose_spec,
        (P.exists_root_eq_smul_of_mem_weylGroup hw i).choose_spec, inv_smul_smul]
    right_inv := fun i => by
      obtain ⟨w, hw⟩ := w
      have hw' : w⁻¹ ∈ P.weylGroup := (Subgroup.inv_mem_iff P.weylGroup).mpr hw
      apply P.root.injective
      rw [(P.exists_root_eq_smul_of_mem_weylGroup hw
          ((P.exists_root_eq_smul_of_mem_weylGroup hw' i).choose)).choose_spec,
        (P.exists_root_eq_smul_of_mem_weylGroup hw' i).choose_spec, smul_inv_smul] }
  map_one' := by ext; simp
  map_mul' x y := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    ext i
    apply P.root.injective
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, comp_apply]
    rw [(P.exists_root_eq_smul_of_mem_weylGroup (mul_mem hx hy) i).choose_spec,
      (P.exists_root_eq_smul_of_mem_weylGroup hx
        ((P.exists_root_eq_smul_of_mem_weylGroup hy i).choose)).choose_spec,
      (P.exists_root_eq_smul_of_mem_weylGroup hy i).choose_spec, mul_smul]
@[simp]
lemma weylGroupToPerm_apply_reflection :
    P.weylGroupToPerm ⟨P.reflection i, P.reflection_mem_weylGroup i⟩ = P.reflection_perm i := by
  ext j
  apply P.root.injective
  rw [weylGroupToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, root_reflection_perm,
    (P.exists_root_eq_smul_of_mem_weylGroup (P.reflection_mem_weylGroup i) j).choose_spec,
    LinearEquiv.smul_def]
@[simp]
lemma range_weylGroupToPerm :
    P.weylGroupToPerm.range = Subgroup.closure (range P.reflection_perm) := by
  refine (Subgroup.closure_eq_of_le _ ?_ ?_).symm
  · rintro - ⟨i, rfl⟩
    simpa only [← weylGroupToPerm_apply_reflection] using mem_range_self _
  · rintro - ⟨⟨w, hw⟩, rfl⟩
    induction hw using Subgroup.closure_induction'' with
    | one =>
      change P.weylGroupToPerm 1 ∈ _
      simpa only [map_one] using Subgroup.one_mem _
    | mem w' hw' =>
      obtain ⟨i, rfl⟩ := hw'
      simpa only [weylGroupToPerm_apply_reflection] using Subgroup.subset_closure (mem_range_self i)
    | inv_mem w' hw' =>
      obtain ⟨i, rfl⟩ := hw'
      simpa only [reflection_inv, weylGroupToPerm_apply_reflection] using
        Subgroup.subset_closure (mem_range_self i)
    | mul w₁ w₂ hw₁ hw₂ h₁ h₂ =>
      simpa only [← Submonoid.mk_mul_mk _ w₁ w₂ hw₁ hw₂, map_mul] using Subgroup.mul_mem _ h₁ h₂
lemma pairing_smul_root_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflection_perm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h
lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflection_perm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h
lemma two_nsmul_reflection_eq_of_perm_eq (hij : P.reflection_perm i = P.reflection_perm j) :
    2 • ⇑(P.reflection i) = 2 • P.reflection j := by
  ext x
  suffices 2 • P.toLin x (P.coroot i) • P.root i = 2 • P.toLin x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLin x (P.coroot i) • P.root i
      = P.toLin x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLin x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLin x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLin x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLin x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
lemma reflection_perm_eq_reflection_perm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M → M) 2 := IsSMulRegular.pi fun _ ↦ h2
  exact h2 <| P.two_nsmul_reflection_eq_of_perm_eq i j h
lemma reflection_perm_eq_reflection_perm_iff_of_span :
    P.reflection_perm i = P.reflection_perm j ↔
    ∀ x ∈ span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflection_perm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]
lemma _root_.RootSystem.reflection_perm_eq_reflection_perm_iff (P : RootSystem ι R M N) (i j : ι) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  ext x
  exact (P.reflection_perm_eq_reflection_perm_iff_of_span i j).mp h x <| by simp
def coxeterWeight : R := pairing P i j * pairing P j i
lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]
lemma exists_int_eq_coxeterWeight (h : P.IsCrystallographic) (i j : ι) :
    ∃ z : ℤ, P.coxeterWeight i j = z := by
  obtain ⟨a, ha⟩ := P.isCrystallographic_iff.mp h i j
  obtain ⟨b, hb⟩ := P.isCrystallographic_iff.mp h j i
  exact ⟨a * b, by simp [coxeterWeight, ha, hb]⟩
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0
lemma IsOrthogonal.symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]
lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [commute_iff_eq]
  ext v
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  erw [LinearMap.mul_apply, LinearMap.mul_apply]
  simp only [LinearEquiv.coe_coe, reflection_apply, PerfectPairing.flip_apply_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel
end RootPairing