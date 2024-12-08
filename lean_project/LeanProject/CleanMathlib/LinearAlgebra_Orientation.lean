import Mathlib.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.Determinant
noncomputable section
section OrderedCommSemiring
variable (R : Type*) [StrictOrderedCommSemiring R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι ι' : Type*)
abbrev Orientation := Module.Ray R (M [⋀^ι]→ₗ[R] R)
class Module.Oriented where
  positiveOrientation : Orientation R M ι
export Module.Oriented (positiveOrientation)
variable {R M}
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e
@[simp]
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι]→ₗ[R] R) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.compLinearEquiv_eq_zero_iff e.symm).mp hv) :=
  rfl
@[simp]
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map, AlternatingMap.domLCongr_refl, Module.Ray.map_refl]
@[simp]
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm := rfl
section Reindex
variable (R M) {ι ι'}
def Orientation.reindex (e : ι ≃ ι') : Orientation R M ι ≃ Orientation R M ι' :=
  Module.Ray.map <| AlternatingMap.domDomCongrₗ R e
@[simp]
theorem Orientation.reindex_apply (e : ι ≃ ι') (v : M [⋀^ι]→ₗ[R] R) (hv : v ≠ 0) :
    Orientation.reindex R M e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.domDomCongr e) (mt (v.domDomCongr_eq_zero_iff e).mp hv) :=
  rfl
@[simp]
theorem Orientation.reindex_refl : (Orientation.reindex R M <| Equiv.refl ι) = Equiv.refl _ := by
  rw [Orientation.reindex, AlternatingMap.domDomCongrₗ_refl, Module.Ray.map_refl]
@[simp]
theorem Orientation.reindex_symm (e : ι ≃ ι') :
    (Orientation.reindex R M e).symm = Orientation.reindex R M e.symm :=
  rfl
end Reindex
instance (priority := 100) IsEmpty.oriented [IsEmpty ι] : Module.Oriented R M ι where
  positiveOrientation :=
    rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1) <|
      AlternatingMap.constLinearEquivOfIsEmpty.injective.ne (by exact one_ne_zero)
@[simp]
theorem Orientation.map_positiveOrientation_of_isEmpty [IsEmpty ι] (f : M ≃ₗ[R] N) :
    Orientation.map ι f positiveOrientation = positiveOrientation := rfl
@[simp]
theorem Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x := by
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]
end OrderedCommSemiring
section OrderedCommRing
variable {R : Type*} [StrictOrderedCommRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
@[simp]
protected theorem Orientation.map_neg {ι : Type*} (f : M ≃ₗ[R] N) (x : Orientation R M ι) :
    Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x
@[simp]
protected theorem Orientation.reindex_neg {ι ι' : Type*} (e : ι ≃ ι') (x : Orientation R M ι) :
    Orientation.reindex R M e (-x) = -Orientation.reindex R M e x :=
  Module.Ray.map_neg _ x
namespace Basis
variable {ι ι' : Type*}
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x := by
  cases nonempty_fintype ι
  letI := Classical.decEq ι
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply, smul_rayOfNeZero, ray_eq_iff, Units.smul_def,
    (g.compLinearMap f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply,
    show (fun i ↦ (LinearEquiv.symm f).toLinearMap (e i)) = (LinearEquiv.symm f).toLinearMap ∘ e
    by rfl, Basis.det_comp, Basis.det_self, mul_one, smul_eq_mul, mul_comm, mul_smul,
    LinearEquiv.coe_inv_det]
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
protected def orientation (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
theorem orientation_map (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).orientation = Orientation.map ι f e.orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']
theorem orientation_reindex (e : Basis ι R M) (eι : ι ≃ ι') :
    (e.reindex eι).orientation = Orientation.reindex R M eι e.orientation := by
  simp_rw [Basis.orientation, Orientation.reindex_apply, Basis.det_reindex']
theorem orientation_unitsSMul (e : Basis ι R M) (w : ι → Units R) :
    (e.unitsSMul w).orientation = (∏ i, w i)⁻¹ • e.orientation := by
  rw [Basis.orientation, Basis.orientation, smul_rayOfNeZero, ray_eq_iff,
    e.det.eq_smul_basis_det (e.unitsSMul w), det_unitsSMul_self, Units.smul_def, smul_smul]
  norm_cast
  simp only [inv_mul_cancel, Units.val_one, one_smul]
  exact SameRay.rfl
@[simp]
theorem orientation_isEmpty [IsEmpty ι] (b : Basis ι R M) :
    b.orientation = positiveOrientation := by
  rw [Basis.orientation]
  congr
  exact b.det_isEmpty
end Basis
end OrderedCommRing
section LinearOrderedCommRing
variable {R : Type*} [LinearOrderedCommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}
namespace Orientation
theorem eq_or_eq_neg_of_isEmpty [IsEmpty ι] (o : Orientation R M ι) :
    o = positiveOrientation ∨ o = -positiveOrientation := by
  induction' o using Module.Ray.ind with x hx
  dsimp [positiveOrientation]
  simp only [ray_eq_iff, sameRay_neg_swap]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  set f : (M [⋀^ι]→ₗ[R] R) ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  have H : LinearIndependent R ![f x, 1] := by
    convert h.map' f.toLinearMap f.ker
    ext i
    fin_cases i <;> simp [f]
  rw [linearIndependent_iff'] at H
  simpa using H Finset.univ ![1, -f x] (by simp [Fin.sum_univ_succ]) 0 (by simp)
end Orientation
namespace Basis
variable [Fintype ι] [DecidableEq ι]
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.orientation ∨ x = -e.orientation := by
  induction' x using Module.Ray.ind with x hx
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_iff_ne, ne_comm]
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x ≠ e.orientation ↔ x = -e.orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩
theorem orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = e.orientation ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = -e.orientation ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
    LinearEquiv.coe_det]
@[simp]
theorem orientation_neg_single (e : Basis ι R M) (i : ι) :
    (e.unitsSMul (Function.update 1 i (-1))).orientation = -e.orientation := by
  rw [orientation_unitsSMul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp
def adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))
@[simp]
theorem orientation_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).orientation = x := by
  rw [adjustToOrientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h
theorem adjustToOrientation_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  rw [adjustToOrientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]
theorem det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det := by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp only [e.det_unitsSMul, ne_eq, Finset.mem_univ, Finset.prod_update_of_mem, not_true,
      Pi.one_apply, Finset.prod_const_one, mul_one, inv_neg', inv_one, Units.val_neg, Units.val_one]
    ext
    simp
@[simp]
theorem abs_det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι → M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  cases' e.det_adjustToOrientation x with h h <;> simp [h]
end Basis
end LinearOrderedCommRing
section LinearOrderedField
variable {R : Type*} [LinearOrderedField R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}
namespace Orientation
variable [Fintype ι]
open FiniteDimensional Module
theorem eq_or_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  letI := Classical.decEq ι
  have orientation_neg_neg :
      ∀ f : Basis ι R M, - -Basis.orientation f = Basis.orientation f := by
    #adaptation_note
    set_option maxSynthPendingDepth 2 in simp
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂, orientation_neg_neg]
theorem ne_iff_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩
theorem map_eq_det_inv_smul [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x :=
  haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f
theorem map_eq_iff_det_pos [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := of_finrank_pos H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]
def someBasis [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x
@[simp]
theorem someBasis_orientation [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
    (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : (x.someBasis h).orientation = x :=
  Basis.orientation_adjustToOrientation _ _
end Orientation
end LinearOrderedField