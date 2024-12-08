import Mathlib.Algebra.Order.Module.Algebra
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Tactic.Positivity.Basic
noncomputable section
section StrictOrderedCommSemiring
variable (R : Type*) [StrictOrderedCommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι : Type*) [DecidableEq ι]
def SameRay (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂
variable {R}
namespace SameRay
variable {x y z : M}
@[simp]
theorem zero_left (y : M) : SameRay R 0 y :=
  Or.inl rfl
@[simp]
theorem zero_right (x : M) : SameRay R x 0 :=
  Or.inr <| Or.inl rfl
@[nontriviality]
theorem of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y := by
  rw [Subsingleton.elim x 0]
  exact zero_left _
@[nontriviality]
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y :=
  haveI := Module.subsingleton R M
  of_subsingleton x y
@[refl]
theorem refl (x : M) : SameRay R x x := by
  nontriviality R
  exact Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)
protected theorem rfl : SameRay R x x :=
  refl _
@[symm]
theorem symm (h : SameRay R x y) : SameRay R y x :=
  (or_left_comm.1 h).imp_right <| Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩
theorem exists_pos (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
  (h.resolve_left hx).resolve_left hy
theorem sameRay_comm : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩
theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 → x = 0 ∨ z = 0) :
    SameRay R x z := by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, ?_⟩)
  rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]
variable {S : Type*} [OrderedCommSemiring S] [Algebra S R] [Module S M] [SMulPosMono S R]
  [IsScalarTower S R M] {a : S}
lemma sameRay_nonneg_smul_right (v : M) (h : 0 ≤ a) : SameRay R v (a • v) := by
  obtain h | h := (algebraMap_nonneg R h).eq_or_gt
  · rw [← algebraMap_smul R a v, h, zero_smul]
    exact zero_right _
  · refine Or.inr <| Or.inr ⟨algebraMap S R a, 1, h, by nontriviality R; exact zero_lt_one, ?_⟩
    module
lemma sameRay_nonneg_smul_left (v : M) (ha : 0 ≤ a) : SameRay R (a • v) v :=
  (sameRay_nonneg_smul_right v ha).symm
lemma sameRay_pos_smul_right (v : M) (ha : 0 < a) : SameRay R v (a • v) :=
  sameRay_nonneg_smul_right v ha.le
lemma sameRay_pos_smul_left (v : M) (ha : 0 < a) : SameRay R (a • v) v :=
  sameRay_nonneg_smul_left v ha.le
lemma nonneg_smul_right (h : SameRay R x y) (ha : 0 ≤ a) : SameRay R x (a • y) :=
  h.trans (sameRay_nonneg_smul_right y ha) fun hy => Or.inr <| by rw [hy, smul_zero]
lemma nonneg_smul_left (h : SameRay R x y) (ha : 0 ≤ a) : SameRay R (a • x) y :=
  (h.symm.nonneg_smul_right ha).symm
theorem pos_smul_right (h : SameRay R x y) (ha : 0 < a) : SameRay R x (a • y) :=
  h.nonneg_smul_right ha.le
theorem pos_smul_left (h : SameRay R x y) (hr : 0 < a) : SameRay R (a • x) y :=
  h.nonneg_smul_left hr.le
theorem map (f : M →ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y) :=
  (h.imp fun hx => by rw [hx, map_zero]) <|
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩
theorem _root_.Function.Injective.sameRay_map_iff
    {F : Type*} [FunLike F M N] [LinearMapClass F R M N]
    {f : F} (hf : Function.Injective f) :
    SameRay R (f x) (f y) ↔ SameRay R x y := by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]
@[simp]
theorem sameRay_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y :=
  Function.Injective.sameRay_map_iff (EquivLike.injective e)
theorem smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
    (h : SameRay R x y) (s : S) : SameRay R (s • x) (s • y) :=
  h.map (s • (LinearMap.id : M →ₗ[R] M))
theorem add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z := by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, ?_, ?_⟩)
  · positivity
  · convert congr(ry • $Hx + rx • $Hy) using 1 <;> module
theorem add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z) :=
  (hy.symm.add_left hz.symm).symm
end SameRay
set_option linter.unusedVariables false in
@[nolint unusedArguments]
def RayVector (R M : Type*) [Zero M] :=
  { v : M // v ≠ 0 }
instance RayVector.coe [Zero M] : CoeOut (RayVector R M) M where
  coe := Subtype.val
instance {R M : Type*} [Zero M] [Nontrivial M] : Nonempty (RayVector R M) :=
  let ⟨x, hx⟩ := exists_ne (0 : M)
  ⟨⟨x, hx⟩⟩
variable (R M)
instance RayVector.Setoid : Setoid (RayVector R M) where
  r x y := SameRay R (x : M) y
  iseqv :=
    ⟨fun _ => SameRay.refl _, fun h => h.symm, by
      intros x y z hxy hyz
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩
def Module.Ray :=
  Quotient (RayVector.Setoid R M)
variable {R M}
theorem equiv_iff_sameRay {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl
variable (R)
def rayOfNeZero (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦⟨v, h⟩⟧
theorem Module.Ray.ind {C : Module.Ray R M → Prop} (h : ∀ (v) (hv : v ≠ 0), C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotient.ind (Subtype.rec <| h) x
variable {R}
instance [Nontrivial M] : Nonempty (Module.Ray R M) :=
  Nonempty.map Quotient.mk' inferInstance
theorem ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotient.eq'
@[simp]
theorem ray_pos_smul {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r) (hrv : r • v ≠ 0) :
    rayOfNeZero R (r • v) hrv = rayOfNeZero R v h :=
  (ray_eq_iff _ _).2 <| SameRay.sameRay_pos_smul_left v hr
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm
def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  Quotient.congr (RayVector.mapLinearEquiv e) fun _ _=> (SameRay.sameRay_map_iff _).symm
@[simp]
theorem Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl
@[simp]
theorem Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.refl _ :=
  Equiv.ext <| Module.Ray.ind R fun _ _ => rfl
@[simp]
theorem Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl
section Action
variable {G : Type*} [Group G] [DistribMulAction G M]
instance {R : Type*} : MulAction G (RayVector R M) where
  smul r := Subtype.map (r • ·) fun _ => (smul_ne_zero_iff_ne _).2
  mul_smul a b _ := Subtype.ext <| mul_smul a b _
  one_smul _ := Subtype.ext <| one_smul _ _
variable [SMulCommClass R G M]
instance : MulAction G (Module.Ray R M) where
  smul r := Quotient.map (r • ·) fun _ _ h => h.smul _
  mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' <| mul_smul a b _
  one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' <| one_smul _ _
@[simp]
theorem Module.Ray.linearEquiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) :
    e • v = Module.Ray.map e v :=
  rfl
@[simp]
theorem smul_rayOfNeZero (g : G) (v : M) (hv) :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl
end Action
namespace Module.Ray
theorem units_smul_of_pos (u : Rˣ) (hu : 0 < (u.1 : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  rw [smul_rayOfNeZero, ray_eq_iff]
  exact SameRay.sameRay_pos_smul_left _ hu
def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotient.out x
@[simp]
theorem someRayVector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R M) = x :=
  Quotient.out_eq _
def someVector (x : Module.Ray R M) : M :=
  x.someRayVector
@[simp]
theorem someVector_ne_zero (x : Module.Ray R M) : x.someVector ≠ 0 :=
  x.someRayVector.property
@[simp]
theorem someVector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.someVector_ne_zero = x :=
  (congr_arg _ (Subtype.coe_eta _ _) : _).trans x.out_eq
end Module.Ray
end StrictOrderedCommSemiring
section StrictOrderedCommRing
variable {R : Type*} [StrictOrderedCommRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] {x y : M}
@[simp]
theorem sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y := by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]
alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff
theorem sameRay_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y) := by rw [← sameRay_neg_iff, neg_neg]
theorem eq_zero_of_sameRay_neg_smul_right [NoZeroSMulDivisors R M] {r : R} (hr : r < 0)
    (h : SameRay R x (r • x)) : x = 0 := by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
  · simpa [hr.ne] using h₀
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine h.resolve_left (ne_of_gt <| sub_pos.2 ?_)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁
theorem eq_zero_of_sameRay_self_neg [NoZeroSMulDivisors R M] (h : SameRay R x (-x)) : x = 0 := by
  nontriviality M; haveI : Nontrivial R := Module.nontrivial R M
  refine eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) ?_
  rwa [neg_one_smul]
namespace RayVector
instance {R : Type*} : Neg (RayVector R M) :=
  ⟨fun v => ⟨-v, neg_ne_zero.2 v.prop⟩⟩
@[simp, norm_cast]
theorem coe_neg {R : Type*} (v : RayVector R M) : ↑(-v) = -(v : M) :=
  rfl
instance {R : Type*} : InvolutiveNeg (RayVector R M) where
  neg := Neg.neg
  neg_neg v := by rw [Subtype.ext_iff, coe_neg, coe_neg, neg_neg]
@[simp]
theorem equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
  sameRay_neg_iff
end RayVector
variable (R)
instance : Neg (Module.Ray R M) :=
  ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩
@[simp]
theorem neg_rayOfNeZero (v : M) (h : v ≠ 0) :
    -rayOfNeZero R _ h = rayOfNeZero R (-v) (neg_ne_zero.2 h) :=
  rfl
namespace Module.Ray
variable {R}
instance : InvolutiveNeg (Module.Ray R M) where
  neg := Neg.neg
  neg_neg x := by apply ind R (by simp) x
theorem ne_neg_self [NoZeroSMulDivisors R M] (x : Module.Ray R M) : x ≠ -x := by
  induction' x using Module.Ray.ind with x hx
  rw [neg_rayOfNeZero, Ne, ray_eq_iff]
  exact mt eq_zero_of_sameRay_self_neg hx
theorem neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v) := by
  induction v using Module.Ray.ind
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]
theorem units_smul_of_neg (u : Rˣ) (hu : u.1 < 0) (v : Module.Ray R M) : u • v = -v := by
  rw [← neg_inj, neg_neg, ← neg_units_smul, units_smul_of_pos]
  rwa [Units.val_neg, Right.neg_pos_iff]
@[simp]
protected theorem map_neg (f : M ≃ₗ[R] N) (v : Module.Ray R M) : map f (-v) = -map f v := by
  induction' v using Module.Ray.ind with g hg
  simp
end Module.Ray
end StrictOrderedCommRing
section LinearOrderedCommRing
variable {R : Type*} [LinearOrderedCommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
theorem sameRay_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ MulAction.orbit ↥(Units.posSubgroup R) v₂) :
    SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  exact SameRay.sameRay_pos_smul_left _ hr
@[simp]
theorem units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v :=
  have := mul_self_pos.2 u.ne_zero
  calc
    u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm <| (u⁻¹ • v).units_smul_of_pos _ (by exact this)
    _ = u • v := by rw [mul_smul, smul_inv_smul]
section
variable [NoZeroSMulDivisors R M]
@[simp]
theorem sameRay_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 ≤ r ∨ v = 0 :=
  ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩
theorem sameRay_smul_right_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R v (r • v) ↔ 0 < r := by
  simp only [sameRay_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]
@[simp]
theorem sameRay_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 ≤ r ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_smul_right_iff
theorem sameRay_smul_left_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R (r • v) v ↔ 0 < r :=
  SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)
@[simp]
theorem sameRay_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r ≤ 0 ∨ v = 0 := by
  rw [← sameRay_neg_iff, neg_neg, ← neg_smul, sameRay_smul_right_iff, neg_nonneg]
theorem sameRay_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (-v) (r • v) ↔ r < 0 := by
  simp only [sameRay_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]
@[simp]
theorem sameRay_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r ≤ 0 ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff
theorem sameRay_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (r • v) (-v) ↔ r < 0 :=
  SameRay.sameRay_comm.trans <| sameRay_neg_smul_right_iff_of_ne hv hr
@[simp]
theorem units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ 0 < u.1 := by
  induction' v using Module.Ray.ind with v hv
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]
@[simp]
theorem units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ u.1 < 0 := by
  rw [← neg_inj, neg_neg, ← Module.Ray.neg_units_smul, units_smul_eq_self_iff, Units.val_neg,
    neg_pos]
theorem sameRay_or_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  simp_rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
    · exact False.elim (hy hy0)
    · refine ⟨![r₁, -r₂], ?_⟩
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
    · exact False.elim (hx hx0)
    · exact False.elim (hy (neg_eq_zero.1 hy0))
    · refine ⟨![r₁, r₂], ?_⟩
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
  · rcases h with ⟨m, hm, hmne⟩
    rw [Fin.sum_univ_two, add_eq_zero_iff_eq_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm1, hx, hm0.ne] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm0, hy, hm1.ne] at hm
    · rw [Fin.exists_fin_two] at hmne
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
    · exfalso
      simp [hm0, hy, hm1.ne.symm] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      rwa [neg_smul]
    · exfalso
      simp [hm1, hx, hm0.ne.symm] at hm
    · refine Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, ?_⟩))
      rwa [smul_neg]
theorem sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0 <;> simp [hx, hy]
end
end LinearOrderedCommRing
namespace SameRay
variable {R : Type*} [LinearOrderedField R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y v₁ v₂ : M}
theorem exists_pos_left (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ r • x = y :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩
theorem exists_pos_right (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ x = r • y :=
  (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm
theorem exists_nonneg_left (h : SameRay R x y) (hx : x ≠ 0) : ∃ r : R, 0 ≤ r ∧ r • x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt
theorem exists_nonneg_right (h : SameRay R x y) (hy : y ≠ 0) : ∃ r : R, 0 ≤ r ∧ x = r • y :=
  (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm
theorem exists_eq_smul_add (h : SameRay R v₁ v₂) :
    ∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) := by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
  · use 1, 0
    simp
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, ?_, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
theorem exists_eq_smul (h : SameRay R v₁ v₂) :
    ∃ (u : M) (a b : R), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
  ⟨v₁ + v₂, h.exists_eq_smul_add⟩
end SameRay
section LinearOrderedField
variable {R : Type*} [LinearOrderedField R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y : M}
theorem exists_pos_left_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_pos_left hx hy⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_pos_smul_right x hr
theorem exists_pos_left_iff_sameRay_and_ne_zero (hx : x ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y ≠ 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hx, hr.le, hr.ne']
  · rintro ⟨hxy, hy⟩
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy
theorem exists_nonneg_left_iff_sameRay (hx : x ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_nonneg_left hx⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_nonneg_smul_right x hr
theorem exists_pos_right_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay hy hx
theorem exists_pos_right_iff_sameRay_and_ne_zero (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y ∧ x ≠ 0 := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay_and_ne_zero hy
theorem exists_nonneg_right_iff_sameRay (hy : y ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_nonneg_left_iff_sameRay (R := R) hy
end LinearOrderedField