import Mathlib.Algebra.Exact
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TensorProduct.Basic
section Modules
open TensorProduct LinearMap
section Semiring
variable {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M →ₗ[R] N} (g : N →ₗ[R] P)
lemma le_comap_range_lTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨q ⊗ₜ[R] n, rfl⟩
lemma le_comap_range_rTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (rTensor Q g)).comap
      ((TensorProduct.mk R P Q).flip q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n ⊗ₜ[R] q, rfl⟩
variable (Q) {g}
theorem LinearMap.lTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (lTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q ⊗ₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
theorem LinearMap.lTensor_range :
    range (lTensor Q g) =
      range (lTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [lTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply lTensor_surjective
  rw [← range_eq_top, range_rangeRestrict]
theorem LinearMap.rTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (rTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n ⊗ₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
theorem LinearMap.rTensor_range :
    range (rTensor Q g) =
      range (rTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [rTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply rTensor_surjective
  rw [← range_eq_top, range_rangeRestrict]
lemma LinearMap.rTensor_exact_iff_lTensor_exact :
    Function.Exact (f.rTensor Q) (g.rTensor Q) ↔
    Function.Exact (f.lTensor Q) (g.lTensor Q) :=
  Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
    (by ext; simp) (by ext; simp)
end Semiring
variable {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
open Function
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hfg : Exact f g) (hg : Function.Surjective g)
noncomputable def lTensor.toFun (hfg : Exact f g) :
    Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) →ₗ[R] Q ⊗[R] P :=
  Submodule.liftQ _ (lTensor Q g) <| by
    rw [LinearMap.range_le_iff_comap, ← LinearMap.ker_comp,
      ← lTensor_comp, hfg.linearMap_comp_eq_zero, lTensor_zero, ker_zero]
noncomputable def lTensor.inverse_of_rightInverse {h : P → N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  TensorProduct.lift <| LinearMap.flip <| {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
    map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (p + p')) - (q ⊗ₜ[R] (h p) + q ⊗ₜ[R] (h p')) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (r • p)) - r • q ⊗ₜ[R] (h p) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }
lemma lTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : Q ⊗[R] N) :
    (lTensor.inverse_of_rightInverse Q hfg hgh) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp? [lTensor.inverse_of_rightInverse] says
    simp only [inverse_of_rightInverse, coe_comp, Function.comp_apply, lTensor_tmul,
      lift.tmul, flip_apply, coe_mk, AddHom.coe_mk, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]
lemma lTensor.inverse_of_rightInverse_comp_lTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (lTensor.inverse_of_rightInverse Q hfg hgh).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]
noncomputable
def lTensor.inverse :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_apply]
lemma lTensor.inverse_comp_lTensor :
    (lTensor.inverse Q hfg hg).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_comp_lTensor]
noncomputable
def lTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) := {
  toLinearMap := lTensor.toFun Q hfg
  invFun    := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv  := fun y ↦ by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor_surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }
noncomputable def lTensor.equiv :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) :=
  lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
include hfg hg in
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [exact_iff, ← Submodule.ker_mkQ (p := range (lTensor Q f)),
    ← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective
lemma lTensor_mkQ (N : Submodule R M) :
    ker (lTensor Q (N.mkQ)) = range (lTensor Q N.subtype) := by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
noncomputable def rTensor.toFun (hfg : Exact f g) :
    N ⊗[R] Q ⧸ range (rTensor Q f) →ₗ[R] P ⊗[R] Q :=
  Submodule.liftQ _ (rTensor Q g) <| by
    rw [range_le_iff_comap, ← ker_comp, ← rTensor_comp,
      hfg.linearMap_comp_eq_zero, rTensor_zero, ker_zero]
noncomputable def rTensor.inverse_of_rightInverse {h : P → N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  TensorProduct.lift  {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
    map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (p + p') ⊗ₜ[R] q - (h p ⊗ₜ[R] q + h p' ⊗ₜ[R] q) ∈ range (rTensor Q f)
      rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (r • p) ⊗ₜ[R] q - r • h p ⊗ₜ[R] q ∈ range (rTensor Q f)
      rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }
lemma rTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : N ⊗[R] Q) :
    (rTensor.inverse_of_rightInverse Q hfg hgh) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp? [rTensor.inverse_of_rightInverse] says
    simp only [inverse_of_rightInverse, coe_comp, Function.comp_apply, rTensor_tmul,
      lift.tmul, coe_mk, AddHom.coe_mk, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]
lemma rTensor.inverse_of_rightInverse_comp_rTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (rTensor.inverse_of_rightInverse Q hfg hgh).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]
noncomputable
def rTensor.inverse :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
    (rTensor.inverse Q hfg hg) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_apply]
lemma rTensor.inverse_comp_rTensor :
    (rTensor.inverse Q hfg hg).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_comp_rTensor]
noncomputable
def rTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((N ⊗[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) := {
  toLinearMap := rTensor.toFun Q hfg
  invFun      := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv    := fun y ↦ by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv   := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor_surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }
noncomputable def rTensor.equiv :
    ((N ⊗[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) :=
  rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)
include hfg hg in
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [rTensor_exact_iff_lTensor_exact]
  exact lTensor_exact Q hfg hg
lemma rTensor_mkQ (N : Submodule R M) :
    ker (rTensor Q (N.mkQ)) = range (rTensor Q N.subtype) := by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
variable {M' N' P' : Type*}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M'] [Module R N'] [Module R P']
    {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}
    (hfg' : Exact f' g') (hg' : Function.Surjective g')
include hg hg' in
theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← lTensor_comp_rTensor, coe_comp]
  exact Function.Surjective.comp (lTensor_surjective _ hg') (rTensor_surjective _ hg)
include hg hg' hfg hfg' in
theorem TensorProduct.map_ker :
    ker (TensorProduct.map g g') = range (lTensor N f') ⊔ range (rTensor N' f) := by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map, ← Submodule.map_comp, rTensor_comp_lTensor,
    Submodule.map_top]
  rw [← lTensor_comp_rTensor, range_eq_map, Submodule.map_comp,
    Submodule.map_top]
  rw [range_eq_top.mpr (rTensor_surjective M' hg), Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]
variable (M)
variable (R) in
theorem TensorProduct.mk_surjective (S) [Semiring S] [Algebra R S]
    (h : Surjective (algebraMap R S)) :
    Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact ⟨x • y, rfl⟩
end Modules
section Algebras
open Algebra.TensorProduct
open scoped TensorProduct
variable
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
lemma Ideal.map_includeLeft_eq (I : Ideal A) :
    (I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.rTensor B (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Submodule.carrier_inj]
  apply le_antisymm
  · intro x
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem, LinearMap.mem_range]
    intro hx
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ ⊗ₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) ⊗ₜ[R] (b * y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          with_unfolding_all rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
        suffices (a : A) ⊗ₜ[R] b = ((1 : A) ⊗ₜ[R] b) * ((a : A) ⊗ₜ[R] (1 : B)) by
          simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
            Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem]
          rw [this]
          apply Ideal.mul_mem_left
          apply Ideal.mem_map_of_mem includeLeft
          exact Submodule.coe_mem a
        simp only [Submodule.coe_restrictScalars, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy
lemma Ideal.map_includeRight_eq (I : Ideal B) :
    (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Submodule.carrier_inj]
  apply le_antisymm
  · intro x
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem, LinearMap.mem_range]
    intro hx
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 ⊗ₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) ⊗ₜ[R] (b •y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        suffices a ⊗ₜ[R] (b : B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] (b : B)) by
          rw [this]
          simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
            Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem]
          apply Ideal.mul_mem_left
          apply Ideal.mem_map_of_mem includeRight
          exact Submodule.coe_mem b
        simp only [Submodule.coe_restrictScalars, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy
variable {R : Type*} [CommRing R]
  {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  (f : A →ₐ[R] B) (g : C →ₐ[R] D)
lemma Algebra.TensorProduct.lTensor_ker (hg : Function.Surjective g) :
    RingHom.ker (map (AlgHom.id R A) g) =
      (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map (AlgHom.id R A) g)).restrictScalars R =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this, Ideal.map_includeRight_eq]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl
lemma Algebra.TensorProduct.rTensor_ker (hf : Function.Surjective f) :
    RingHom.ker (map f (AlgHom.id R C)) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map f (AlgHom.id R C))).restrictScalars R =
    LinearMap.ker (LinearMap.rTensor C (AlgHom.toLinearMap f)) := rfl
  rw [this, Ideal.map_includeLeft_eq]
  rw [(rTensor_exact C f.toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl
theorem Algebra.TensorProduct.map_ker (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RingHom.ker (map f g) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) ⊔
        (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id R A) g) := ext rfl rfl
  rw [this]
  simp only [AlgHom.coe_ker, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.coe_ker]
  rw [← Algebra.TensorProduct.lTensor_ker _ hg, RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective (map (AlgHom.id R A) g) (LinearMap.lTensor_surjective A hg)]
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom, Algebra.TensorProduct.map_comp_includeLeft]
  rfl
end Algebras