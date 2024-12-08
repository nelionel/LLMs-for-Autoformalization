import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
suppress_compilation
section KaehlerDifferential
open scoped TensorProduct
open Algebra Finsupp
universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
abbrev KaehlerDifferential.ideal : Ideal (S ⊗[R] S) :=
  RingHom.ker (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)
variable {S}
theorem KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (a : S) :
    (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ KaehlerDifferential.ideal R S := by simp [RingHom.mem_ker]
variable {R}
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
def Derivation.tensorProductTo (D : Derivation R S M) : S ⊗[R] S →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.lsmul S (S →ₗ[R] M)).flip D.toLinearMap)
theorem Derivation.tensorProductTo_tmul (D : Derivation R S M) (s t : S) :
    D.tensorProductTo (s ⊗ₜ t) = s • D t := rfl
theorem Derivation.tensorProductTo_mul (D : Derivation R S M) (x y : S ⊗[R] S) :
    D.tensorProductTo (x * y) =
      TensorProduct.lmul' (S := S) R x • D.tensorProductTo y +
        TensorProduct.lmul' (S := S) R y • D.tensorProductTo x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rw [zero_mul, map_zero, map_zero, zero_smul, smul_zero, add_zero]
  swap
  · intro x₁ y₁ h₁ h₂
    rw [add_mul, map_add, map_add, map_add, add_smul, smul_add, h₁, h₂, add_add_add_comm]
  intro x₁ x₂
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · rw [mul_zero, map_zero, map_zero, zero_smul, smul_zero, add_zero]
  swap
  · intro x₁ y₁ h₁ h₂
    rw [mul_add, map_add, map_add, map_add, add_smul, smul_add, h₁, h₂, add_add_add_comm]
  intro x y
  simp only [TensorProduct.tmul_mul_tmul, Derivation.tensorProductTo,
    TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul',
    TensorProduct.lmul'_apply_tmul]
  dsimp
  rw [D.leibniz]
  simp only [smul_smul, smul_add, mul_comm (x * y) x₁, mul_right_comm x₁ x₂, ← mul_assoc]
variable (R S)
theorem KaehlerDifferential.submodule_span_range_eq_ideal :
    Submodule.span S (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
      (KaehlerDifferential.ideal R S).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
  · rintro x (hx : _ = _)
    have : x - TensorProduct.lmul' (S := S) R x ⊗ₜ[R] (1 : S) = x := by
      rw [hx, TensorProduct.zero_tmul, sub_zero]
    rw [← this]
    clear this hx
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rw [map_zero, TensorProduct.zero_tmul, sub_zero]; exact zero_mem _
    · intro x y
      have : x ⊗ₜ[R] y - (x * y) ⊗ₜ[R] (1 : S) = x • ((1 : S) ⊗ₜ y - y ⊗ₜ (1 : S)) := by
        simp_rw [smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.lmul'_apply_tmul, this]
      refine Submodule.smul_mem _ x ?_
      apply Submodule.subset_span
      exact Set.mem_range_self y
    · intro x y hx hy
      rw [map_add, TensorProduct.add_tmul, ← sub_add_sub_comm]
      exact add_mem hx hy
theorem KaehlerDifferential.span_range_eq_ideal :
    Ideal.span (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
      KaehlerDifferential.ideal R S := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
  · change (KaehlerDifferential.ideal R S).restrictScalars S ≤ (Ideal.span _).restrictScalars S
    rw [← KaehlerDifferential.submodule_span_range_eq_ideal, Ideal.span]
    conv_rhs => rw [← Submodule.span_span_of_tower S]
    exact Submodule.subset_span
def KaehlerDifferential : Type v :=
  (KaehlerDifferential.ideal R S).Cotangent
instance : AddCommGroup (KaehlerDifferential R S) := inferInstanceAs <|
  AddCommGroup (KaehlerDifferential.ideal R S).Cotangent
instance KaehlerDifferential.module : Module (S ⊗[R] S) (KaehlerDifferential R S) :=
  Ideal.Cotangent.moduleOfTower _
@[inherit_doc KaehlerDifferential]
notation:100 "Ω[" S "⁄" R "]" => KaehlerDifferential R S
instance : Nonempty (Ω[S⁄R]) := ⟨0⟩
instance KaehlerDifferential.module' {R' : Type*} [CommRing R'] [Algebra R' S]
    [SMulCommClass R R' S] :
    Module R' (Ω[S⁄R]) :=
  Submodule.Quotient.module' _
instance : IsScalarTower S (S ⊗[R] S) (Ω[S⁄R]) :=
  Ideal.Cotangent.isScalarTower _
instance KaehlerDifferential.isScalarTower_of_tower {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ S] [Algebra R₂ S] [SMul R₁ R₂]
    [SMulCommClass R R₁ S] [SMulCommClass R R₂ S] [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ (Ω[S⁄R]) :=
  Submodule.Quotient.isScalarTower _ _
instance KaehlerDifferential.isScalarTower' : IsScalarTower R (S ⊗[R] S) (Ω[S⁄R]) :=
  Submodule.Quotient.isScalarTower _ _
def KaehlerDifferential.fromIdeal : KaehlerDifferential.ideal R S →ₗ[S ⊗[R] S] Ω[S⁄R] :=
  (KaehlerDifferential.ideal R S).toCotangent
def KaehlerDifferential.DLinearMap : S →ₗ[R] Ω[S⁄R] :=
  ((KaehlerDifferential.fromIdeal R S).restrictScalars R).comp
    ((TensorProduct.includeRight.toLinearMap - TensorProduct.includeLeft.toLinearMap :
            S →ₗ[R] S ⊗[R] S).codRestrict
        ((KaehlerDifferential.ideal R S).restrictScalars R)
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R) :
      _ →ₗ[R] _)
theorem KaehlerDifferential.DLinearMap_apply (s : S) :
    KaehlerDifferential.DLinearMap R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ := rfl
def KaehlerDifferential.D : Derivation R S (Ω[S⁄R]) :=
  { toLinearMap := KaehlerDifferential.DLinearMap R S
    map_one_eq_zero' := by
      dsimp [KaehlerDifferential.DLinearMap_apply, Ideal.toCotangent_apply]
      congr
      rw [sub_self]
    leibniz' := fun a b => by
      have : LinearMap.CompatibleSMul { x // x ∈ ideal R S } (Ω[S⁄R]) S (S ⊗[R] S) := inferInstance
      dsimp [KaehlerDifferential.DLinearMap_apply]
      erw [← LinearMap.map_smul_of_tower (M₂ := Ω[S⁄R]),
        ← LinearMap.map_smul_of_tower (M₂ := Ω[S⁄R]), ← map_add, Ideal.toCotangent_eq, pow_two]
      convert Submodule.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a : _)
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b : _) using 1
      simp only [AddSubgroupClass.coe_sub, Submodule.coe_add, Submodule.coe_mk,
        TensorProduct.tmul_mul_tmul, mul_sub, sub_mul, mul_comm b, Submodule.coe_smul_of_tower,
        smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      ring_nf }
theorem KaehlerDifferential.D_apply (s : S) :
    KaehlerDifferential.D R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ := rfl
theorem KaehlerDifferential.span_range_derivation :
    Submodule.span S (Set.range <| KaehlerDifferential.D R S) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  have : x ∈ (KaehlerDifferential.ideal R S).restrictScalars S := hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal] at this
  suffices ∃ hx, (KaehlerDifferential.ideal R S).toCotangent ⟨x, hx⟩ ∈
      Submodule.span S (Set.range <| KaehlerDifferential.D R S) by
    exact this.choose_spec
  refine Submodule.span_induction ?_ ?_ ?_ ?_ this
  · rintro _ ⟨x, rfl⟩
    refine ⟨KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x, ?_⟩
    apply Submodule.subset_span
    exact ⟨x, KaehlerDifferential.DLinearMap_apply R S x⟩
  · exact ⟨zero_mem _, Submodule.zero_mem _⟩
  · rintro x y - - ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩; exact ⟨add_mem hx₁ hy₁, Submodule.add_mem _ hx₂ hy₂⟩
  · rintro r x - ⟨hx₁, hx₂⟩
    exact ⟨((KaehlerDifferential.ideal R S).restrictScalars S).smul_mem r hx₁,
      Submodule.smul_mem _ r hx₂⟩
lemma KaehlerDifferential.subsingleton_of_surjective (h : Function.Surjective (algebraMap R S)) :
    Subsingleton (Ω[S⁄R]) := by
  suffices (⊤ : Submodule S (Ω[S⁄R])) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun y ↦ this trivial
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩; obtain ⟨x, rfl⟩ := h x; simp
variable {R S}
def Derivation.liftKaehlerDifferential (D : Derivation R S M) : Ω[S⁄R] →ₗ[S] M := by
  refine LinearMap.comp ((((KaehlerDifferential.ideal R S) •
    (⊤ : Submodule (S ⊗[R] S) (KaehlerDifferential.ideal R S))).restrictScalars S).liftQ ?_ ?_)
    (Submodule.Quotient.restrictScalarsEquiv S _).symm.toLinearMap
  · exact D.tensorProductTo.comp ((KaehlerDifferential.ideal R S).subtype.restrictScalars S)
  · intro x hx
    rw [LinearMap.mem_ker]
    refine Submodule.smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ ?_
    · rintro x hx y -
      rw [RingHom.mem_ker] at hx
      dsimp
      rw [Derivation.tensorProductTo_mul, hx, y.prop, zero_smul, zero_smul, zero_add]
    · intro x y ex ey; rw [map_add, ex, ey, zero_add]
theorem Derivation.liftKaehlerDifferential_apply (D : Derivation R S M) (x) :
    D.liftKaehlerDifferential ((KaehlerDifferential.ideal R S).toCotangent x) =
      D.tensorProductTo x := rfl
theorem Derivation.liftKaehlerDifferential_comp (D : Derivation R S M) :
    D.liftKaehlerDifferential.compDer (KaehlerDifferential.D R S) = D := by
  ext a
  dsimp [KaehlerDifferential.D_apply]
  refine (D.liftKaehlerDifferential_apply _).trans ?_
  rw [Subtype.coe_mk, map_sub, Derivation.tensorProductTo_tmul, Derivation.tensorProductTo_tmul,
    one_smul, D.map_one_eq_zero, smul_zero, sub_zero]
@[simp]
theorem Derivation.liftKaehlerDifferential_comp_D (D' : Derivation R S M) (x : S) :
    D'.liftKaehlerDifferential (KaehlerDifferential.D R S x) = D' x :=
  Derivation.congr_fun D'.liftKaehlerDifferential_comp x
@[ext]
theorem Derivation.liftKaehlerDifferential_unique (f f' : Ω[S⁄R] →ₗ[S] M)
    (hf : f.compDer (KaehlerDifferential.D R S) = f'.compDer (KaehlerDifferential.D R S)) :
    f = f' := by
  apply LinearMap.ext
  intro x
  have : x ∈ Submodule.span S (Set.range <| KaehlerDifferential.D R S) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ this
  · rintro _ ⟨x, rfl⟩; exact congr_arg (fun D : Derivation R S M => D x) hf
  · rw [map_zero, map_zero]
  · intro x y _ _ hx hy; rw [map_add, map_add, hx, hy]
  · intro a x _ e; simp [e]
variable (R S)
theorem Derivation.liftKaehlerDifferential_D :
    (KaehlerDifferential.D R S).liftKaehlerDifferential = LinearMap.id :=
  Derivation.liftKaehlerDifferential_unique _ _
    (KaehlerDifferential.D R S).liftKaehlerDifferential_comp
variable {R S}
theorem KaehlerDifferential.D_tensorProductTo (x : KaehlerDifferential.ideal R S) :
    (KaehlerDifferential.D R S).tensorProductTo x =
      (KaehlerDifferential.ideal R S).toCotangent x := by
  rw [← Derivation.liftKaehlerDifferential_apply, Derivation.liftKaehlerDifferential_D]
  rfl
variable (R S)
theorem KaehlerDifferential.tensorProductTo_surjective :
    Function.Surjective (KaehlerDifferential.D R S).tensorProductTo := by
  intro x; obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R S).toCotangent_surjective x
  exact ⟨x, KaehlerDifferential.D_tensorProductTo x⟩
@[simps! symm_apply apply_apply]
def KaehlerDifferential.linearMapEquivDerivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  { Derivation.llcomp.flip <| KaehlerDifferential.D R S with
    invFun := Derivation.liftKaehlerDifferential
    left_inv := fun _ =>
      Derivation.liftKaehlerDifferential_unique _ _ (Derivation.liftKaehlerDifferential_comp _)
    right_inv := Derivation.liftKaehlerDifferential_comp }
def KaehlerDifferential.quotientCotangentIdealRingEquiv :
    (S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸ (KaehlerDifferential.ideal R S).cotangentIdeal ≃+*
      S := by
  have : Function.RightInverse (TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
      (↑(TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) : S ⊗[R] S →+* S) := by
    intro x; rw [AlgHom.coe_toRingHom, ← AlgHom.comp_apply, TensorProduct.lmul'_comp_includeLeft]
    rfl
  refine (Ideal.quotCotangent _).trans ?_
  refine (Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfRightInverse this)
  ext; rfl
def KaehlerDifferential.quotientCotangentIdeal :
    ((S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸
        (KaehlerDifferential.ideal R S).cotangentIdeal) ≃ₐ[S] S :=
  { KaehlerDifferential.quotientCotangentIdealRingEquiv R S with
    commutes' := (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).apply_symm_apply }
theorem KaehlerDifferential.End_equiv_aux (f : S →ₐ[R] S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) :
    (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f =
        IsScalarTower.toAlgHom R S _ ↔
      (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S := by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  apply forall_congr'
  intro x
  have e₁ : (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift (f x) =
      KaehlerDifferential.quotientCotangentIdealRingEquiv R S
        (Ideal.Quotient.mk (KaehlerDifferential.ideal R S).cotangentIdeal <| f x) := by
    generalize f x = y; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y; rfl
  have e₂ :
    x = KaehlerDifferential.quotientCotangentIdealRingEquiv R S (IsScalarTower.toAlgHom R S _ x) :=
    (mul_one x).symm
  constructor
  · intro e
    exact (e₁.trans (@RingEquiv.congr_arg _ _ _ _ _ _
      (KaehlerDifferential.quotientCotangentIdealRingEquiv R S) _ _ e)).trans e₂.symm
  · intro e; apply (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).injective
    exact e₁.symm.trans (e.trans e₂)
local instance smul_SSmod_SSmod : SMul (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
    (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Mul.toSMul _
@[nolint defLemma]
local instance isScalarTower_S_right :
    IsScalarTower S (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
      (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Ideal.Quotient.isScalarTower_right
@[nolint defLemma]
local instance isScalarTower_R_right :
    IsScalarTower R (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
      (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Ideal.Quotient.isScalarTower_right
@[nolint defLemma]
local instance isScalarTower_SS_right : IsScalarTower (S ⊗[R] S)
    (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) :=
  Ideal.Quotient.isScalarTower_right
local instance instS : Module S (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _
local instance instR : Module R (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _
local instance instSS : Module (S ⊗[R] S) (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _
noncomputable def KaehlerDifferential.endEquivDerivation' :
    Derivation R S (Ω[S⁄R]) ≃ₗ[R] Derivation R S (ideal R S).cotangentIdeal :=
  LinearEquiv.compDer ((KaehlerDifferential.ideal R S).cotangentEquivIdeal.restrictScalars S)
def KaehlerDifferential.endEquivAuxEquiv :
    { f //
        (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f =
          IsScalarTower.toAlgHom R S _ } ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (Equiv.refl _).subtypeEquiv (KaehlerDifferential.End_equiv_aux R S)
noncomputable def KaehlerDifferential.endEquiv :
    Module.End S (Ω[S⁄R]) ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans <|
    (KaehlerDifferential.endEquivDerivation' R S).toEquiv.trans <|
      (derivationToSquareZeroEquivLift (KaehlerDifferential.ideal R S).cotangentIdeal
            (KaehlerDifferential.ideal R S).cotangentIdeal_square).trans <|
        KaehlerDifferential.endEquivAuxEquiv R S
section Finiteness
theorem KaehlerDifferential.ideal_fg [EssFiniteType R S] :
    (KaehlerDifferential.ideal R S).FG := by
  classical
  use (EssFiniteType.finset R S).image (fun s ↦ (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S))
  apply le_antisymm
  · rw [Finset.coe_image, Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x
  · rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    let I : Ideal (S ⊗[R] S) := Ideal.span
      ((EssFiniteType.finset R S).image (fun s ↦ (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)))
    show _ - _ ∈ I
    have : (IsScalarTower.toAlgHom R (S ⊗[R] S) (S ⊗[R] S ⧸ I)).comp TensorProduct.includeRight =
        (IsScalarTower.toAlgHom R (S ⊗[R] S) (S ⊗[R] S ⧸ I)).comp TensorProduct.includeLeft := by
      apply EssFiniteType.algHom_ext
      intro a ha
      simp only [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq,
        Function.comp_apply, TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      refine Ideal.subset_span ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨a, ha, rfl⟩
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun this x
instance KaehlerDifferential.finite [EssFiniteType R S] :
    Module.Finite S (Ω[S⁄R]) := by
  classical
  let s := (EssFiniteType.finset R S).image (fun s ↦ D R S s)
  refine ⟨⟨s, top_le_iff.mp ?_⟩⟩
  rw [← span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have : ∀ x ∈ adjoin R (EssFiniteType.finset R S).toSet,
      .D _ _ x ∈ Submodule.span S s.toSet := by
    intro x hx
    refine adjoin_induction ?_ ?_ ?_ ?_ hx
    · exact fun x hx ↦ Submodule.subset_span (Finset.mem_image_of_mem _ hx)
    · simp
    · exact fun x y _ _ hx hy ↦ (D R S).map_add x y ▸ add_mem hx hy
    · intro x y _ _ hx hy
      simp only [Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  obtain ⟨t, ht, ht', hxt⟩ := (essFiniteType_cond_iff R S (EssFiniteType.finset R S)).mp
    EssFiniteType.cond.choose_spec x
  rw [show D R S x =
    ht'.unit⁻¹ • (D R S (x * t) - x • D R S t) by simp [smul_smul, Units.smul_def]]
  exact Submodule.smul_mem _ _ (sub_mem (this _ hxt) (Submodule.smul_mem _ _ (this _ ht)))
end Finiteness
section Presentation
open KaehlerDifferential (D)
open Finsupp (single)
noncomputable def KaehlerDifferential.kerTotal : Submodule S (S →₀ S) :=
  Submodule.span S
    (((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : R => single (algebraMap R S x) 1)
unsuppress_compilation in
local notation3 x "𝖣" y => DFunLike.coe (KaehlerDifferential.kerTotal R S).mkQ (single y x)
theorem KaehlerDifferential.kerTotal_mkQ_single_add (x y z) : (z𝖣x + y) = (z𝖣x) + z𝖣y := by
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub (Submodule.mkQ (kerTotal R S)),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp_rw [← Finsupp.smul_single_one _ z, ← smul_add, ← smul_sub]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl <| Or.inl <| ⟨⟨_, _⟩, rfl⟩))
theorem KaehlerDifferential.kerTotal_mkQ_single_mul (x y z) :
    (z𝖣x * y) = ((z * x)𝖣y) + (z * y)𝖣x := by
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub (Submodule.mkQ (kerTotal R S)),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp_rw [← Finsupp.smul_single_one _ z, ← @smul_eq_mul _ _ z, ← Finsupp.smul_single, ← smul_add,
    ← smul_sub]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl <| Or.inr <| ⟨⟨_, _⟩, rfl⟩))
theorem KaehlerDifferential.kerTotal_mkQ_single_algebraMap (x y) : (y𝖣algebraMap R S x) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Finsupp.smul_single_one _ y]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr <| ⟨_, rfl⟩))
theorem KaehlerDifferential.kerTotal_mkQ_single_algebraMap_one (x) : (x𝖣1) = 0 := by
  rw [← (algebraMap R S).map_one, KaehlerDifferential.kerTotal_mkQ_single_algebraMap]
theorem KaehlerDifferential.kerTotal_mkQ_single_smul (r : R) (x y) : (y𝖣r • x) = r • y𝖣x := by
  letI : SMulZeroClass R S := inferInstance
  rw [Algebra.smul_def, KaehlerDifferential.kerTotal_mkQ_single_mul,
    KaehlerDifferential.kerTotal_mkQ_single_algebraMap, add_zero, ← LinearMap.map_smul_of_tower,
    Finsupp.smul_single, mul_comm, Algebra.smul_def]
noncomputable def KaehlerDifferential.derivationQuotKerTotal :
    Derivation R S ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) where
  toFun x := 1𝖣x
  map_add' _ _ := KaehlerDifferential.kerTotal_mkQ_single_add _ _ _ _ _
  map_smul' _ _ := KaehlerDifferential.kerTotal_mkQ_single_smul _ _ _ _ _
  map_one_eq_zero' := KaehlerDifferential.kerTotal_mkQ_single_algebraMap_one _ _ _
  leibniz' a b :=
    (KaehlerDifferential.kerTotal_mkQ_single_mul _ _ _ _ _).trans
      (by simp_rw [← Finsupp.smul_single_one _ (1 * _ : S)]; dsimp; simp)
theorem KaehlerDifferential.derivationQuotKerTotal_apply (x) :
    KaehlerDifferential.derivationQuotKerTotal R S x = 1𝖣x :=
  rfl
theorem KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination :
    (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential.comp
        (Finsupp.linearCombination S (KaehlerDifferential.D R S)) =
      Submodule.mkQ _ := by
  apply Finsupp.lhom_ext
  intro a b
  conv_rhs => rw [← Finsupp.smul_single_one a b, LinearMap.map_smul]
  simp [KaehlerDifferential.derivationQuotKerTotal_apply]
@[deprecated (since := "2024-08-29")] alias
  KaehlerDifferential.derivationQuotKerTotal_lift_comp_total :=
  KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination
theorem KaehlerDifferential.kerTotal_eq :
    LinearMap.ker (Finsupp.linearCombination S (KaehlerDifferential.D R S)) =
      KaehlerDifferential.kerTotal R S := by
  apply le_antisymm
  · conv_rhs => rw [← (KaehlerDifferential.kerTotal R S).ker_mkQ]
    rw [← KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination]
    exact LinearMap.ker_le_ker_comp _ _
  · rw [KaehlerDifferential.kerTotal, Submodule.span_le]
    rintro _ ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨x, rfl⟩) <;> dsimp <;> simp [LinearMap.mem_ker]
theorem KaehlerDifferential.linearCombination_surjective :
    Function.Surjective (Finsupp.linearCombination S (KaehlerDifferential.D R S)) := by
  rw [← LinearMap.range_eq_top, range_linearCombination, span_range_derivation]
@[deprecated (since := "2024-08-29")] alias KaehlerDifferential.total_surjective :=
  KaehlerDifferential.linearCombination_surjective
@[simps!]
noncomputable def KaehlerDifferential.quotKerTotalEquiv :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) ≃ₗ[S] Ω[S⁄R] :=
  { (KaehlerDifferential.kerTotal R S).liftQ
      (Finsupp.linearCombination S (KaehlerDifferential.D R S))
      (KaehlerDifferential.kerTotal_eq R S).ge with
    invFun := (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential
    left_inv := by
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      exact
        LinearMap.congr_fun
          (KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination R S : _) x
    right_inv := by
      intro x
      obtain ⟨x, rfl⟩ := KaehlerDifferential.linearCombination_surjective R S x
      have := LinearMap.congr_fun
        (KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination R S) x
      rw [LinearMap.comp_apply] at this
      rw [this]
      rfl }
theorem KaehlerDifferential.quotKerTotalEquiv_symm_comp_D :
    (KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.compDer
        (KaehlerDifferential.D R S) =
      KaehlerDifferential.derivationQuotKerTotal R S := by
  convert (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential_comp
end Presentation
section ExactSequence
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra R A]
variable [Algebra A B] [Algebra S B]
unsuppress_compilation in
local macro "finsupp_map" : term =>
  `((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
    (Finsupp.lmapDomain A A (algebraMap A B)))
theorem KaehlerDifferential.kerTotal_map [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    (h : Function.Surjective (algebraMap A B)) :
    (KaehlerDifferential.kerTotal R A).map finsupp_map ⊔
        Submodule.span A (Set.range fun x : S => .single (algebraMap S B x) (1 : B)) =
      (KaehlerDifferential.kerTotal S B).restrictScalars _ := by
  rw [KaehlerDifferential.kerTotal, Submodule.map_span, KaehlerDifferential.kerTotal,
    Submodule.restrictScalars_span _ _ h]
  simp_rw [Set.image_union, Submodule.span_union, ← Set.image_univ, Set.image_image, Set.image_univ,
    map_sub, map_add]
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
    map_one, map_add, map_mul]
  simp_rw [sup_assoc, ← (h.prodMap h).range_comp]
  congr!
  simp_rw [← IsScalarTower.algebraMap_apply R A B]
  rw [sup_eq_right]
  apply Submodule.span_mono
  simp_rw [IsScalarTower.algebraMap_apply R S B]
  exact Set.range_comp_subset_range (algebraMap R S)
    fun x => Finsupp.single (algebraMap S B x) (1 : B)
theorem KaehlerDifferential.kerTotal_map' [Algebra R B]
    [IsScalarTower R A B] (h : Function.Surjective (algebraMap A B)) :
    (KaehlerDifferential.kerTotal R A ⊔
      Submodule.span A (Set.range fun x ↦ .single (algebraMap R A x) 1)).map finsupp_map =
      (KaehlerDifferential.kerTotal R B).restrictScalars _ := by
  rw [Submodule.map_sup, ← kerTotal_map R R A B h, Submodule.map_span, ← Set.range_comp]
  congr
  refine congr_arg Set.range ?_
  ext; simp [IsScalarTower.algebraMap_eq R A B]
section
variable [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
def KaehlerDifferential.map : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
  Derivation.liftKaehlerDifferential
    (((KaehlerDifferential.D S B).restrictScalars R).compAlgebraMap A)
theorem KaehlerDifferential.map_compDer :
    (KaehlerDifferential.map R S A B).compDer (KaehlerDifferential.D R A) =
      ((KaehlerDifferential.D S B).restrictScalars R).compAlgebraMap A :=
  Derivation.liftKaehlerDifferential_comp _
@[simp]
theorem KaehlerDifferential.map_D (x : A) :
    KaehlerDifferential.map R S A B (KaehlerDifferential.D R A x) =
      KaehlerDifferential.D S B (algebraMap A B x) :=
  Derivation.congr_fun (KaehlerDifferential.map_compDer R S A B) x
theorem KaehlerDifferential.ker_map :
    LinearMap.ker (KaehlerDifferential.map R S A B) =
      (((kerTotal S B).restrictScalars A).comap finsupp_map).map
        (Finsupp.linearCombination (M := Ω[A⁄R]) A (D R A)) := by
  rw [← Submodule.map_comap_eq_of_surjective (linearCombination_surjective R A) (LinearMap.ker _)]
  congr 1
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_ker, Finsupp.apply_linearCombination, ← kerTotal_eq,
    Submodule.restrictScalars_mem]
  simp only [linearCombination_apply, Function.comp_apply, LinearMap.coe_comp, lmapDomain_apply,
    Finsupp.mapRange.linearMap_apply]
  rw [Finsupp.sum_mapRange_index, Finsupp.sum_mapDomain_index]
  · simp [ofId]
  · simp
  · simp [add_smul]
  · simp
lemma KaehlerDifferential.ker_map_of_surjective (h : Function.Surjective (algebraMap A B)) :
    LinearMap.ker (map R R A B) =
      (LinearMap.ker finsupp_map).map (Finsupp.linearCombination A (D R A)) := by
  rw [ker_map, ← kerTotal_map' R A B h, Submodule.comap_map_eq, Submodule.map_sup,
    Submodule.map_sup, ← kerTotal_eq, ← Submodule.comap_bot,
    Submodule.map_comap_eq_of_surjective (linearCombination_surjective _ _),
    bot_sup_eq, Submodule.map_span, ← Set.range_comp]
  convert bot_sup_eq _
  rw [Submodule.span_eq_bot]; simp
open IsScalarTower (toAlgHom)
theorem KaehlerDifferential.map_surjective_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.map R S A B) := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff,
    ← @Submodule.restrictScalars_top A B, ← span_range_derivation,
    Submodule.restrictScalars_span _ _ h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := h x
  rw [← KaehlerDifferential.map_D R S A B]
  exact ⟨_, rfl⟩
theorem KaehlerDifferential.map_surjective :
    Function.Surjective (KaehlerDifferential.map R S B B) :=
  map_surjective_of_surjective R S B B Function.surjective_id
noncomputable def KaehlerDifferential.mapBaseChange : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R] :=
  (TensorProduct.isBaseChange A (Ω[A⁄R]) B).lift (KaehlerDifferential.map R R A B)
@[simp]
theorem KaehlerDifferential.mapBaseChange_tmul (x : B) (y : Ω[A⁄R]) :
    KaehlerDifferential.mapBaseChange R A B (x ⊗ₜ y) = x • KaehlerDifferential.map R R A B y := by
  conv_lhs => rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul', LinearMap.map_smul]
  congr 1
  exact IsBaseChange.lift_eq _ _ _
lemma KaehlerDifferential.range_mapBaseChange :
    LinearMap.range (mapBaseChange R A B) = LinearMap.ker (map R A B B) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction' x with r s
    · simp
    · obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ s
      simp only [mapBaseChange_tmul, LinearMap.mem_ker, map_smul]
      induction x using Finsupp.induction_linear
      · simp
      · simp [smul_add, *]
      · simp
    · rw [map_add]; exact add_mem ‹_› ‹_›
  · convert_to (kerTotal A B).map (Finsupp.linearCombination B (D R B)) ≤ _
    · rw [KaehlerDifferential.ker_map]
      congr 1
      convert Submodule.comap_id _
      · ext; simp
    rw [Submodule.map_le_iff_le_comap, kerTotal, Submodule.span_le]
    rintro f ((⟨⟨x, y⟩, rfl⟩|⟨⟨x, y⟩, rfl⟩)|⟨x, rfl⟩)
    · use 0; simp
    · use 0; simp
    · use 1 ⊗ₜ D _ _ x; simp
lemma KaehlerDifferential.exact_mapBaseChange_map :
    Function.Exact (mapBaseChange R A B) (map R A B B) :=
  SetLike.ext_iff.mp (range_mapBaseChange R A B).symm
end
@[simps]
noncomputable
def KaehlerDifferential.kerToTensor :
    RingHom.ker (algebraMap A B) →ₗ[A] B ⊗[A] Ω[A⁄R] where
  toFun x := 1 ⊗ₜ D R A x
  map_add' x y := by simp only [Submodule.coe_add, map_add, TensorProduct.tmul_add]
  map_smul' r x := by simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ←
    algebraMap_eq_smul_one, RingHom.mem_ker.mp x.prop, TensorProduct.zero_tmul, add_zero,
    RingHom.id_apply]
noncomputable
def KaehlerDifferential.kerCotangentToTensor :
    (RingHom.ker (algebraMap A B)).Cotangent →ₗ[A] B ⊗[A] Ω[A⁄R] :=
  Submodule.liftQ _ (kerToTensor R A B) <| by
    rw [Submodule.smul_eq_map₂]
    apply iSup_le_iff.mpr
    simp only [Submodule.map_le_iff_le_comap, Subtype.forall]
    rintro x hx y -
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, LinearMap.mem_ker, map_smul,
      kerToTensor_apply, TensorProduct.smul_tmul', ← algebraMap_eq_smul_one,
      RingHom.mem_ker.mp hx, TensorProduct.zero_tmul]
@[simp]
lemma KaehlerDifferential.kerCotangentToTensor_toCotangent (x) :
    kerCotangentToTensor R A B (Ideal.toCotangent _ x) = 1 ⊗ₜ D _ _ x.1 := rfl
variable [Algebra R B] [IsScalarTower R A B]
theorem KaehlerDifferential.range_kerCotangentToTensor
    (h : Function.Surjective (algebraMap A B)) :
    LinearMap.range (kerCotangentToTensor R A B) =
      (LinearMap.ker (KaehlerDifferential.mapBaseChange R A B)).restrictScalars A := by
  classical
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    simp [kerCotangentToTensor_toCotangent, RingHom.mem_ker.mp x.2]
  · intro hx
    obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective (Ω[A⁄R]) (g := Algebra.linearMap A B) h x
    obtain ⟨x, rfl⟩ := (TensorProduct.lid _ _).symm.surjective x
    replace hx : x ∈ LinearMap.ker (KaehlerDifferential.map R R A B) := by simpa using hx
    rw [KaehlerDifferential.ker_map_of_surjective R A B h] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      Algebra.linearMap_apply, map_one]
    rw [← Finsupp.sum_single x, Finsupp.sum, ← Finset.sum_fiberwise_of_maps_to
      (fun _ ↦ Finset.mem_image_of_mem (algebraMap A B))]
    simp only [Function.comp_apply, map_sum (s := x.support.image (algebraMap A B)),
      TensorProduct.tmul_sum]
    apply sum_mem
    intro c _
    simp only [Finset.filter_congr_decidable, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one, LinearMap.mem_range]
    simp only [map_sum, Finsupp.linearCombination_single]
    have : (x.support.filter (algebraMap A B · = c)).sum x ∈ RingHom.ker (algebraMap A B) := by
      simpa [Finsupp.mapDomain, Finsupp.sum, Finsupp.finset_sum_apply, RingHom.mem_ker,
        Finsupp.single_apply, ← Finset.sum_filter] using DFunLike.congr_fun hx c
    obtain ⟨a, ha⟩ := h c
    use (x.support.filter (algebraMap A B · = c)).attach.sum
        fun i ↦ x i • Ideal.toCotangent _ ⟨i - a, ?_⟩; swap
    · have : x i ≠ 0 ∧ algebraMap A B i = c := by
        convert i.prop
        simp_rw [Finset.mem_filter, Finsupp.mem_support_iff]
      simp [RingHom.mem_ker, ha, this.2]
    · simp only [map_sum, LinearMapClass.map_smul, kerCotangentToTensor_toCotangent, map_sub]
      simp_rw [← TensorProduct.tmul_smul]
      simp only [smul_sub, TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.tmul_sum,
        ← Finset.sum_smul, Finset.sum_attach, sub_eq_self,
        Finset.sum_attach (f := fun i ↦ x i • KaehlerDifferential.D R A i)]
      rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp this,
        TensorProduct.zero_tmul]
theorem KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) :=
  SetLike.ext_iff.mp (range_kerCotangentToTensor R A B h).symm
lemma KaehlerDifferential.mapBaseChange_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
  have := subsingleton_of_surjective A B h
  rw [← LinearMap.range_eq_top, range_mapBaseChange, ← top_le_iff]
  exact fun x _ ↦ Subsingleton.elim _ _
end ExactSequence
end KaehlerDifferential