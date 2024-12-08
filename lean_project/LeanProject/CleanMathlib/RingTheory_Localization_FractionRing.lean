import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.SimpleRing.Basic
assert_not_exists Ideal
variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]
variable {A : Type*} [CommRing A] (K : Type*)
abbrev IsFractionRing [CommRing K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K
instance {R : Type*} [Field R] : IsFractionRing R R :=
  IsLocalization.at_units _ (fun _ ↦ isUnit_of_mem_nonZeroDivisors)
instance Rat.isFractionRing : IsFractionRing ℤ ℚ where
  map_units' := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj' := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero, Int.natCast_ne_zero_iff_pos]
    exact Nat.zero_lt_of_ne_zero hd
  exists_of_eq {x y} := by
    rw [eq_intCast, eq_intCast, Int.cast_inj]
    rintro rfl
    use 1
namespace IsFractionRing
open IsLocalization
variable {R K}
section CommRing
variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]
theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl
variable (R K)
protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)
variable {R K}
@[norm_cast, simp]
theorem coe_inj {a b : R} : (Algebra.cast a : K) = Algebra.cast b ↔ a = b :=
  (IsFractionRing.injective R K).eq_iff
instance (priority := 100) [NoZeroDivisors K] : NoZeroSMulDivisors R K :=
  NoZeroSMulDivisors.of_algebraMap_injective <| IsFractionRing.injective R K
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] {x : R}
    (hx : x ∈ nonZeroDivisors R) : algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx
variable (A) [IsDomain A]
include A in
protected theorem isDomain : IsDomain K :=
  isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))
protected noncomputable irreducible_def inv (z : K) : K := open scoped Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
          h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩
protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 := by
  rw [IsFractionRing.inv, dif_neg hx, ←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1,
          mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
            hx <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
    one_mul, mul_assoc]
  rw [mk'_spec, ← eq_mk'_iff_mul_eq]
  exact (mk'_sec _ x).symm
@[stacks 09FJ]
noncomputable abbrev toField : Field K where
  __ := IsFractionRing.isDomain A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
lemma surjective_iff_isField [IsDomain R] : Function.Surjective (algebraMap R K) ↔ IsField R where
  mp h := (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField _ (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx ↦ Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective
end CommRing
variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A →+* L}
theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) :
    mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  haveI := (algebraMap A K).domain_nontrivial
  mk'_eq_iff_eq_mul.2 <|
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm
@[simp]
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2
theorem div_surjective (z : K) :
    ∃ x y : A, y ∈ nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩
theorem isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) :
    IsUnit (g y) :=
  haveI := g.domain_nontrivial
  IsUnit.mk0 (g y) <|
    show g.toMonoidWithZeroHom y ≠ 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2
theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  haveI := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]
theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  haveI := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y ≠ (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div, div_eq_one_iff_eq hy] at hxy
  exact IsFractionRing.injective A K hxy
section Subfield
variable (A K) in
theorem closure_range_algebraMap : Subfield.closure (Set.range (algebraMap A K)) = ⊤ :=
  top_unique fun z _ ↦ by
    obtain ⟨_, _, -, rfl⟩ := div_surjective (A := A) z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩
variable {L : Type*} [Field L] {g : A →+* L} {f : K →+* L}
theorem ringHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = g) :
    f.fieldRange = Subfield.closure g.range := by
  rw [f.fieldRange_eq_map, ← closure_range_algebraMap A K,
    f.map_field_closure, ← Set.range_comp, ← f.coe_comp, h, g.coe_range]
theorem ringHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g)
    {s : Set L} (hs : g.range = Subring.closure s) : f.fieldRange = Subfield.closure s := by
  rw [ringHom_fieldRange_eq_of_comp_eq h, hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]
end Subfield
open Function
noncomputable def lift (hg : Injective g) : K →+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
section liftAlgHom
variable [Algebra R A] [Algebra R K] [IsScalarTower R A K] [Algebra R L]
  {g : A →ₐ[R] L} (hg : Injective g) (x : K)
include hg
noncomputable def liftAlgHom : K →ₐ[R] L :=
  IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
theorem liftAlgHom_toRingHom : (liftAlgHom hg : K →ₐ[R] L).toRingHom = lift hg := rfl
@[simp]
theorem coe_liftAlgHom : ⇑(liftAlgHom hg : K →ₐ[R] L) = lift hg := rfl
theorem liftAlgHom_apply : liftAlgHom hg x = lift hg x := rfl
end liftAlgHom
@[simp]
theorem lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _
theorem lift_fieldRange (hg : Injective g) :
    (lift hg : K →+* L).fieldRange = Subfield.closure g.range :=
  ringHom_fieldRange_eq_of_comp_eq (by ext; simp)
theorem lift_fieldRange_eq_of_range_eq (hg : Injective g)
    {s : Set L} (hs : g.range = Subring.closure s) :
    (lift hg : K →+* L).fieldRange = Subfield.closure s :=
  ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) :
    lift hg (mk' K x y) = g x / g y := by simp only [mk'_eq_div, map_div₀, lift_algebraMap]
noncomputable def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}
    (hj : Injective j) : K →+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
section ringEquivOfRingEquiv
variable {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  (h : A ≃+* B)
noncomputable def ringEquivOfRingEquiv : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)
@[deprecated (since := "2024-11-05")]
alias fieldEquivOfRingEquiv := ringEquivOfRingEquiv
@[simp]
lemma ringEquivOfRingEquiv_algebraMap
    (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp [ringEquivOfRingEquiv]
@[deprecated (since := "2024-11-05")]
alias fieldEquivOfRingEquiv_algebraMap := ringEquivOfRingEquiv_algebraMap
@[simp]
lemma ringEquivOfRingEquiv_symm :
    (ringEquivOfRingEquiv h : K ≃+* L).symm = ringEquivOfRingEquiv h.symm := rfl
end ringEquivOfRingEquiv
section algEquivOfAlgEquiv
variable {R A K B L : Type*} [CommSemiring R] [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra R A] [Algebra R K] [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (h : A ≃ₐ[R] B)
noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=
  IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)
@[simp]
lemma algEquivOfAlgEquiv_algebraMap
    (a : A) : algEquivOfAlgEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp [algEquivOfAlgEquiv]
@[simp]
lemma algEquivOfAlgEquiv_symm :
    (algEquivOfAlgEquiv h : K ≃ₐ[R] L).symm = algEquivOfAlgEquiv h.symm := rfl
end algEquivOfAlgEquiv
section fieldEquivOfAlgEquiv
variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  (FA FB FC FD : Type*) [Field FA] [Field FB] [Field FC] [Field FD]
  [Algebra A FA] [Algebra B FB] [Algebra C FC] [Algebra D FD]
  [IsFractionRing A FA] [IsFractionRing B FB] [IsFractionRing C FC] [IsFractionRing D FD]
  [Algebra A FB] [IsScalarTower A B FB]
  [Algebra A FC] [IsScalarTower A C FC]
  [Algebra A FD] [IsScalarTower A D FD]
  [Algebra FA FB] [IsScalarTower A FA FB]
  [Algebra FA FC] [IsScalarTower A FA FC]
  [Algebra FA FD] [IsScalarTower A FA FD]
noncomputable def fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : FB ≃ₐ[FA] FC where
  __ := IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]
lemma restrictScalars_fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) :
    (fieldEquivOfAlgEquiv FA FB FC f).restrictScalars A = algEquivOfAlgEquiv f := by
  ext; rfl
@[simp]
lemma fieldEquivOfAlgEquiv_algebraMap (f : B ≃ₐ[A] C) (b : B) :
    fieldEquivOfAlgEquiv FA FB FC f (algebraMap B FB b) = algebraMap C FC (f b) :=
  ringEquivOfRingEquiv_algebraMap f.toRingEquiv b
variable (A B) in
@[simp]
lemma fieldEquivOfAlgEquiv_refl :
    fieldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl : B ≃ₐ[A] B) = AlgEquiv.refl := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  simp
lemma fieldEquivOfAlgEquiv_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) :
    fieldEquivOfAlgEquiv FA FB FD (f.trans g) =
      (fieldEquivOfAlgEquiv FA FB FC f).trans (fieldEquivOfAlgEquiv FA FC FD g) := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  simp
end fieldEquivOfAlgEquiv
section fieldEquivOfAlgEquivHom
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]
noncomputable def fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L) where
  toFun := fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f
@[simp]
lemma fieldEquivOfAlgEquivHom_apply (f : B ≃ₐ[A] B) :
    fieldEquivOfAlgEquivHom K L f = fieldEquivOfAlgEquiv K L L f :=
  rfl
variable (A B)
lemma fieldEquivOfAlgEquivHom_injective :
    Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L)) := by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)
end fieldEquivOfAlgEquivHom
theorem isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsFractionRing R S ↔
      @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta IsFractionRing
  convert isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  ext x
  erw [Submonoid.map_equiv_eq_comap_symm]
  simp only [MulEquiv.coe_toMonoidHom, RingEquiv.toMulEquiv_eq_coe, Submonoid.mem_comap]
  constructor
  · rintro hx z (hz : z * h.symm x = 0)
    rw [← h.map_eq_zero_iff]
    apply hx
    simpa only [h.map_zero, h.apply_symm_apply, h.map_mul] using congr_arg h hz
  · rintro (hx : h.symm x ∈ _) z hz
    rw [← h.symm.map_eq_zero_iff]
    apply hx
    rw [← h.symm.map_mul, hz, h.symm.map_zero]
protected theorem nontrivial (R S : Type*) [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    [IsFractionRing R S] : Nontrivial S := by
  apply nontrivial_of_ne
  · intro h
    apply @zero_ne_one R
    exact
      IsLocalization.injective S (le_of_eq rfl)
        (((algebraMap R S).map_zero.trans h).trans (algebraMap R S).map_one.symm)
end IsFractionRing
section algebraMap_injective
theorem algebraMap_injective_of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : Function.Injective (algebraMap R S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
theorem NoZeroSMulDivisors.of_field_isFractionRing [NoZeroDivisors S] (K L : Type*) [Field K]
    [Semiring L] [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] : NoZeroSMulDivisors R S :=
  of_algebraMap_injective (algebraMap_injective_of_field_isFractionRing R S K L)
end algebraMap_injective
variable (A)
abbrev FractionRing :=
  Localization (nonZeroDivisors R)
namespace FractionRing
instance unique [Subsingleton R] : Unique (FractionRing R) := inferInstance
instance [Nontrivial R] : Nontrivial (FractionRing R) := inferInstance
variable [IsDomain A]
noncomputable instance field : Field (FractionRing A) := inferInstance
@[simp]
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) =
      (algebraMap _ _ r / algebraMap A _ s : FractionRing A) := by
  rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]
noncomputable abbrev liftAlgebra [IsDomain R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Algebra (FractionRing R) K :=
  RingHom.toAlgebra (IsFractionRing.lift (NoZeroSMulDivisors.algebraMap_injective R _))
instance isScalarTower_liftAlgebra [IsDomain R] [Field K] [Algebra R K] [NoZeroSMulDivisors R K] :
    by letI := liftAlgebra R K; exact IsScalarTower R (FractionRing R) K := by
  letI := liftAlgebra R K
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (NoZeroSMulDivisors.algebraMap_injective R K) x).symm
noncomputable def algEquiv (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K
instance [Algebra R A] [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R (FractionRing A) := by
  apply NoZeroSMulDivisors.of_algebraMap_injective
  rw [IsScalarTower.algebraMap_eq R A]
  apply Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective A (FractionRing A))
    (NoZeroSMulDivisors.algebraMap_injective R A)
end FractionRing