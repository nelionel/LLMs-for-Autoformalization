import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.OreLocalization.Ring
assert_not_exists Ideal
open Function
section CommSemiring
variable {R : Type*} [CommSemiring R] {M N : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]
namespace IsLocalization
section IsLocalization
variable [IsLocalization M S]
variable (M S) in
include M in
theorem linearMap_compatibleSMul (N₁ N₂) [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁]
    [Module S N₁] [Module R N₂] [Module S N₂] [IsScalarTower R S N₁] [IsScalarTower R S N₂] :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul f s s' := by
    obtain ⟨r, m, rfl⟩ := mk'_surjective M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]
variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))
variable (M) in
include M in
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩
section AlgEquiv
variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]
section
variable (M S Q)
@[simps!]
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }
end
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y := by
  simp
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp
variable (M) in
include M in
protected lemma bijective (f : S →+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q) :
    Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective
end AlgEquiv
section liftAlgHom
variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R}
  {S : Type*} [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  {P : Type*} [CommSemiring P] [Algebra A P] [IsLocalization M S]
  {f : R →ₐ[A] P} (hf : ∀ y : M, IsUnit (f y)) (x : S)
include hf
noncomputable def liftAlgHom : S →ₐ[A] P where
  __ := lift hf
  commutes' r := show lift hf (algebraMap A S r) = _ by
    simp [IsScalarTower.algebraMap_apply A R S]
theorem liftAlgHom_toRingHom : (liftAlgHom hf : S →ₐ[A] P).toRingHom = lift hf := rfl
@[simp]
theorem coe_liftAlgHom : ⇑(liftAlgHom hf : S →ₐ[A] P) = lift hf := rfl
theorem liftAlgHom_apply : liftAlgHom hf x = lift hf x := rfl
end liftAlgHom
section AlgEquivOfAlgEquiv
variable {A : Type*} [CommSemiring A]
  {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R} (S : Type*)
  [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsLocalization M S]
  {P : Type*} [CommSemiring P] [Algebra A P] {T : Submonoid P} (Q : Type*)
  [CommSemiring Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsLocalization T Q]
  (h : R ≃ₐ[A] P) (H : Submonoid.map h M = T)
include H
@[simps!]
noncomputable def algEquivOfAlgEquiv : S ≃ₐ[A] Q where
  __ := ringEquivOfRingEquiv S Q h.toRingEquiv H
  commutes' _ := by dsimp; rw [IsScalarTower.algebraMap_apply A R S, map_eq,
    RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]
variable {S Q h}
theorem algEquivOfAlgEquiv_eq_map :
    (algEquivOfAlgEquiv S Q h H : S →+* Q) =
      map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl
theorem algEquivOfAlgEquiv_eq (x : R) :
    algEquivOfAlgEquiv S Q h H ((algebraMap R S) x) = algebraMap P Q (h x) := by
  simp
set_option linter.docPrime false in
theorem algEquivOfAlgEquiv_mk' (x : R) (y : M) :
    algEquivOfAlgEquiv S Q h H (mk' S x y) =
      mk' Q (h x) ⟨h y, show h y ∈ T from H ▸ Set.mem_image_of_mem h y.2⟩ := by
  simp [map_mk']
theorem algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv S Q h H).symm =
    algEquivOfAlgEquiv Q S h.symm (show Submonoid.map h.symm T = M by
      erw [← H, ← Submonoid.comap_equiv_eq_map_symm,
        Submonoid.comap_map_eq_of_injective h.injective]) := rfl
end AlgEquivOfAlgEquiv
section at_units
variable (R M)
noncomputable def atUnits (H : M ≤ IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [RingHom.map_mul, ← eq, ← hu, mul_assoc, ← RingHom.map_mul]
    simp
end at_units
end IsLocalization
section
variable (M N)
theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor
  · intro y
    convert (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S → P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    exact id
theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩
theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔
      haveI := (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }
variable (S) in
theorem isLocalization_iff_of_isLocalization [IsLocalization M S] [IsLocalization N S]
    [Algebra R P] : IsLocalization M P ↔ IsLocalization N P :=
  ⟨fun _ ↦ isLocalization_of_algEquiv N (algEquiv M S P),
    fun _ ↦ isLocalization_of_algEquiv M (algEquiv N S P)⟩
end
variable (M)
lemma commutes (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (M₁ M₂ : Submonoid R)
    [IsLocalization M₁ S₁] [IsLocalization M₂ S₂]
    [IsLocalization (Algebra.algebraMapSubmonoid S₂ M₁) T] :
    IsLocalization (Algebra.algebraMapSubmonoid S₁ M₂) T where
  map_units' := by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units' ⟨a, ha⟩)
  surj' a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units' ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T, ← hz, map_mul, ← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc, hr, mul_assoc, hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul, ← map_mul, mul_assoc, mul_comm _ c, ha, map_mul, map_mul]
    ring
end IsLocalization
namespace Localization
open IsLocalization
theorem mk_natCast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℕ) _
@[deprecated (since := "2024-04-17")]
alias mk_nat_cast := mk_natCast
variable [IsLocalization M S]
section
variable (S) (M)
@[simps!]
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique
end
nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _
nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _
theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']
theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', algEquiv_symm_mk']
lemma coe_algEquiv :
    (Localization.algEquiv M S : Localization M →+* S) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl
lemma coe_algEquiv_symm :
    ((Localization.algEquiv M S).symm : S →+* Localization M) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl
end Localization
end CommSemiring
section CommRing
variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]
namespace Localization
theorem mk_intCast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℤ) _
@[deprecated (since := "2024-04-17")]
alias mk_int_cast := mk_intCast
end Localization
open IsLocalization
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  letI := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM
section Algebra
variable {S} {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
include S
section
variable (S M)
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
end
section
variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable (S Rₘ Sₘ)
theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← _root_.map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)
variable (M)
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x
theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    IsLocalization.lift (M := M) (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm
end
variable (Rₘ Sₘ)
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS
end Algebra
end CommRing