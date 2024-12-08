import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Normal
open Polynomial minpoly IntermediateField
variable {R K L S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B] [Field K] [Field L]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [Algebra K S] [Algebra K L] [Algebra K A] [Algebra L S]
variable (R) in
def IsConjRoot (x y : A) : Prop := minpoly R x = minpoly R y
theorem isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R x = minpoly R y := Iff.rfl
namespace IsConjRoot
@[refl] theorem refl {x : A} : IsConjRoot R x x := rfl
@[symm] theorem symm {x y : A} (h : IsConjRoot R x y) : IsConjRoot R y x := Eq.symm h
@[trans] theorem trans {x y z: A} (h₁ : IsConjRoot R x y) (h₂ : IsConjRoot R y z) :
    IsConjRoot R x z := Eq.trans h₁ h₂
variable (R A) in
def setoid : Setoid A where
  r := IsConjRoot R
  iseqv := ⟨fun _ => refl, symm, trans⟩
theorem aeval_eq_zero {x y : A} (h : IsConjRoot R x y) : aeval y (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R y
theorem add_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x + algebraMap K S r) (y + algebraMap K S r) := by
  rw [isConjRoot_def, minpoly.add_algebraMap x r, minpoly.add_algebraMap y r, h]
theorem sub_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x - algebraMap K S r) (y - algebraMap K S r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h
theorem neg {x y : S} (h : IsConjRoot K x y) :
    IsConjRoot K (-x) (-y) := by
  rw [isConjRoot_def, minpoly.neg x, minpoly.neg y, h]
end IsConjRoot
open IsConjRoot
theorem isConjRoot_algHom_iff_of_injective {x y : A} {f : A →ₐ[R] B}
    (hf : Function.Injective f) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y := by
  rw [isConjRoot_def, isConjRoot_def, algHom_eq f hf, algHom_eq f hf]
theorem isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A]
    [Nontrivial B] {x y : A} (f : A →ₐ[R] B) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y :=
  isConjRoot_algHom_iff_of_injective f.injective
theorem isConjRoot_of_aeval_eq_zero [IsDomain A] {x y : A} (hx : IsIntegral K x)
    (h : aeval y (minpoly K x) = 0) : IsConjRoot K x y :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)
theorem isConjRoot_iff_aeval_eq_zero [IsDomain A] {x y : A}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ aeval y (minpoly K x) = 0 :=
  ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩
@[simp]
theorem isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)
@[simp]
theorem isConjRoot_of_algEquiv' (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R (s x) x :=
  (minpoly.algEquiv_eq s x)
@[simp]
theorem isConjRoot_of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  isConjRoot_def.mpr <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)
theorem IsConjRoot.exists_algEquiv [Normal K L] {x y: L} (h : IsConjRoot K x y) :
    ∃ σ : L ≃ₐ[K] L, σ y = x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩
theorem isConjRoot_iff_exists_algEquiv [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ ∃ σ : L ≃ₐ[K] L, σ y = x :=
  ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ (isConjRoot_of_algEquiv _ _).symm⟩
theorem isConjRoot_iff_orbitRel [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ MulAction.orbitRel (L ≃ₐ[K] L) L x y:=
  (isConjRoot_iff_exists_algEquiv)
variable [IsDomain S]
theorem IsConjRoot.of_isScalarTower [IsScalarTower K L S] {x y : S} (hx : IsIntegral K x)
    (h : IsConjRoot L x y) : IsConjRoot K x y :=
  isConjRoot_of_aeval_eq_zero hx <| minpoly.aeval_of_isScalarTower K x y (aeval_eq_zero h)
theorem isConjRoot_iff_mem_minpoly_aroots {x y : S} (h : IsIntegral K x) :
    IsConjRoot K x y ↔ y ∈ (minpoly K x).aroots S := by
  rw [Polynomial.mem_aroots, isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h
theorem isConjRoot_iff_mem_minpoly_rootSet {x y : S}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ y ∈ (minpoly K x).rootSet S :=
  (isConjRoot_iff_mem_minpoly_aroots h).trans (by simp [rootSet])
namespace IsConjRoot
theorem isIntegral {x y : A} (hx : IsIntegral R x) (h : IsConjRoot R x y) :
    IsIntegral R y :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R y⟩
theorem eq_algebraMap_of_injective [Nontrivial R] [NoZeroSMulDivisors R S] {r : R} {x : S}
    (h : IsConjRoot R (algebraMap R S r) x) (hf : Function.Injective (algebraMap R S)) :
    x = algebraMap R S r := by
  rw [IsConjRoot, minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x ∈ (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this
theorem eq_algebraMap {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x) :
    x = algebraMap K S r :=
  eq_algebraMap_of_injective h (algebraMap K S).injective
theorem eq_zero_of_injective [Nontrivial R] [NoZeroSMulDivisors R S] {x : S} (h : IsConjRoot R 0 x)
    (hf : Function.Injective (algebraMap R S)) : x = 0 :=
  (algebraMap R S).map_zero ▸ (eq_algebraMap_of_injective ((algebraMap R S).map_zero ▸ h) hf)
theorem eq_zero {x : S} (h : IsConjRoot K 0 x) : x = 0 :=
  eq_zero_of_injective h (algebraMap K S).injective
end IsConjRoot
theorem isConjRoot_iff_eq_algebraMap_of_injective [Nontrivial R] [NoZeroSMulDivisors R S] {r : R}
    {x : S} (hf : Function.Injective (algebraMap R S)) :
    IsConjRoot R (algebraMap R S r) x ↔ x = algebraMap R S r :=
    ⟨fun h => eq_algebraMap_of_injective h hf, fun h => h.symm ▸ rfl⟩
@[simp]
theorem isConjRoot_iff_eq_algebraMap {r : K} {x : S} :
    IsConjRoot K (algebraMap K S r) x ↔ x = algebraMap K S r :=
  isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective
@[simp]
theorem isConjRoot_iff_eq_algebraMap' {r : K} {x : S} :
    IsConjRoot K x (algebraMap K S r) ↔ x = algebraMap K S r :=
  eq_comm.trans <| isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective
theorem isConjRoot_zero_iff_eq_zero_of_injective [Nontrivial R] {x : S} [NoZeroSMulDivisors R S]
    (hf : Function.Injective (algebraMap R S)) : IsConjRoot R 0 x ↔ x = 0 :=
  ⟨fun h => eq_zero_of_injective h hf, fun h => h.symm ▸ rfl⟩
@[simp]
theorem isConjRoot_zero_iff_eq_zero {x : S} : IsConjRoot K 0 x ↔ x = 0 :=
  isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective
@[simp]
theorem isConjRoot_zero_iff_eq_zero' {x : S} : IsConjRoot K x 0 ↔ x = 0 :=
  eq_comm.trans <| isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective
namespace IsConjRoot
theorem ne_zero_of_injective [Nontrivial R] [NoZeroSMulDivisors R S] {x y : S} (hx : x ≠ 0)
    (h : IsConjRoot R x y) (hf : Function.Injective (algebraMap R S)) : y ≠ 0 :=
  fun g => hx (eq_zero_of_injective (g ▸ h.symm) hf)
theorem ne_zero {x y : S} (hx : x ≠ 0) (h : IsConjRoot K x y) : y ≠ 0 :=
  ne_zero_of_injective hx h (algebraMap K S).injective
end IsConjRoot
theorem not_mem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ y : L, x ≠ y ∧ IsConjRoot K x y := by
  calc
    _ ↔ 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 ≤ Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ ∃ y : ((minpoly K x).rootSet L), ↑y ≠ x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mpr hy⟩,
          fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mp hy⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨y, hy⟩, hne⟩ => ⟨y, ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hy⟩⟩,
          fun ⟨y, hne, hy⟩ => ⟨⟨y,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hy⟩, hne.symm⟩⟩