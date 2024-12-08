import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.SpecificGroups.Cyclic
section
open Finset Polynomial Function Nat
section CancelMonoidWithZero
variable {M : Type*} [CancelMonoidWithZero M] [Finite M]
theorem mul_right_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => a * b :=
  Finite.injective_iff_bijective.1 <| mul_right_injective₀ ha
theorem mul_left_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => b * a :=
  Finite.injective_iff_bijective.1 <| mul_left_injective₀ ha
def Fintype.groupWithZeroOfCancel (M : Type*) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M]
    [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [Inv.inv, dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp [Inv.inv, dif_pos rfl] }
theorem exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Subsingleton Rˣ] {a b c : R} {n : ℕ} (cp : IsCoprime a b) (h : a * b = c ^ n) :
    ∃ d : R, a = d ^ n := by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact  
    dvd_add (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_right _ _) _)
nonrec
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Subsingleton Rˣ] {n : ℕ} {c : R} {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j))
    (hprod : ∏ i ∈ s, f i = c ^ n) : ∀ i ∈ s, ∃ d : R, f i = d ^ n := by
  classical
    intro i hi
    rw [← insert_erase hi, prod_insert (not_mem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.not_mem_erase _) hj
end CancelMonoidWithZero
variable {R : Type*} {G : Type*}
section Ring
variable [Ring R] [IsDomain R] [Fintype R]
def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R where
  __ := Fintype.groupWithZeroOfCancel R
  __ := ‹Ring R›
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }
theorem Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)
end Ring
variable [CommRing R] [IsDomain R] [Group G]
theorem card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G →* R) (hf : Injective f)
    {n : ℕ} (hn : 0 < n) (g₀ : G) :
    #{g | g ^ n = g₀} ≤ Multiset.card (nthRoots n (f g₀)) := by
  haveI : DecidableEq R := Classical.decEq _
  calc
    _ ≤ #(nthRoots n (f g₀)).toFinset := card_le_card_of_injOn f (by aesop) hf.injOn
    _ ≤ _ := (nthRoots n (f g₀)).toFinset_card_le
theorem isCyclic_of_subgroup_isDomain [Finite G] (f : G →* R) (hf : Injective f) : IsCyclic G := by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))
instance [Finite Rˣ] : IsCyclic Rˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom R) <| Units.ext
section
variable (S : Subgroup Rˣ) [Finite S]
instance subgroup_units_cyclic : IsCyclic S := by
  apply isCyclic_of_subgroup_isDomain (R := R) (G := S) _ _
  · exact MonoidHom.mk (OneHom.mk (fun s => ↑s.val) rfl) (by simp)
  · exact Units.ext.comp Subtype.val_injective
end
section EuclideanDivision
namespace Polynomial
variable (K : Type) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]
theorem div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) :
    ∃ q r : R[X], r.degree < g.degree ∧
      (algebraMap R[X] K f) / (algebraMap R[X] K g) =
        algebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g) := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp [hg']
    rw [add_comm, mul_comm, ← map_mul, ← map_add, modByMonic_add_div f hg]
end Polynomial
end EuclideanDivision
variable [Fintype G]
@[deprecated (since := "2024-06-10")]
alias card_fiber_eq_of_mem_range := MonoidHom.card_fiber_eq_of_mem_range
theorem sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 := by
  classical
    obtain ⟨x, hx⟩ : ∃ x : MonoidHom.range f.toHomUnits,
        ∀ y : MonoidHom.range f.toHomUnits, y ∈ Submonoid.powers x :=
      IsCyclic.exists_monoid_generator
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hf
      ext g
      rw [MonoidHom.one_apply]
      cases' hx ⟨f.toHomUnits g, g, rfl⟩ with n hn
      rwa [Subtype.ext_iff, Units.ext_iff, Subtype.coe_mk, MonoidHom.coe_toHomUnits, one_pow,
        eq_comm] at hn
    replace hx1 : (x.val : R) - 1 ≠ 0 := 
      fun h => hx1 (Subtype.eq (Units.ext (sub_eq_zero.1 h)))
    let c := #{g | f.toHomUnits g = 1}
    calc
      ∑ g : G, f g = ∑ g : G, (f.toHomUnits g : R) := rfl
      _ = ∑ u ∈ univ.image f.toHomUnits, #{g | f.toHomUnits g = u} • (u : R) :=
        sum_comp ((↑) : Rˣ → R) f.toHomUnits
      _ = ∑ u ∈ univ.image f.toHomUnits, c • (u : R) :=
        (sum_congr rfl fun u hu => congr_arg₂ _ ?_ rfl)
      _ = ∑ b : MonoidHom.range f.toHomUnits, c • ((b : Rˣ) : R) :=
        (Finset.sum_subtype _ (by simp) _)
      _ = c • ∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R) := smul_sum.symm
      _ = c • (0 : R) := congr_arg₂ _ rfl ?_
      _ = (0 : R) := smul_zero _
    · 
      show #{g : G | f.toHomUnits g = u} = c
      apply MonoidHom.card_fiber_eq_of_mem_range f.toHomUnits
      · simpa only [mem_image, mem_univ, true_and, Set.mem_range] using hu
      · exact ⟨1, f.toHomUnits.map_one⟩
    show (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R)) = 0
    calc
      (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R))
        = ∑ n ∈ range (orderOf x), ((x : Rˣ) : R) ^ n :=
        Eq.symm <|
          sum_nbij (x ^ ·) (by simp only [mem_univ, forall_true_iff])
            (by simpa using pow_injOn_Iio_orderOf)
            (fun b _ => let ⟨n, hn⟩ := hx b
              ⟨n % orderOf x, mem_range.2 (Nat.mod_lt _ (orderOf_pos _)),
               by dsimp at hn ⊢; rw [pow_mod_orderOf, hn]⟩)
            (by simp only [imp_true_iff, eq_self_iff_true, Subgroup.coe_pow,
                Units.val_pow_eq_pow_val])
      _ = 0 := ?_
    rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul]
    norm_cast
    simp [pow_orderOf_eq_one]
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] :
    ∑ g : G, f g = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h
  · simp [h, card_univ]
  · rw [cast_zero] 
    exact sum_hom_units_eq_zero f h
end