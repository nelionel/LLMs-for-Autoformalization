import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.CharP.Reduced
open Function Polynomial
class PerfectRing (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p] : Prop where
  bijective_frobenius : Bijective <| frobenius R p
section PerfectRing
variable (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]
lemma PerfectRing.ofSurjective (R : Type*) (p : ℕ) [CommRing R] [ExpChar R p]
    [IsReduced R] (h : Surjective <| frobenius R p) : PerfectRing R p :=
  ⟨frobenius_inj R p, h⟩
instance PerfectRing.ofFiniteOfIsReduced (R : Type*) [CommRing R] [ExpChar R p]
    [Finite R] [IsReduced R] : PerfectRing R p :=
  ofSurjective _ _ <| Finite.surjective_of_injective (frobenius_inj R p)
variable [PerfectRing R p]
@[simp]
theorem bijective_frobenius : Bijective (frobenius R p) := PerfectRing.bijective_frobenius
theorem bijective_iterateFrobenius : Bijective (iterateFrobenius R p n) :=
  coe_iterateFrobenius R p n ▸ (bijective_frobenius R p).iterate n
@[simp]
theorem injective_frobenius : Injective (frobenius R p) := (bijective_frobenius R p).1
@[simp]
theorem surjective_frobenius : Surjective (frobenius R p) := (bijective_frobenius R p).2
@[simps! apply]
noncomputable def frobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (frobenius R p) PerfectRing.bijective_frobenius
@[simp]
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv R p) = frobenius R p := rfl
theorem frobeniusEquiv_def (x : R) : frobeniusEquiv R p x = x ^ p := rfl
@[simps! apply]
noncomputable def iterateFrobeniusEquiv : R ≃+* R :=
  RingEquiv.ofBijective (iterateFrobenius R p n) (bijective_iterateFrobenius R p n)
@[simp]
theorem coe_iterateFrobeniusEquiv : ⇑(iterateFrobeniusEquiv R p n) = iterateFrobenius R p n := rfl
theorem iterateFrobeniusEquiv_def (x : R) : iterateFrobeniusEquiv R p n x = x ^ p ^ n := rfl
theorem iterateFrobeniusEquiv_add_apply (x : R) : iterateFrobeniusEquiv R p (m + n) x =
    iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x) :=
  iterateFrobenius_add_apply R p m n x
theorem iterateFrobeniusEquiv_add : iterateFrobeniusEquiv R p (m + n) =
    (iterateFrobeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m) :=
  RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)
theorem iterateFrobeniusEquiv_symm_add_apply (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x =
    (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p n).symm x) :=
  (iterateFrobeniusEquiv R p (m + n)).injective <| by rw [RingEquiv.apply_symm_apply, add_comm,
    iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
theorem iterateFrobeniusEquiv_symm_add : (iterateFrobeniusEquiv R p (m + n)).symm =
    (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm :=
  RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)
theorem iterateFrobeniusEquiv_zero_apply (x : R) : iterateFrobeniusEquiv R p 0 x = x := by
  rw [iterateFrobeniusEquiv_def, pow_zero, pow_one]
theorem iterateFrobeniusEquiv_one_apply (x : R) : iterateFrobeniusEquiv R p 1 x = x ^ p := by
  rw [iterateFrobeniusEquiv_def, pow_one]
@[simp]
theorem iterateFrobeniusEquiv_zero  : iterateFrobeniusEquiv R p 0 = RingEquiv.refl R :=
  RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)
@[simp]
theorem iterateFrobeniusEquiv_one : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p :=
  RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)
theorem iterateFrobeniusEquiv_eq_pow : iterateFrobeniusEquiv R p n = frobeniusEquiv R p ^ n :=
  DFunLike.ext' <| show _ = ⇑(RingAut.toPerm _ _) by
    rw [map_pow, Equiv.Perm.coe_pow]; exact (pow_iterate p n).symm
theorem iterateFrobeniusEquiv_symm :
    (iterateFrobeniusEquiv R p n).symm = (frobeniusEquiv R p).symm ^ n := by
  rw [iterateFrobeniusEquiv_eq_pow]; exact (inv_pow _ _).symm
@[simp]
theorem frobeniusEquiv_symm_apply_frobenius (x : R) :
    (frobeniusEquiv R p).symm (frobenius R p x) = x :=
  leftInverse_surjInv PerfectRing.bijective_frobenius x
@[simp]
theorem frobenius_apply_frobeniusEquiv_symm (x : R) :
    frobenius R p ((frobeniusEquiv R p).symm x) = x :=
  surjInv_eq _ _
@[simp]
theorem frobenius_comp_frobeniusEquiv_symm :
    (frobenius R p).comp (frobeniusEquiv R p).symm = RingHom.id R := by
  ext; simp
@[simp]
theorem frobeniusEquiv_symm_comp_frobenius :
    ((frobeniusEquiv R p).symm : R →+* R).comp (frobenius R p) = RingHom.id R := by
  ext; simp
@[simp]
theorem frobeniusEquiv_symm_pow_p (x : R) : ((frobeniusEquiv R p).symm x) ^ p = x :=
  frobenius_apply_frobeniusEquiv_symm R p x
theorem injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y := (frobeniusEquiv R p).injective h
lemma polynomial_expand_eq (f : R[X]) :
    expand R p f = (f.map (frobeniusEquiv R p).symm) ^ p := by
  rw [← (f.map (S := R) (frobeniusEquiv R p).symm).expand_char p, map_expand, map_map,
    frobenius_comp_frobeniusEquiv_symm, map_id]
@[simp]
theorem not_irreducible_expand (R p) [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (f : R[X]) : ¬ Irreducible (expand R p f) := by
  rw [polynomial_expand_eq]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one
instance instPerfectRingProd (S : Type*) [CommSemiring S] [ExpChar S p] [PerfectRing S p] :
    PerfectRing (R × S) p where
  bijective_frobenius := (bijective_frobenius R p).prodMap (bijective_frobenius S p)
end PerfectRing
class PerfectField (K : Type*) [Field K] : Prop where
  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable
lemma PerfectRing.toPerfectField (K : Type*) (p : ℕ)
    [Field K] [ExpChar K p] [PerfectRing K p] : PerfectField K := by
  obtain hp | ⟨hp⟩ := ‹ExpChar K p›
  · exact ⟨Irreducible.separable⟩
  refine PerfectField.mk fun hf ↦ ?_
  rcases separable_or p hf with h | ⟨-, g, -, rfl⟩
  · assumption
  · exfalso; revert hf; haveI := Fact.mk hp; simp
namespace PerfectField
variable {K : Type*} [Field K]
instance ofCharZero [CharZero K] : PerfectField K := ⟨Irreducible.separable⟩
instance ofFinite [Finite K] : PerfectField K := by
  obtain ⟨p, _instP⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  exact PerfectRing.toPerfectField K p
variable [PerfectField K]
instance toPerfectRing (p : ℕ) [ExpChar K p] : PerfectRing K p := by
  refine PerfectRing.ofSurjective _ _ fun y ↦ ?_
  let f : K[X] := X ^ p - C y
  let L := f.SplittingField
  let ι := algebraMap K L
  have hf_deg : f.degree ≠ 0 := by
    rw [degree_X_pow_sub_C (expChar_pos K p) y, p.cast_ne_zero]; exact (expChar_pos K p).ne'
  let a : L := f.rootOfSplits ι (SplittingField.splits f) hf_deg
  have hfa : aeval a f = 0 := by rw [aeval_def, map_rootOfSplits _ (SplittingField.splits f) hf_deg]
  have ha_pow : a ^ p = ι y := by rwa [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hfa
  let g : K[X] := minpoly K a
  suffices (g.map ι).natDegree = 1 by
    rw [g.natDegree_map, ← degree_eq_iff_natDegree_eq_of_pos Nat.one_pos] at this
    obtain ⟨a' : K, ha' : ι a' = a⟩ := minpoly.mem_range_of_degree_eq_one K a this
    refine ⟨a', NoZeroSMulDivisors.algebraMap_injective K L ?_⟩
    rw [RingHom.map_frobenius, ha', frobenius_def, ha_pow]
  have hg_dvd : g.map ι ∣ (X - C a) ^ p := by
    convert Polynomial.map_dvd ι (minpoly.dvd K a hfa)
    rw [sub_pow_expChar, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← ha_pow, map_pow]
  have ha : IsIntegral K a := .of_finite K a
  have hg_pow : g.map ι = (X - C a) ^ (g.map ι).natDegree := by
    obtain ⟨q, -, hq⟩ := (dvd_prime_pow (prime_X_sub_C a) p).mp hg_dvd
    rw [eq_of_monic_of_associated ((minpoly.monic ha).map ι) ((monic_X_sub_C a).pow q) hq,
      natDegree_pow, natDegree_X_sub_C, mul_one]
  have hg_sep : (g.map ι).Separable := (separable_of_irreducible <| minpoly.irreducible ha).map
  rw [hg_pow] at hg_sep
  refine (Separable.of_pow (not_isUnit_X_sub_C a) ?_ hg_sep).2
  rw [g.natDegree_map ι, ← Nat.pos_iff_ne_zero, natDegree_pos_iff_degree_pos]
  exact minpoly.degree_pos ha
theorem separable_iff_squarefree {g : K[X]} : g.Separable ↔ Squarefree g := by
  refine ⟨Separable.squarefree, fun sqf ↦ isCoprime_of_irreducible_dvd (sqf.ne_zero ·.1) ?_⟩
  rintro p (h : Irreducible p) ⟨q, rfl⟩ (dvd : p ∣ derivative (p * q))
  replace dvd : p ∣ q := by
    rw [derivative_mul, dvd_add_left (dvd_mul_right p _)] at dvd
    exact (separable_of_irreducible h).dvd_of_dvd_mul_left dvd
  exact (h.1 : ¬ IsUnit p) (sqf _ <| mul_dvd_mul_left _ dvd)
end PerfectField
instance Algebra.IsAlgebraic.isSeparable_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] : Algebra.IsSeparable K L :=
  ⟨fun x ↦ PerfectField.separable_of_irreducible <|
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩
theorem Algebra.IsAlgebraic.perfectField {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [PerfectField K] : PerfectField L := ⟨fun {f} hf ↦ by
  obtain ⟨_, _, hi, h⟩ := hf.exists_dvd_monic_irreducible_of_isIntegral (K := K)
  exact (PerfectField.separable_of_irreducible hi).map |>.of_dvd h⟩
namespace Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] (p n : ℕ) [ExpChar R p] (f : R[X])
open Multiset
theorem roots_expand_pow_map_iterateFrobenius_le :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) ≤ p ^ n • f.roots := by
  classical
  refine le_iff_count.2 fun r ↦ ?_
  by_cases h : ∃ s, r = s ^ p ^ n
  · obtain ⟨s, rfl⟩ := h
    simp_rw [count_nsmul, count_roots, ← rootMultiplicity_expand_pow, ← count_roots, count_map,
      count_eq_card_filter_eq]
    exact card_le_card (monotone_filter_right _ fun _ h ↦ iterateFrobenius_inj R p n h)
  convert Nat.zero_le _
  simp_rw [count_map, card_eq_zero]
  exact ext' fun t ↦ count_zero t ▸ count_filter_of_neg fun h' ↦ h ⟨t, h'⟩
theorem roots_expand_map_frobenius_le :
    (expand R p f).roots.map (frobenius R p) ≤ p • f.roots := by
  rw [← iterateFrobenius_one]
  convert ← roots_expand_pow_map_iterateFrobenius_le p 1 f <;> apply pow_one
theorem roots_expand_pow_image_iterateFrobenius_subset [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) ⊆ f.roots.toFinset := by
  rw [Finset.image_toFinset, ← (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne',
    toFinset_subset]
  exact subset_of_le (roots_expand_pow_map_iterateFrobenius_le p n f)
theorem roots_expand_image_frobenius_subset [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) ⊆ f.roots.toFinset := by
  rw [← iterateFrobenius_one]
  convert ← roots_expand_pow_image_iterateFrobenius_subset p 1 f
  apply pow_one
section PerfectRing
variable {p n f}
variable [PerfectRing R p]
theorem roots_expand_pow :
    (expand R (p ^ n) f).roots = p ^ n • f.roots.map (iterateFrobeniusEquiv R p n).symm := by
  classical
  refine ext' fun r ↦ ?_
  rw [count_roots, rootMultiplicity_expand_pow, ← count_roots, count_nsmul, count_map,
    count_eq_card_filter_eq]; congr; ext
  exact (iterateFrobeniusEquiv R p n).eq_symm_apply.symm
theorem roots_expand : (expand R p f).roots = p • f.roots.map (frobeniusEquiv R p).symm := by
  conv_lhs => rw [← pow_one p, roots_expand_pow, iterateFrobeniusEquiv_eq_pow, pow_one]
  rfl
theorem roots_X_pow_char_pow_sub_C {y : R} :
    (X ^ p ^ n - C y).roots = p ^ n • {(iterateFrobeniusEquiv R p n).symm y} := by
  have H := roots_expand_pow (p := p) (n := n) (f := X - C y)
  rwa [roots_X_sub_C, Multiset.map_singleton, map_sub, expand_X, expand_C] at H
theorem roots_X_pow_char_pow_sub_C_pow {y : R} {m : ℕ} :
    ((X ^ p ^ n - C y) ^ m).roots = (m * p ^ n) • {(iterateFrobeniusEquiv R p n).symm y} := by
  rw [roots_pow, roots_X_pow_char_pow_sub_C, mul_smul]
theorem roots_X_pow_char_sub_C {y : R} :
    (X ^ p - C y).roots = p • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C (p := p) (n := 1) (y := y)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H
theorem roots_X_pow_char_sub_C_pow {y : R} {m : ℕ} :
    ((X ^ p - C y) ^ m).roots = (m * p) • {(frobeniusEquiv R p).symm y} := by
  have H := roots_X_pow_char_pow_sub_C_pow (p := p) (n := 1) (y := y) (m := m)
  rwa [pow_one, iterateFrobeniusEquiv_one] at H
theorem roots_expand_pow_map_iterateFrobenius :
    (expand R (p ^ n) f).roots.map (iterateFrobenius R p n) = p ^ n • f.roots := by
  simp_rw [← coe_iterateFrobeniusEquiv, roots_expand_pow, Multiset.map_nsmul,
    Multiset.map_map, comp_apply, RingEquiv.apply_symm_apply, map_id']
theorem roots_expand_map_frobenius : (expand R p f).roots.map (frobenius R p) = p • f.roots := by
  simp [roots_expand, Multiset.map_nsmul]
theorem roots_expand_image_iterateFrobenius [DecidableEq R] :
    (expand R (p ^ n) f).roots.toFinset.image (iterateFrobenius R p n) = f.roots.toFinset := by
  rw [Finset.image_toFinset, roots_expand_pow_map_iterateFrobenius,
    (roots f).toFinset_nsmul _ (expChar_pow_pos R p n).ne']
theorem roots_expand_image_frobenius [DecidableEq R] :
    (expand R p f).roots.toFinset.image (frobenius R p) = f.roots.toFinset := by
  rw [Finset.image_toFinset, roots_expand_map_frobenius,
      (roots f).toFinset_nsmul _ (expChar_pos R p).ne']
end PerfectRing
variable [DecidableEq R]
noncomputable def rootsExpandToRoots : (expand R p f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p, roots_expand_image_frobenius_subset p f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (frobenius_inj R p <| Subtype.ext_iff.1 h)
@[simp]
theorem rootsExpandToRoots_apply (x) : (rootsExpandToRoots p f x : R) = x ^ p := rfl
open scoped Classical in
noncomputable def rootsExpandPowToRoots :
    (expand R (p ^ n) f).roots.toFinset ↪ f.roots.toFinset where
  toFun x := ⟨x ^ p ^ n,
    roots_expand_pow_image_iterateFrobenius_subset p n f (Finset.mem_image_of_mem _ x.2)⟩
  inj' _ _ h := Subtype.ext (iterateFrobenius_inj R p n <| Subtype.ext_iff.1 h)
@[simp]
theorem rootsExpandPowToRoots_apply (x) : (rootsExpandPowToRoots p n f x : R) = x ^ p ^ n := rfl
variable [PerfectRing R p]
noncomputable def rootsExpandEquivRoots : (expand R p f).roots.toFinset ≃ f.roots.toFinset :=
  ((frobeniusEquiv R p).image _).trans <| .Set.ofEq <| show _ '' setOf (· ∈ _) = setOf (· ∈ _) by
    classical simp_rw [← roots_expand_image_frobenius (p := p) (f := f), Finset.mem_val,
      Finset.setOf_mem, Finset.coe_image, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      frobeniusEquiv_apply]
@[simp]
theorem rootsExpandEquivRoots_apply (x) : (rootsExpandEquivRoots p f x : R) = x ^ p := rfl
noncomputable def rootsExpandPowEquivRoots (n : ℕ) :
    (expand R (p ^ n) f).roots.toFinset ≃ f.roots.toFinset :=
  ((iterateFrobeniusEquiv R p n).image _).trans <|
    .Set.ofEq <| show _ '' (setOf (· ∈ _)) = setOf (· ∈ _) by
    classical simp_rw [← roots_expand_image_iterateFrobenius (p := p) (f := f) (n := n),
      Finset.mem_val, Finset.setOf_mem, Finset.coe_image, RingEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, iterateFrobeniusEquiv_apply]
@[simp]
theorem rootsExpandPowEquivRoots_apply (n : ℕ) (x) :
    (rootsExpandPowEquivRoots p f n x : R) = x ^ p ^ n := rfl
end Polynomial