import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.WittVector.WittPolynomial
open MvPolynomial Set
open Finset (range)
open Finsupp (single)
attribute [-simp] coe_eval₂Hom
variable {p : ℕ} {R : Type*} {idx : Type*} [CommRing R]
open scoped Witt
section PPrime
variable (p)
variable [hp : Fact p.Prime]
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W_" => wittPolynomial p
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W" => wittPolynomial p _
noncomputable def wittStructureRat (Φ : MvPolynomial idx ℚ) (n : ℕ) : MvPolynomial (idx × ℕ) ℚ :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) (xInTermsOfW p ℚ n)
theorem wittStructureRat_prop (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ ℚ k)) Φ)
          (bind₁ (xInTermsOfW p ℚ) (W_ ℚ n)) := by
      rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
      rw [bind₁_xInTermsOfW_wittPolynomial p _ n, bind₁_X_right]
theorem wittStructureRat_existsUnique (Φ : MvPolynomial idx ℚ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℚ,
      ∀ n : ℕ, bind₁ φ (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
  refine ⟨wittStructureRat p Φ, ?_, ?_⟩
  · intro n; apply wittStructureRat_prop
  · intro φ H
    funext n
    rw [show φ n = bind₁ φ (bind₁ (W_ ℚ) (xInTermsOfW p ℚ n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p, bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂Hom_congr (RingHom.ext_rat _ _) (funext H) rfl
theorem wittStructureRat_rec_aux (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n * C ((p : ℚ) ^ n) =
      bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
        ∑ i ∈ range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i) := by
  have := xInTermsOfW_aux p ℚ n
  replace := congr_arg (bind₁ fun k : ℕ => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) this
  rw [map_mul, bind₁_C_right] at this
  rw [wittStructureRat, this]; clear this
  conv_lhs => simp only [map_sub, bind₁_X_right]
  rw [sub_right_inj]
  simp only [map_sum, map_mul, bind₁_C_right, map_pow]
  rfl
theorem wittStructureRat_rec (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n =
      C (1 / (p : ℚ) ^ n) *
        (bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
          ∑ i ∈ range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i)) := by
  calc
    wittStructureRat p Φ n = C (1 / (p : ℚ) ^ n) * (wittStructureRat p Φ n * C ((p : ℚ) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm, ← C_mul, div_mul_cancel₀, C_1, mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)
noncomputable def wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  Finsupp.mapRange Rat.num (Rat.num_intCast 0) (wittStructureRat p (map (Int.castRingHom ℚ) Φ) n)
variable {p}
theorem bind₁_rename_expand_wittPolynomial (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n + 1 →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    bind₁ (fun b => rename (fun i => (b, i)) (expand p (W_ ℤ n))) Φ =
      bind₁ (fun i => expand p (wittStructureInt p Φ i)) (W_ ℤ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  have key := (wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n).symm
  apply_fun expand p at key
  simp only [expand_bind₁] at key
  rw [key]; clear key
  apply eval₂Hom_congr' rfl _ rfl
  rintro i hi -
  rw [wittPolynomial_vars, Finset.mem_range] at hi
  simp only [IH i hi]
theorem C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    (C ((p ^ n :) : ℤ) : MvPolynomial (idx × ℕ) ℤ) ∣
      bind₁ (fun b : idx => rename (fun i => (b, i)) (wittPolynomial p ℤ n)) Φ -
        ∑ i ∈ range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i) := by
  cases' n with n
  · simp only [isUnit_one, Int.ofNat_zero, Int.ofNat_succ, zero_add, pow_zero, C_1, IsUnit.dvd,
      Nat.cast_one]
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  rw [C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_bind₁]
  simp only [map_rename, map_wittPolynomial, wittPolynomial_zmod_self]
  rw [key]; clear key IH
  rw [bind₁, aeval_wittPolynomial, map_sum, map_sum, Finset.sum_congr rfl]
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [← sub_eq_zero, ← RingHom.map_sub, ← C_dvd_iff_zmod, C_eq_coe_nat, ← Nat.cast_pow,
    ← Nat.cast_pow, C_eq_coe_nat, ← mul_sub]
  have : p ^ (n + 1) = p ^ k * p ^ (n - k + 1) := by
    rw [← pow_add, ← add_assoc]; congr 2; rw [add_comm, ← tsub_eq_iff_eq_add_of_le hk]
  rw [this]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  apply mul_dvd_mul_left ((p : MvPolynomial (idx × ℕ) ℤ) ^ k)
  rw [show p ^ (n + 1 - k) = p * p ^ (n - k) by rw [← pow_succ', ← tsub_add_eq_add_tsub hk]]
  rw [pow_mul]
  apply dvd_sub_pow_of_dvd_sub
  rw [← C_eq_coe_nat, C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_expand, RingHom.map_pow,
    MvPolynomial.expand_zmod]
variable (p)
@[simp]
theorem map_wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    map (Int.castRingHom ℚ) (wittStructureInt p Φ n) =
      wittStructureRat p (map (Int.castRingHom ℚ) Φ) n := by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [wittStructureInt, map_mapRange_eq_iff, Int.coe_castRingHom]
  intro c
  rw [wittStructureRat_rec, coeff_C_mul, mul_comm, mul_div_assoc', mul_one]
  have sum_induction_steps :
      map (Int.castRingHom ℚ)
        (∑ i ∈ range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i)) =
      ∑ i ∈ range n,
        C ((p : ℚ) ^ i) * wittStructureRat p (map (Int.castRingHom ℚ) Φ) i ^ p ^ (n - i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [IH i hi, RingHom.map_mul, RingHom.map_pow, map_C]
    rfl
  simp only [← sum_induction_steps, ← map_wittPolynomial p (Int.castRingHom ℚ), ← map_rename, ←
    map_bind₁, ← RingHom.map_sub, coeff_map]
  rw [show (p : ℚ) ^ n = ((↑(p ^ n) : ℤ) : ℚ) by norm_cast]
  rw [← Rat.den_eq_one_iff, eq_intCast, Rat.den_div_intCast_eq_one_iff]
  swap; · exact mod_cast pow_ne_zero n hp.1.ne_zero
  revert c; rw [← C_dvd_iff_dvd_coeff]
  exact C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum Φ n IH
theorem wittStructureInt_prop (Φ : MvPolynomial idx ℤ) (n) :
    bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
      bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have := wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]
theorem eq_wittStructureInt (Φ : MvPolynomial idx ℤ) (φ : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ) :
    φ = wittStructureInt p Φ := by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_wittStructureInt]
  revert k
  refine congr_fun ?_
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom ℚ) Φ))
  · intro n
    specialize h n
    apply_fun map (Int.castRingHom ℚ) at h
    simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
      AlgHom.coe_toRingHom] using h
  · intro n; apply wittStructureRat_prop
theorem wittStructureInt_existsUnique (Φ : MvPolynomial idx ℤ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℤ,
      ∀ n : ℕ,
        bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ ℤ n)) Φ :=
  ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩
theorem witt_structure_prop (Φ : MvPolynomial idx ℤ) (n) :
    aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p ℤ n) =
      aeval (fun i => rename (Prod.mk i) (W n)) Φ := by
  convert congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;>
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
  · simp only [map_rename, map_wittPolynomial]
theorem wittStructureInt_rename {σ : Type*} (Φ : MvPolynomial idx ℤ) (f : idx → σ) (n : ℕ) :
    wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (wittStructureInt p Φ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl
@[simp]
theorem constantCoeff_wittStructureRat_zero (Φ : MvPolynomial idx ℚ) :
    constantCoeff (wittStructureRat p Φ 0) = constantCoeff Φ := by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]
theorem constantCoeff_wittStructureRat (Φ : MvPolynomial idx ℚ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureRat p Φ n) = 0 := by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]
@[simp]
theorem constantCoeff_wittStructureInt_zero (Φ : MvPolynomial idx ℤ) :
    constantCoeff (wittStructureInt p Φ 0) = constantCoeff Φ := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat_zero,
    constantCoeff_map]
theorem constantCoeff_wittStructureInt (Φ : MvPolynomial idx ℤ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureInt p Φ n) = 0 := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat, RingHom.map_zero]
  rw [constantCoeff_map, h, RingHom.map_zero]
variable (R)
theorem wittStructureRat_vars [Fintype idx] (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    (wittStructureRat p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  rw [wittStructureRat]
  intro x hx
  simp only [Finset.mem_product, true_and, Finset.mem_univ, Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [wittPolynomial_vars, Finset.mem_range] at hj
  replace hk := xInTermsOfW_vars_subset p _ hk
  rw [Finset.mem_range] at hk
  exact lt_of_lt_of_le hj hk
theorem wittStructureInt_vars [Fintype idx] (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    (wittStructureInt p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  have : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← vars_map_of_injective _ this, map_wittStructureInt]
  apply wittStructureRat_vars
end PPrime