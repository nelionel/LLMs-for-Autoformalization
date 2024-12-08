import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Norm.Basic
universe u
variable {K : Type u} [Field K]
open Polynomial IntermediateField AdjoinRoot
section Splits
lemma root_X_pow_sub_C_pow (n : ℕ) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]
lemma root_X_pow_sub_C_ne_zero {n : ℕ} (hn : 1 < n) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 :=
  mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.not_eq_zero_of_lt hn))
    X_ne_zero <| by rwa [natDegree_X_pow_sub_C, natDegree_X]
lemma root_X_pow_sub_C_ne_zero' {n : ℕ} {a : K} (hn : 0 < n) (ha : a ≠ 0) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 := by
  obtain (rfl|hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]
  · exact root_X_pow_sub_C_ne_zero hn a
theorem X_pow_sub_C_splits_of_isPrimitiveRoot
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) :
    (X ^ n - C a).Splits (RingHom.id _) := by
  cases n.eq_zero_or_pos with
  | inl hn =>
    rw [hn, pow_zero, ← C.map_one, ← map_sub]
    exact splits_C _ _
  | inr hn =>
    rw [splits_iff_card_roots, ← nthRoots, hζ.card_nthRoots, natDegree_X_pow_sub_C, if_pos ⟨α, e⟩]
private
theorem X_pow_sub_C_eq_prod'
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i ∈ Finset.range n, (X - C (ζ ^ i * α)) := by
  rw [eq_prod_roots_of_monic_of_splits_id (monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn))
    (X_pow_sub_C_splits_of_isPrimitiveRoot hζ e), ← nthRoots, hζ.nthRoots_eq e, Multiset.map_map]
  rfl
lemma X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i ∈ Finset.range n, (X - C (ζ ^ i * α)) := by
  let K := FractionRing R
  let i := algebraMap R K
  have h := NoZeroSMulDivisors.algebraMap_injective R K
  apply_fun Polynomial.map i using map_injective i h
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul]
    using X_pow_sub_C_eq_prod' (hζ.map_of_injective h) hn <| map_pow i α n ▸ congrArg i e
end Splits
section Irreducible
lemma ne_zero_of_irreducible_X_pow_sub_C {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    n ≠ 0 := by
  rintro rfl
  rw [pow_zero, ← C.map_one, ← map_sub] at H
  exact not_irreducible_C _ H
lemma ne_zero_of_irreducible_X_pow_sub_C' {n : ℕ} (hn : n ≠ 1) {a : K}
    (H : Irreducible (X ^ n - C a)) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, sub_zero] at H
  exact not_irreducible_pow hn H
lemma root_X_pow_sub_C_eq_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0 := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this, pow_one, map_zero, sub_zero, ← mk_X, mk_self]
lemma root_X_pow_sub_C_ne_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 ↔ a ≠ 0 :=
  (root_X_pow_sub_C_eq_zero_iff H).not
theorem pow_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : ℕ} (hm : m ∣ n) (hm' : m ≠ 1) (b : K) : b ^ m ≠ a := by
  have hn : n ≠ 0 := fun e ↦ not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm, pow_mul, map_pow, hq] at H
  have : degree q = 0 := by
    simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 _ q rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)
@[stacks 09HF "We proved the result without the condition that `K` is char p in 09HF."]
theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_le hg'
    (X_pow_sub_C_ne_zero hp.pos a) (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg
  by_contra h
  have : Fact (Irreducible g) := ⟨hg⟩
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree := by
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      ← finrank_top', ← IntermediateField.adjoin_root_eq_top g,
      IntermediateField.adjoin.finrank,
      AdjoinRoot.minpoly_root hg.ne_zero, natDegree_mul_C]
    · simpa using hg.ne_zero
    · exact AdjoinRoot.isIntegral_root hg.ne_zero
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ ((pow_mem_range_pow_of_coprime this.symm a).mp ⟨_, key⟩).choose_spec
theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) {a : K} :
    Irreducible (X ^ p - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩
theorem X_pow_mul_sub_C_irreducible
    {n m : ℕ} {a : K} (hm : Irreducible (X ^ m - C a))
    (hn : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = X ^ m - C a),
      Irreducible (X ^ n - C (AdjoinSimple.gen K x))) :
    Irreducible (X ^ (n * m) - C a) := by
  have hm' : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← C.map_one, ← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)
theorem X_pow_sub_C_irreducible_of_odd
    {n : ℕ} (hn : Odd n) {a : K} (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | h₀ => simp [← Nat.not_even_iff_odd] at hn
  | h₁ => simpa using irreducible_X_sub_C a
  | h p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have : IsIntegral K x := not_not.mp fun h ↦ by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    apply IH (Nat.odd_mul.mp hn).2
    intros q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm _ b)
    rw [← map_pow, hb, ← adjoin.powerBasis_gen this,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hp.ne_zero.symm, (Nat.odd_mul.mp hn).1.neg_pow]
theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :=
  ⟨fun e _ hp hpn ↦ pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩
theorem X_pow_sub_C_irreducible_iff_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ d, d ∣ n → d ≠ 1 → ∀ b : K, b ^ d ≠ a) :=
  ⟨fun e _ ↦ pow_ne_of_irreducible_X_pow_sub_C e,
    fun H ↦ X_pow_sub_C_irreducible_of_odd hn fun p hp hpn ↦ (H p hpn hp.ne_one)⟩
theorem X_pow_sub_C_irreducible_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) (n : ℕ) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ (p ^ n) - C a) := by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intros q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha
theorem X_pow_sub_C_irreducible_iff_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) {n} (hn : n ≠ 0) {a : K} :
    Irreducible (X ^ p ^ n - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩
end Irreducible
variable {n : ℕ} (hζ : (primitiveRoots n K).Nonempty)
variable (a : K) (H : Irreducible (X ^ n - C a))
set_option quotPrecheck false in
scoped[KummerExtension] notation3 "K[" n "√" a "]" => AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)
attribute [nolint docBlame] KummerExtension.«termK[_√_]»
open scoped KummerExtension
section AdjoinRoot
include hζ H in
theorem Polynomial.separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable := by
  letI := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
  rw [← separable_map (algebraMap K K[n√a]), Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
    AdjoinRoot.algebraMap_eq,
    X_pow_sub_C_eq_prod (hζ.map_of_injective (algebraMap K _).injective) hn
    (root_X_pow_sub_C_pow n a), separable_prod_X_sub_C_iff']
  #adaptation_note
  have : MonoidHomClass (K →+* K[n√a]) K K[n√a] := inferInstance
  exact (hζ.map_of_injective (algebraMap K K[n√a]).injective).injOn_pow_mul
    (root_X_pow_sub_C_ne_zero (lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm hn')) _)
variable (n)
noncomputable
def autAdjoinRootXPowSubCHom :
    rootsOfUnity n K →* (K[n√a] →ₐ[K] K[n√a]) where
  toFun := fun η ↦ liftHom (X ^ n - C a) (((η : Kˣ) : K) • (root _) : K[n√a]) <| by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    rw [map_sub, map_pow, aeval_C, aeval_X, Algebra.smul_def, mul_pow, root_X_pow_sub_C_pow,
      AdjoinRoot.algebraMap_eq, ← map_pow, this, map_one, one_mul, sub_self]
  map_one' := algHom_ext <| by simp
  map_mul' := fun ε η ↦ algHom_ext <| by simp [mul_smul, smul_comm ((ε : Kˣ) : K)]
noncomputable
def autAdjoinRootXPowSubC :
    rootsOfUnity n K →* (K[n√a] ≃ₐ[K] K[n√a]) :=
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a).toHomUnits
variable {n}
lemma autAdjoinRootXPowSubC_root (η) :
    autAdjoinRootXPowSubC n a η (root _) = ((η : Kˣ) : K) • root _ := by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  apply liftHom_root
variable {a}
noncomputable
def AdjoinRootXPowSubCEquivToRootsOfUnity [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a]) :
    rootsOfUnity n K :=
  letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := n) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    split
    · exact one_pow _
    rw [div_pow, ← map_pow]
    simp only [root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
    rw [div_self]
    rwa [Ne, map_eq_zero_iff _ (algebraMap K _).injective]))
noncomputable
def autAdjoinRootXPowSubCEquiv [NeZero n] :
    rootsOfUnity n K ≃* (K[n√a] ≃ₐ[K] K[n√a]) where
  __ := autAdjoinRootXPowSubC n a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    letI : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K K[n√a]).injective hζ).injective
    ext
    simp only [AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, ne_eq, MulEquiv.apply_symm_apply,
      rootsOfUnity.val_mkOfPowEq_coe, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe,
      AdjoinRootXPowSubCEquivToRootsOfUnity]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      have : (η : Kˣ) = 1 := (pow_one _).symm.trans η.prop
      simp only [this, Units.val_one, map_one]
    · exact mul_div_cancel_right₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)
  right_inv := by
    intro e
    have := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    apply AlgEquiv.coe_algHom_injective
    apply AdjoinRoot.algHom_ext
    simp only [AdjoinRootXPowSubCEquivToRootsOfUnity, AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, AlgHom.coe_coe, autAdjoinRootXPowSubC_root, Algebra.smul_def]
    rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply, rootsOfUnity.val_mkOfPowEq_coe]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      rw [(pow_one _).symm.trans (root_X_pow_sub_C_pow 1 a), one_mul,
        ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
    · refine div_mul_cancel₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)
lemma autAdjoinRootXPowSubCEquiv_root [NeZero n] (η) :
    autAdjoinRootXPowSubCEquiv hζ H η (root _) = ((η : Kˣ) : K) • root _ :=
  autAdjoinRootXPowSubC_root a η
lemma autAdjoinRootXPowSubCEquiv_symm_smul [NeZero n] (σ) :
    ((autAdjoinRootXPowSubCEquiv hζ H).symm σ : Kˣ) • (root _ : K[n√a]) = σ (root _) := by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    AdjoinRoot.algebraMap_eq, rootsOfUnity.mkOfPowEq, Units.smul_def, Algebra.smul_def,
    rootsOfUnityEquivOfPrimitiveRoots_symm_apply, Units.val_ofPowEqOne, ite_mul, one_mul]
  simp_rw [← root_X_pow_sub_C_eq_zero_iff H]
  split_ifs with h
  · rw [h, map_zero]
  · rw [div_mul_cancel₀ _ h]
end AdjoinRoot
section IsSplittingField
variable {a}
variable {L : Type*} [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]
include hζ in
lemma isSplittingField_AdjoinRoot_X_pow_sub_C :
    haveI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective)
      (root_X_pow_sub_C_pow n a)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    have := ne_zero_of_irreducible_X_pow_sub_C H
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero this) a), aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]
variable {α : L} (hα : α ^ n = algebraMap K L a)
noncomputable
def adjoinRootXPowSubCEquiv (hζ : (primitiveRoots n K).Nonempty) (H : Irreducible (X ^ n - C a))
    (hα : α ^ n = algebraMap K L a) : K[n√a] ≃ₐ[K] L :=
  AlgEquiv.ofBijective (AdjoinRoot.liftHom (X ^ n - C a) α (by simp [hα])) <| by
    haveI := Fact.mk H
    letI := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(liftHom (X ^ n - C a) α _).injective, ?_⟩
    rw [← AlgHom.range_eq_top, ← IsSplittingField.adjoin_rootSet _ (X ^ n - C a),
      eq_comm, adjoin_rootSet_eq_range, IsSplittingField.adjoin_rootSet]
    exact IsSplittingField.splits _ _
lemma adjoinRootXPowSubCEquiv_root :
    adjoinRootXPowSubCEquiv hζ H hα (root _) = α := by
  rw [adjoinRootXPowSubCEquiv, AlgEquiv.coe_ofBijective, liftHom_root]
lemma adjoinRootXPowSubCEquiv_symm_eq_root :
    (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _ := by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply, adjoinRootXPowSubCEquiv_root]
include hζ H hα in
lemma Algebra.adjoin_root_eq_top_of_isSplittingField :
    Algebra.adjoin K {α} = ⊤ := by
  apply Subalgebra.map_injective (B := K[n√a]) (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top, (AlgHom.range_eq_top _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective, AlgHom.map_adjoin,
    Set.image_singleton, AlgHom.coe_coe, adjoinRootXPowSubCEquiv_symm_eq_root, adjoinRoot_eq_top]
include hζ H hα in
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField :
    K⟮α⟯ = ⊤ := by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm
variable (a) (L)
noncomputable
abbrev rootOfSplitsXPowSubC (hn : 0 < n) (a : K)
    (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)] : L :=
  (rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))
lemma rootOfSplitsXPowSubC_pow [NeZero n] :
    (rootOfSplitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a := by
  have := map_rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
  exact this _
variable {a}
noncomputable
def autEquivRootsOfUnity [NeZero n] :
    (L ≃ₐ[K] L) ≃* (rootsOfUnity n K) :=
  (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ H).symm
lemma autEquivRootsOfUnity_apply_rootOfSplit [NeZero n] (σ : L ≃ₐ[K] L) :
    σ (rootOfSplitsXPowSubC (NeZero.pos n) a L) =
      autEquivRootsOfUnity hζ H L σ • (rootOfSplitsXPowSubC (NeZero.pos n) a L) := by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply, autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRootXPowSubCEquiv_symm_eq_root, autAdjoinRootXPowSubCEquiv_root, map_smul,
    adjoinRootXPowSubCEquiv_root]
  rfl
include hα in
lemma autEquivRootsOfUnity_smul [NeZero n] (σ : L ≃ₐ[K] L) :
    autEquivRootsOfUnity hζ H L σ • α = σ α := by
  have ⟨ζ, hζ'⟩ := hζ
  have hn := NeZero.pos n
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn, (hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow a L)] at hα
  simp only [Finset.range_val, Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ := hα
  simp only [map_mul, ← map_pow, ← Algebra.smul_def, map_smul,
    autEquivRootsOfUnity_apply_rootOfSplit hζ H L]
  exact smul_comm _ _ _
noncomputable
def autEquivZmod [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (L ≃ₐ[K] L) ≃* Multiplicative (ZMod n) :=
  haveI hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq
      (hζ.isUnit_unit' hn)).symm).trans (AddEquiv.toMultiplicative'
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm))
include hα in
lemma autEquivZmod_symm_apply_intCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℤ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]
include hα in
lemma autEquivZmod_symm_apply_natCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  simpa only [Int.cast_natCast, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m
include hζ H in
lemma isCyclic_of_isSplittingField_X_pow_sub_C [NeZero n] : IsCyclic (L ≃ₐ[K] L) :=
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective
include hζ H in
lemma isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L :=
  IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)
include hζ H in
lemma finrank_of_isSplittingField_X_pow_sub_C : Module.finrank K L = n := by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_finrank, Fintype.card_congr ((autEquivZmod H L <|
    (mem_primitiveRoots hn).mp hζ.choose_spec).toEquiv.trans Multiplicative.toAdd), ZMod.card]
end IsSplittingField
section IsCyclic
variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
variable (hK : (primitiveRoots (Module.finrank K L) K).Nonempty)
open Module
variable (K L)
include hK in
lemma exists_root_adjoin_eq_top_of_isCyclic [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic (L ≃ₐ[K] L)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  have : IsRoot (minpoly K σ.toLinearMap) ζ := by
    simpa [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hσ',
      sub_eq_zero, IsGalois.card_aut_eq_finrank] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot this).exists_hasEigenvector
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  refine ⟨v, ?_, ?_⟩
  · 
    rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ', hσ'⟩
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hv', smul_pow, ← pow_mul,
      mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · 
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intros σ' hσ'
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    have := hσ' ⟨v, IntermediateField.mem_adjoin_simple_self K v⟩
    simp only [AlgEquiv.smul_def, hv'] at this
    conv_rhs at this => rw [← one_smul K v]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective K hv.2 this)
    rw [pow_mul, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one, one_pow]
    exact one_mem _
variable {K L}
lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    Irreducible (X ^ (finrank K L) - C a) := by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intros q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne_zero)
      rw [degree_X_pow_sub_C finrank_pos,
        degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite K α)),
        ← IntermediateField.adjoin.finrank (IsIntegral.of_finite K α), hα, Nat.cast_le]
      exact (finrank_top K L).ge
  exact this ▸ minpoly.irreducible (IsIntegral.of_finite K α)
include hK in
lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ (finrank K L) - C a) := by
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero finrank_pos a),
      aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, ha, sub_self]
end IsCyclic
open Module in
lemma isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    List.TFAE [
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L),
      ∃ a : K, Irreducible (X ^ (finrank K L) - C a) ∧
        IsSplittingField K L (X ^ (finrank K L) - C a),
      ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤] := by
  have : NeZero (Module.finrank K L) := NeZero.of_pos finrank_pos
  tfae_have 1 → 3
  | ⟨inst₁, inst₂⟩ => exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 → 2
  | ⟨α, ⟨a, ha⟩, hα⟩ => ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK ha.symm hα⟩
  tfae_have 2 → 1
  | ⟨a, H, inst⟩ => ⟨isGalois_of_isSplittingField_X_pow_sub_C hK H L,
      isCyclic_of_isSplittingField_X_pow_sub_C hK H L⟩
  tfae_finish