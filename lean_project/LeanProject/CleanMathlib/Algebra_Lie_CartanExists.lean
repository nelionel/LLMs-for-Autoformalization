import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank
namespace LieAlgebra
section CommRing
variable {K R L M : Type*}
variable [Field K] [CommRing R]
variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite K L]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]
open Module LieSubalgebra Module.Free Polynomial
variable (K)
namespace engel_isBot_of_isMin
variable (R M)
variable (x y : L)
open LieModule LinearMap
local notation "φ" => LieModule.toEnd R L M
private noncomputable
def lieCharpoly : Polynomial R[X] :=
  letI bL := chooseBasis R L
  (polyCharpoly (LieHom.toLinearMap φ) bL).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)
lemma lieCharpoly_monic : (lieCharpoly R M x y).Monic :=
  (polyCharpoly_monic _ _).map _
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly R M x y).natDegree = finrank R M := by
  rw [lieCharpoly, (polyCharpoly_monic _ _).natDegree_map, polyCharpoly_natDegree]
variable {R} in
lemma lieCharpoly_map_eval (r : R) :
    (lieCharpoly R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly, map_map]
  set b := chooseBasis R L
  have aux : (fun i ↦ (b.repr y) i * r + (b.repr x) i) = b.repr (r • y + x) := by
    ext i; simp [mul_comm r]
  simp_rw [← coe_aeval_eq_evalRingHom, ← AlgHom.comp_toRingHom, MvPolynomial.comp_aeval,
    map_add, map_mul, aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, aeval_X, aux,
    MvPolynomial.coe_aeval_eq_eval, polyCharpoly_map_eq_charpoly, LieHom.coe_toLinearMap]
lemma lieCharpoly_coeff_natDegree [Nontrivial R] (i j : ℕ) (hij : i + j = finrank R M) :
    ((lieCharpoly R M x y).coeff i).natDegree ≤ j := by
  classical
  rw [← mul_one j, lieCharpoly, coeff_map]
  apply MvPolynomial.aeval_natDegree_le
  · apply (polyCharpoly_coeff_isHomogeneous φ (chooseBasis R L) _ _ hij).totalDegree_le
  intro k
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    simp only [natDegree_X, le_rfl]
  · simp only [natDegree_C, zero_le]
end engel_isBot_of_isMin
end CommRing
section Field
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
open Module LieSubalgebra LieSubmodule Polynomial Cardinal LieModule engel_isBot_of_isMin
#adaptation_note 
set_option linter.unusedVariables false in
lemma engel_isBot_of_isMin (hLK : finrank K L ≤ #K) (U : LieSubalgebra K L)
    (E : {engel K x | x ∈ U}) (hUle : U ≤ E) (hmin : IsMin E) :
    IsBot E := by
  rcases E with ⟨_, x, hxU, rfl⟩
  rintro ⟨_, y, hyU, rfl⟩
  set Ex : {engel K x | x ∈ U} := ⟨engel K x, x, hxU, rfl⟩
  set Ey : {engel K y | y ∈ U} := ⟨engel K y, y, hyU, rfl⟩
  replace hUle : U ≤ Ex := hUle
  replace hmin : ∀ E, E ≤ Ex → Ex ≤ E := @hmin
  let E : LieSubmodule K U L :=
  { engel K x with
    lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUle hu) hy }
  obtain rfl|hx₀ := eq_or_ne x 0
  · simpa [Ex, Ey] using hmin Ey
  let Q := L ⧸ E
  let r := finrank K E
  obtain hr|hr : r = finrank K L ∨ r < finrank K L := (Submodule.finrank_le _).eq_or_lt
  · suffices engel K y ≤ engel K x from hmin Ey this
    suffices engel K x = ⊤ by simp_rw [this, le_top]
    apply LieSubalgebra.to_submodule_injective
    apply Submodule.eq_top_of_finrank_eq hr
  set x' : U := ⟨x, hxU⟩
  set y' : U := ⟨y, hyU⟩
  let u : U := y' - x'
  let χ : Polynomial (K[X]) := lieCharpoly K E x' u
  let ψ : Polynomial (K[X]) := lieCharpoly K Q x' u
  suffices χ = X ^ r by
    apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    simp_rw [Polynomial.map_pow, map_X, χ, lieCharpoly_map_eval, one_smul, u, sub_add_cancel,
      r, LinearMap.charpoly_eq_X_pow_iff,
      Subtype.ext_iff, coe_toEnd_pow _ _ _ E, ZeroMemClass.coe_zero] at this
    intro z hz
    rw [mem_engel_iff]
    exact this ⟨z, hz⟩
  suffices ∀ i < r, χ.coeff i = 0 by
    simp_rw [r, ← lieCharpoly_natDegree K E x' u] at this ⊢
    rw [(lieCharpoly_monic K E x' u).eq_X_pow_iff_natDegree_le_natTrailingDegree]
    exact le_natTrailingDegree (lieCharpoly_monic K E x' u).ne_zero this
  intro i hi
  obtain rfl|hi0 := eq_or_ne i 0
  · 
    apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    case deg =>
      apply lt_of_lt_of_le _ hLK
      rw [Nat.cast_lt]
      apply lt_of_le_of_lt _ hr
      apply lieCharpoly_coeff_natDegree _ _ _ _ 0 r (zero_add r)
    intro α
    rw [← coe_evalRingHom, ← coeff_map, lieCharpoly_map_eval,
      ← constantCoeff_apply, LinearMap.charpoly_constantCoeff_eq_zero_iff]
    let z := α • u + x'
    obtain hz₀|hz₀ := eq_or_ne z 0
    · 
      refine ⟨⟨x, self_mem_engel K x⟩, ?_, ?_⟩
      · exact Subtype.coe_ne_coe.mp hx₀
      · dsimp only [z] at hz₀
        simp only [coe_bracket_of_module, hz₀, LieHom.map_zero, LinearMap.zero_apply]
    refine ⟨⟨z, hUle z.2⟩, ?_, ?_⟩
    · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero, Subtype.ext_iff] using hz₀
    · show ⁅z, _⁆ = (0 : E)
      ext
      exact lie_self z.1
  have hψ : constantCoeff ψ ≠ 0 := by
    intro H
    obtain ⟨z, hz0, hxz⟩ : ∃ z : Q, z ≠ 0 ∧ ⁅x', z⁆ = 0 := by
      apply_fun (evalRingHom 0) at H
      rw [constantCoeff_apply, ← coeff_map, lieCharpoly_map_eval,
        ← constantCoeff_apply, map_zero, LinearMap.charpoly_constantCoeff_eq_zero_iff] at H
      simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add, toEnd_apply_apply]
        using H
    apply hz0
    obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    have : ⁅x, z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    simp only [coe_bracket_of_module, LieSubmodule.mem_mk_iff', mem_coe_submodule, mem_engel_iff,
      LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero', E, Q] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n+1
    rwa [pow_succ]
  obtain ⟨s, hs, hsψ⟩ : ∃ s : Finset K, r ≤ s.card ∧ ∀ α ∈ s, (constantCoeff ψ).eval α ≠ 0 := by
    classical
    let t := (constantCoeff ψ).roots.toFinset
    have ht : t.card ≤ finrank K L - r := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (card_roots' _).trans ?_
      rw [constantCoeff_apply]
      apply lieCharpoly_coeff_natDegree
      suffices finrank K Q + r = finrank K L by rw [← this, zero_add, Nat.add_sub_cancel]
      apply Submodule.finrank_quotient_add_finrank
    obtain ⟨s, hs⟩ := exists_finset_le_card K _ hLK
    use s \ t
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (Finset.le_card_sdiff _ _)
      omega
    · intro α hα
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset, mem_roots', IsRoot.def, not_and, t] at hα
      exact hα.2 hψ
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s _ ?hcard
  case hcard =>
    apply lt_of_le_of_lt (lieCharpoly_coeff_natDegree _ _ _ _ i (r - i) _)
    · omega
    · dsimp only [r] at hi ⊢
      rw [Nat.add_sub_cancel' hi.le]
  intro α hα
  rw [← coe_evalRingHom, ← coeff_map, lieCharpoly_map_eval,
    (LinearMap.charpoly_eq_X_pow_iff _).mpr, coeff_X_pow, if_neg hi.ne]
  let v := α • u + x'
  suffices engel K (v : L) ≤ engel K x by
    replace this : engel K x ≤ engel K (v : L) := (hmin ⟨_, v, v.2, rfl⟩ this).ge
    intro z
    simpa only [mem_engel_iff, Subtype.ext_iff, coe_toEnd_pow _ _ _ E] using this z.2
  intro z hz
  show z ∈ E
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  set z' : Q := LieSubmodule.Quotient.mk' E z
  have hz' : ∃ n : ℕ, (toEnd K U Q v ^ n) z' = 0 := by
    rw [mem_engel_iff] at hz
    obtain ⟨n, hn⟩ := hz
    use n
    apply_fun LieSubmodule.Quotient.mk' E at hn
    rw [LieModuleHom.map_zero] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => simp only [pow_zero, LinearMap.one_apply]
    | succ n ih => rw [pow_succ', pow_succ', LinearMap.mul_apply, ih]; rfl
  classical
  set n := Nat.find hz' with _hn
  have hn : (toEnd K U Q v ^ n) z' = 0 := Nat.find_spec hz'
  obtain hn₀|⟨k, hk⟩ : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp
  · simpa only [hn₀, pow_zero, LinearMap.one_apply] using hn
  specialize hsψ α hα
  rw [← coe_evalRingHom, constantCoeff_apply, ← coeff_map, lieCharpoly_map_eval,
    ← constantCoeff_apply, ne_eq, LinearMap.charpoly_constantCoeff_eq_zero_iff] at hsψ
  contrapose! hsψ
  use (toEnd K U Q v ^ k) z'
  refine ⟨?_, ?_⟩
  · 
    apply Nat.find_min hz'; omega
  · rw [← hn, hk, pow_succ', LinearMap.mul_apply]
variable (K L)
lemma exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L ≤ #K) :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  obtain ⟨x, hx⟩ := exists_isRegular_of_finrank_le_card K L h
  use x
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {engel K z | z ∈ engel K x} := ⟨engel K x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨engel K y, y, hy, rfl⟩
  apply engel_isBot_of_isMin h (engel K x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices finrank K (engel K x) ≤ finrank K (engel K y) by
    suffices engel K y = engel K x from this.ge
    apply LieSubalgebra.to_submodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply rank_le_finrank_engel
lemma exists_isCartanSubalgebra_engel [Infinite K] :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  apply exists_isCartanSubalgebra_engel_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite K›
end Field
end LieAlgebra