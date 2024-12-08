import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
noncomputable section
open Module Polynomial IntermediateField
namespace Field
section PrimitiveElementFinite
variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]
@[stacks 09HY "second part"]
theorem exists_primitive_element_of_finite_top [Finite E] : ∃ α : E, F⟮α⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator Eˣ _ _
  use α
  rw [eq_top_iff]
  rintro x -
  by_cases hx : x = 0
  · rw [hx]
    exact F⟮α.val⟯.zero_mem
  · obtain ⟨n, hn⟩ := Set.mem_range.mp (hα (Units.mk0 x hx))
    rw [show x = α ^ n by norm_cast; rw [hn, Units.val_mk0]]
    exact zpow_mem (mem_adjoin_simple_self F (E := E) ↑α) n
theorem exists_primitive_element_of_finite_bot [Finite F] [FiniteDimensional F E] :
    ∃ α : E, F⟮α⟯ = ⊤ :=
  haveI : Finite E := Module.finite_of_finite F
  exists_primitive_element_of_finite_top F E
end PrimitiveElementFinite
section PrimitiveElementInf
variable {F : Type*} [Field F] [Infinite F] {E : Type*} [Field E] (ϕ : F →+* E) (α β : E)
theorem primitive_element_inf_aux_exists_c (f g : F[X]) :
    ∃ c : F, ∀ α' ∈ (f.map ϕ).roots, ∀ β' ∈ (g.map ϕ).roots, -(α' - α) / (β' - β) ≠ ϕ c := by
  classical
  let sf := (f.map ϕ).roots
  let sg := (g.map ϕ).roots
  classical
  let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ϕ fun x _ y _ h => ϕ.injective h
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset s'
  simp_rw [s', s, Finset.mem_preimage, Multiset.mem_toFinset, Multiset.mem_bind, Multiset.mem_map]
    at hc
  push_neg at hc
  exact ⟨c, hc⟩
variable (F)
variable [Algebra F E]
theorem primitive_element_inf_aux [Algebra.IsSeparable F E] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  classical
  have hα := Algebra.IsSeparable.isIntegral F α
  have hβ := Algebra.IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯ by
    use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel_right α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      rw [map_div₀, RingHom.map_neg, ← coeff_map, ← coeff_map, p_linear]
      simp [mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero),
        -map_add]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (Algebra.IsSeparable.isSeparable F β).map
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ← aeval_def, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map, ← aeval_def, minpoly.aeval]
  have h_splits : Splits ιEE' h :=
    splits_of_splits_gcd_right ιEE' map_g_ne_zero (SplittingField.splits _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, Algebra.smul_def, RingHom.map_add, RingHom.map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, map_add, Polynomial.map_mul, map_X]
    congr
private theorem primitive_element_inf_aux_of_finite_intermediateField
    [Finite (IntermediateField F E)] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  let f : F → IntermediateField F E := fun x ↦ F⟮α + x • β⟯
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  use α + x • β
  apply le_antisymm
  · rw [adjoin_le_iff]
    have αxβ_in_K : α + x • β ∈ F⟮α + x • β⟯ := mem_adjoin_simple_self F _
    have αyβ_in_K : α + y • β ∈ F⟮α + y • β⟯ := mem_adjoin_simple_self F _
    dsimp [f] at *
    simp only [← heq] at αyβ_in_K
    have β_in_K := sub_mem αxβ_in_K αyβ_in_K
    rw [show (α + x • β) - (α + y • β) = (x - y) • β by rw [sub_smul]; abel1] at β_in_K
    replace β_in_K := smul_mem _ β_in_K (x := (x - y)⁻¹)
    rw [smul_smul, inv_mul_eq_div, div_self (sub_ne_zero.2 hneq), one_smul] at β_in_K
    have α_in_K : α ∈ F⟮α + x • β⟯ := by
      convert ← sub_mem αxβ_in_K (smul_mem _ β_in_K)
      apply add_sub_cancel_right
    rintro x (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
    have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
    exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
end PrimitiveElementInf
variable (F E : Type*) [Field F] [Field E]
variable [Algebra F E]
section SeparableAssumption
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]
@[stacks 030N "The moreover part"]
theorem exists_primitive_element : ∃ α : E, F⟮α⟯ = ⊤ := by
  rcases isEmpty_or_nonempty (Fintype F) with (F_inf | ⟨⟨F_finite⟩⟩)
  · let P : IntermediateField F E → Prop := fun K => ∃ α : E, F⟮α⟯ = K
    have base : P ⊥ := ⟨0, adjoin_zero⟩
    have ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F) := by
      intro K β hK
      cases' hK with α hK
      rw [← hK, adjoin_simple_adjoin_simple]
      haveI : Infinite F := isEmpty_fintype.mp F_inf
      cases' primitive_element_inf_aux F α β with γ hγ
      exact ⟨γ, hγ.symm⟩
    exact induction_on_adjoin P base ih ⊤
  · exact exists_primitive_element_of_finite_bot F E
noncomputable def powerBasisOfFiniteOfSeparable : PowerBasis F E :=
  let α := (exists_primitive_element F E).choose
  let pb := adjoin.powerBasis (Algebra.IsSeparable.isIntegral F α)
  have e : F⟮α⟯ = ⊤ := (exists_primitive_element F E).choose_spec
  pb.map ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)
end SeparableAssumption
section FiniteIntermediateField
theorem isAlgebraic_of_adjoin_eq_adjoin {α : E} {m n : ℕ} (hneq : m ≠ n)
    (heq : F⟮α ^ m⟯ = F⟮α ^ n⟯) : IsAlgebraic F α := by
  wlog hmn : m < n
  · exact this F E hneq.symm heq.symm (hneq.lt_or_lt.resolve_left hmn)
  by_cases hm : m = 0
  · rw [hm] at heq hmn
    simp only [pow_zero, adjoin_one] at heq
    obtain ⟨y, h⟩ := mem_bot.1 (heq.symm ▸ mem_adjoin_simple_self F (α ^ n))
    refine ⟨X ^ n - C y, X_pow_sub_C_ne_zero hmn y, ?_⟩
    simp only [map_sub, map_pow, aeval_X, aeval_C, h, sub_self]
  obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff F _).1 (heq ▸ mem_adjoin_simple_self F (α ^ m))
  by_cases hzero : aeval (α ^ n) s = 0
  · simp only [hzero, div_zero, pow_eq_zero_iff hm] at h
    exact h.symm ▸ isAlgebraic_zero
  replace hm : 0 < m := Nat.pos_of_ne_zero hm
  rw [eq_div_iff hzero, ← sub_eq_zero] at h
  replace hzero : s ≠ 0 := by rintro rfl; simp only [map_zero, not_true_eq_false] at hzero
  let f : F[X] := X ^ m * expand F n s - expand F n r
  refine ⟨f, ?_, ?_⟩
  · have : f.coeff (n * s.natDegree + m) ≠ 0 := by
      have hn : 0 < n := by linarith only [hm, hmn]
      have hndvd : ¬ n ∣ n * s.natDegree + m := by
        rw [← Nat.dvd_add_iff_right (n.dvd_mul_right s.natDegree)]
        exact Nat.not_dvd_of_pos_of_lt hm hmn
      simp only [f, coeff_sub, coeff_X_pow_mul, s.coeff_expand_mul' hn, coeff_natDegree,
        coeff_expand hn r, hndvd, ite_false, sub_zero]
      exact leadingCoeff_ne_zero.2 hzero
    intro h
    simp only [h, coeff_zero, ne_eq, not_true_eq_false] at this
  · simp only [f, map_sub, map_mul, map_pow, aeval_X, expand_aeval, h]
theorem isAlgebraic_of_finite_intermediateField
    [Finite (IntermediateField F E)] : Algebra.IsAlgebraic F E := ⟨fun α ↦
  have ⟨_m, _n, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun n ↦ F⟮α ^ n⟯
  isAlgebraic_of_adjoin_eq_adjoin F E hneq heq⟩
theorem FiniteDimensional.of_finite_intermediateField
    [Finite (IntermediateField F E)] : FiniteDimensional F E := by
  let IF := { K : IntermediateField F E // ∃ x, K = F⟮x⟯ }
  have := isAlgebraic_of_finite_intermediateField F E
  haveI : ∀ K : IF, FiniteDimensional F K.1 := fun ⟨_, x, rfl⟩ ↦ adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral _)
  have hfin := finiteDimensional_iSup_of_finite (t := fun K : IF ↦ K.1)
  have htop : ⨆ K : IF, K.1 = ⊤ := le_top.antisymm fun x _ ↦
    le_iSup (fun K : IF ↦ K.1) ⟨F⟮x⟯, x, rfl⟩ <| mem_adjoin_simple_self F x
  rw [htop] at hfin
  exact topEquiv.toLinearEquiv.finiteDimensional
@[deprecated (since := "2024-02-02")]
alias finiteDimensional_of_finite_intermediateField := FiniteDimensional.of_finite_intermediateField
theorem exists_primitive_element_of_finite_intermediateField
    [Finite (IntermediateField F E)] (K : IntermediateField F E) : ∃ α : E, F⟮α⟯ = K := by
  haveI := FiniteDimensional.of_finite_intermediateField F E
  rcases finite_or_infinite F with (_ | _)
  · obtain ⟨α, h⟩ := exists_primitive_element_of_finite_bot F K
    exact ⟨α, by simpa only [lift_adjoin_simple, lift_top] using congr_arg lift h⟩
  · apply induction_on_adjoin (fun K ↦ ∃ α : E, F⟮α⟯ = K) ⟨0, adjoin_zero⟩
    rintro K β ⟨α, rfl⟩
    simp_rw [adjoin_simple_adjoin_simple, eq_comm]
    exact primitive_element_inf_aux_of_finite_intermediateField F α β
theorem FiniteDimensional.of_exists_primitive_element [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) : FiniteDimensional F E := by
  obtain ⟨α, hprim⟩ := h
  have hfin := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) α)
  rw [hprim] at hfin
  exact topEquiv.toLinearEquiv.finiteDimensional
@[deprecated (since := "2024-02-02")]
alias finiteDimensional_of_exists_primitive_element := FiniteDimensional.of_exists_primitive_element
theorem finite_intermediateField_of_exists_primitive_element [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) : Finite (IntermediateField F E) := by
  haveI := FiniteDimensional.of_exists_primitive_element F E h
  obtain ⟨α, hprim⟩ := h
  let f : F[X] := minpoly F α
  let G := { g : E[X] // g.Monic ∧ g ∣ f.map (algebraMap F E) }
  have hfin : Finite G := @Finite.of_fintype _ <| fintypeSubtypeMonicDvd
    (f.map (algebraMap F E)) <| map_ne_zero (minpoly.ne_zero_of_finite F α)
  let g : IntermediateField F E → G := fun K ↦
    ⟨(minpoly K α).map (algebraMap K E), (minpoly.monic <| .of_finite K α).map _, by
      convert Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]; rfl⟩
  have hinj : Function.Injective g := fun K K' heq ↦ by
    rw [Subtype.mk.injEq] at heq
    apply_fun fun f : E[X] ↦ adjoin F (f.coeffs : Set E) at heq
    simpa only [adjoin_minpoly_coeff_of_exists_primitive_element F hprim] using heq
  exact Finite.of_injective g hinj
@[stacks 030N "Equivalence of (1) & (2)"]
theorem exists_primitive_element_iff_finite_intermediateField :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, F⟮α⟯ = ⊤) ↔ Finite (IntermediateField F E) :=
  ⟨fun ⟨_, h⟩ ↦ finite_intermediateField_of_exists_primitive_element F E h,
    fun _ ↦ ⟨isAlgebraic_of_finite_intermediateField F E,
      exists_primitive_element_of_finite_intermediateField F E _⟩⟩
end FiniteIntermediateField
end Field
variable (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
@[simp]
theorem AlgHom.card_of_splits (L : Type*) [Field L] [Algebra F L]
    (hL : ∀ x : E, (minpoly F x).Splits (algebraMap F L)) :
    Fintype.card (E →ₐ[F] L) = finrank F E := by
  convert (AlgHom.card_of_powerBasis (L := L) (Field.powerBasisOfFiniteOfSeparable F E)
    (Algebra.IsSeparable.isSeparable _ _) <| hL _).trans
      (PowerBasis.finrank _).symm
@[simp]
theorem AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = finrank F E :=
  AlgHom.card_of_splits _ _ _ (fun _ ↦ IsAlgClosed.splits_codomain _)
section iff
namespace Field
open Module IntermediateField Polynomial Algebra Set
variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
theorem primitive_element_iff_minpoly_natDegree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E := by
  rw [← adjoin.finrank (IsIntegral.of_finite F α), ← finrank_top F E]
  refine ⟨fun h => ?_, fun h => eq_of_le_of_finrank_eq le_top h⟩
  exact congr_arg (fun K : IntermediateField F E => finrank F K) h
theorem primitive_element_iff_minpoly_degree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).degree = finrank F E := by
  rw [degree_eq_iff_natDegree_eq, primitive_element_iff_minpoly_natDegree_eq]
  exact minpoly.ne_zero_of_finite F α
variable [Algebra.IsSeparable F E] (A : Type*) [Field A] [Algebra F A]
  (hA : ∀ x : E, (minpoly F x).Splits (algebraMap F A))
include hA
theorem primitive_element_iff_algHom_eq_of_eval' (α : E) :
    F⟮α⟯ = ⊤ ↔ Function.Injective fun φ : E →ₐ[F] A ↦ φ α := by
  classical
  simp_rw [primitive_element_iff_minpoly_natDegree_eq, ← card_rootSet_eq_natDegree (K := A)
    (Algebra.IsSeparable.isSeparable F α) (hA _), ← toFinset_card,
    ← (Algebra.IsAlgebraic.of_finite F E).range_eval_eq_rootSet_minpoly_of_splits _ hA α,
    ← AlgHom.card_of_splits F E A hA, Fintype.card, toFinset_range, Finset.card_image_iff,
    Finset.coe_univ, ← injective_iff_injOn_univ]
theorem primitive_element_iff_algHom_eq_of_eval (α : E)
    (φ : E →ₐ[F] A) : F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ α = ψ α → φ = ψ := by
  refine ⟨fun h ψ hψ ↦ (Field.primitive_element_iff_algHom_eq_of_eval' F A hA α).mp h hψ,
    fun h ↦ eq_of_le_of_finrank_eq' le_top ?_⟩
  letI : Algebra F⟮α⟯ A := (φ.comp F⟮α⟯.val).toAlgebra
  haveI := Algebra.isSeparable_tower_top_of_isSeparable F F⟮α⟯ E
  rw [IntermediateField.finrank_top, ← AlgHom.card_of_splits _ _ A, Fintype.card_eq_one_iff]
  · exact ⟨{ __ := φ, commutes' := fun _ ↦ rfl }, fun ψ ↦ AlgHom.restrictScalars_injective F <|
      Eq.symm <| h _ (ψ.commutes <| AdjoinSimple.gen F α).symm⟩
  · exact fun x ↦ (IsIntegral.of_finite F x).minpoly_splits_tower_top (hA x)
end Field
end iff