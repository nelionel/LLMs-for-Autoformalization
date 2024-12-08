import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.PID
variable {ι R M : Type*} {n : ℕ} [CommRing R] [AddCommGroup M]
namespace Basis.SmithNormalForm
variable [Fintype ι]
lemma toAddSubgroup_index_eq_pow_mul_prod [Module R M] {N : Submodule R M}
    (snf : Basis.SmithNormalForm N ι n) :
    N.toAddSubgroup.index = Nat.card R ^ (Fintype.card ι - n) *
      ∏ i : Fin n, (Ideal.span {snf.a i}).toAddSubgroup.index := by
  classical
  rcases snf with ⟨bM, bN, f, a, snf⟩
  dsimp only
  set N' : Submodule R (ι → R) := N.map bM.equivFun with hN'
  let bN' : Basis (Fin n) R N' := bN.map (bM.equivFun.submoduleMap N)
  have snf' : ∀ i, (bN' i : ι → R) = Pi.single (f i) (a i) := by
    intro i
    simp only [map_apply, bN']
    erw [LinearEquiv.submoduleMap_apply]
    simp only [equivFun_apply, snf, map_smul, repr_self, Finsupp.single_eq_pi_single]
    ext j
    simp [Pi.single_apply]
  have hNN' : N.toAddSubgroup.index = N'.toAddSubgroup.index := by
    set e : (ι → R) ≃+ M := ↑bM.equivFun.symm with he
    let e' : (ι → R) →+ M := e
    have he' : Function.Surjective e' := e.surjective
    convert (AddSubgroup.index_comap_of_surjective N.toAddSubgroup he').symm using 2
    rw [AddSubgroup.comap_equiv_eq_map_symm, he, hN', LinearEquiv.coe_toAddEquiv_symm,
    AddEquiv.symm_symm]
    exact Submodule.map_toAddSubgroup ..
  rw [hNN']
  have hN' : N'.toAddSubgroup = AddSubgroup.pi Set.univ
      (fun i ↦ (Ideal.span {if h : ∃ j, f j = i then a h.choose else 0}).toAddSubgroup) := by
    ext g
    simp only [Submodule.mem_toAddSubgroup, bN'.mem_submodule_iff', snf', AddSubgroup.mem_pi,
      Set.mem_univ, true_implies, Ideal.mem_span_singleton]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with ⟨c, rfl⟩
      intro i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs with h
      · convert dvd_mul_left (a h.choose) (c h.choose)
        calc ∑ x : Fin n, _ = c h.choose * if i = f h.choose then a h.choose else 0 := by
              refine Finset.sum_eq_single h.choose ?_ (by simp)
              rintro j - hj
              have hinj := f.injective.ne hj
              rw [h.choose_spec] at hinj
              simp [hinj.symm]
          _ = c h.choose * a h.choose := by simp [h.choose_spec]
      · convert dvd_refl (0 : R)
        convert Finset.sum_const_zero with j
        rw [not_exists] at h
        specialize h j
        rw [eq_comm] at h
        simp [h]
    · refine ⟨fun j ↦ (h (f j)).choose, ?_⟩
      ext i
      simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq,
        Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
      rw [eq_comm]
      by_cases hj : ∃ j, f j = i
      · calc ∑ x : Fin n, _ =
            if i = f hj.choose then (h (f hj.choose)).choose * a hj.choose else 0 := by
              convert Finset.sum_eq_single (β := R) hj.choose ?_ ?_
              · simp [hj]
              · rintro j - h
                have hinj := f.injective.ne h
                rw [hj.choose_spec] at hinj
                simp [hinj.symm]
              · simp
          _ = g i := by
              simp only [hj.choose_spec, ↓reduceIte]
              rw [mul_comm]
              conv_rhs =>
                rw [← hj.choose_spec, (h (f hj.choose)).choose_spec]
              simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq, ↓reduceDIte, Classical.choose_eq]
              congr!
              · exact hj.choose_spec.symm
              · simp [hj]
      · convert Finset.sum_const_zero with x
        · rw [not_exists] at hj
          specialize hj x
          rw [eq_comm] at hj
          simp [hj]
        · rw [← zero_dvd_iff]
          convert h i
          simp [hj]
  simp only [hN', AddSubgroup.index_pi, apply_dite, Finset.prod_dite, Set.singleton_zero,
    Ideal.span_zero, Submodule.bot_toAddSubgroup, AddSubgroup.index_pi, AddSubgroup.index_bot,
    Finset.prod_const, Finset.univ_eq_attach, Finset.card_attach]
  rw [mul_comm]
  congr
  · convert Finset.card_compl {x | ∃ j, f j = x} using 2
    · exact (Finset.compl_filter _).symm
    · convert (Finset.card_image_of_injective Finset.univ f.injective).symm <;> simp
  · rw [Finset.attach_eq_univ]
    let f' : Fin n → { x // x ∈ Finset.filter (fun x ↦ ∃ j, f j = x) Finset.univ } :=
      fun i ↦ ⟨f i, by simp⟩
    have hf' : Function.Injective f' := fun i j hij ↦ by
      rw [Subtype.ext_iff] at hij
      exact f.injective hij
    let f'' : Fin n ↪ { x // x ∈ Finset.filter (fun x ↦ ∃ j, f j = x) Finset.univ } :=
      ⟨f', hf'⟩
    have hu : (Finset.univ : Finset { x // x ∈ Finset.filter (fun x ↦ ∃ j, f j = x) Finset.univ }) =
      Finset.univ.map f'' := by
      ext x
      simp only [Finset.univ_eq_attach, Finset.mem_attach, Finset.mem_map, Finset.mem_univ,
        true_and, true_iff]
      have hx := x.property
      simp only [Finset.univ_filter_exists, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [Subtype.ext_iff]
      exact hi
    rw [hu, Finset.prod_map]
    congr! with i
    rw [← f.injective.eq_iff]
    generalize_proofs h
    rw [h.choose_spec]
    rfl
lemma toAddSubgroup_index_eq_ite [Infinite R] [Module R M] {N : Submodule R M}
    (snf : Basis.SmithNormalForm N ι n) : N.toAddSubgroup.index = (if n = Fintype.card ι then
      ∏ i : Fin n, (Ideal.span {snf.a i}).toAddSubgroup.index else 0) := by
  rw [snf.toAddSubgroup_index_eq_pow_mul_prod]
  split_ifs with h
  · simp [h]
  · have hlt : n < Fintype.card ι :=
      Ne.lt_of_le h (by simpa using Fintype.card_le_of_embedding snf.f)
    simp [hlt]
lemma toAddSubgroup_index_ne_zero_iff {N : Submodule ℤ M} (snf : Basis.SmithNormalForm N ι n) :
    N.toAddSubgroup.index ≠ 0 ↔ n = Fintype.card ι := by
  rw [snf.toAddSubgroup_index_eq_ite]
  rcases snf with ⟨bM, bN, f, a, snf⟩
  simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, and_iff_left_iff_imp]
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    apply Basis.ne_zero bN i
    specialize snf i
    simpa [hi] using snf
  intro h
  simpa [Ideal.span_singleton_toAddSubgroup_eq_zmultiples, Int.index_zmultiples,
    Finset.prod_eq_zero_iff] using ha
end Basis.SmithNormalForm
namespace Int
variable [Finite ι]
lemma submodule_toAddSubgroup_index_ne_zero_iff {N : Submodule ℤ (ι → ℤ)} :
    N.toAddSubgroup.index ≠ 0 ↔ Nonempty (N ≃ₗ[ℤ] (ι → ℤ)) := by
  obtain ⟨n, snf⟩ := N.smithNormalForm <| Basis.ofEquivFun <| LinearEquiv.refl _ _
  have := Fintype.ofFinite ι
  rw [snf.toAddSubgroup_index_ne_zero_iff]
  rcases snf with ⟨-, bN, -, -, -⟩
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · subst h
    exact ⟨(bN.reindex (Fintype.equivFin _).symm).equivFun⟩
  · have hc := card_eq_of_linearEquiv ℤ <| bN.equivFun.symm.trans e
    simpa using hc
lemma addSubgroup_index_ne_zero_iff {H : AddSubgroup (ι → ℤ)} :
    H.index ≠ 0 ↔ Nonempty (H ≃+ (ι → ℤ)) := by
  convert submodule_toAddSubgroup_index_ne_zero_iff (N := AddSubgroup.toIntSubmodule H) using 1
  exact ⟨fun ⟨e⟩ ↦ ⟨e.toIntLinearEquiv⟩, fun ⟨e⟩ ↦ ⟨e.toAddEquiv⟩⟩
lemma subgroup_index_ne_zero_iff {H : Subgroup (ι → Multiplicative ℤ)} :
    H.index ≠ 0 ↔ Nonempty (H ≃* (ι → Multiplicative ℤ)) := by
  let em : Multiplicative (ι → ℤ) ≃* (ι → Multiplicative ℤ) :=
    MulEquiv.funMultiplicative _ _
  let H' : Subgroup (Multiplicative (ι → ℤ)) := H.comap em
  let eH' : H' ≃* H := (MulEquiv.subgroupCongr <| Subgroup.comap_equiv_eq_map_symm em H).trans
    (MulEquiv.subgroupMap em.symm _).symm
  have h : H'.index = H.index := Subgroup.index_comap_of_surjective _ em.surjective
  rw [← h, ← Subgroup.index_toAddSubgroup, addSubgroup_index_ne_zero_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨(eH'.symm.trans (AddEquiv.toMultiplicative e)).trans em⟩,
    fun ⟨e⟩ ↦ ⟨(MulEquiv.toAdditive ((eH'.trans e).trans em.symm)).trans
      (AddEquiv.additiveMultiplicative _)⟩⟩
end Int