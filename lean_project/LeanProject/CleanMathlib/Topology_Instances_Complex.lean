import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.FieldTheory.IntermediateField.Basic
section ComplexSubfield
open Complex Set
open ComplexConjugate
theorem Complex.subfield_eq_of_closed {K : Subfield ℂ} (hc : IsClosed (K : Set ℂ)) :
    K = ofRealHom.fieldRange ∨ K = ⊤ := by
  suffices range (ofReal : ℝ → ℂ) ⊆ K by
    rw [range_subset_iff, ← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_set_eq, IntermediateField.coe_toSubalgebra] at this ⊢
    exact this
  suffices range (ofReal : ℝ → ℂ) ⊆ closure (Set.range ((ofReal : ℝ → ℂ) ∘ ((↑) : ℚ → ℝ))) by
    refine subset_trans this ?_
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, ofReal_ratCast, SetLike.mem_coe, SubfieldClass.ratCast_mem]
  nth_rw 1 [range_comp]
  refine subset_trans ?_ (image_closure_subset_closure_image continuous_ofReal)
  rw [DenseRange.closure_range Rat.isDenseEmbedding_coe_real.dense]
  simp only [image_univ]
  rfl
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield ℂ) {ψ : K →+* ℂ}
    (hc : UniformContinuous ψ) : ψ.toFun = K.subtype ∨ ψ.toFun = conj ∘ K.subtype := by
  letI : TopologicalDivisionRing ℂ := TopologicalDivisionRing.mk
  letI : TopologicalRing K.topologicalClosure :=
    Subring.instTopologicalRing K.topologicalClosure.toSubring
  set ι : K → K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  have ui : IsUniformInducing ι :=
    ⟨by
      rw [uniformity_subtype, uniformity_subtype, Filter.comap_comap]
      congr ⟩
  let di := ui.isDenseInducing (?_ : DenseRange ι)
  · 
    let extψ := IsDenseInducing.extendRingHom ui di.dense hc
    haveI hψ := (uniformContinuous_uniformly_extend ui di.dense hc).continuous
    cases' Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K) with h h
    · left
      let j := RingEquiv.subfieldCongr h
      let ψ₁ := RingHom.comp extψ (RingHom.comp j.symm.toRingHom ofRealHom.rangeRestrict)
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using hψ.comp ((continuous_algebraMap ℝ ℂ).subtype_mk _)
      ext1 x
      rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ofRealHom.rangeRestrict r = j (ι x)
      · have :=
          RingHom.congr_fun (ringHom_eq_ofReal_of_continuous hψ₁) r
        erw [RingHom.comp_apply, RingHom.comp_apply, hr, RingEquiv.toRingHom_eq_coe] at this
        convert this using 1
        · exact (IsDenseInducing.extend_eq di hc.continuous _).symm
        · rw [← ofRealHom.coe_rangeRestrict, hr]
          rfl
      obtain ⟨r, hr⟩ := SetLike.coe_mem (j (ι x))
      exact ⟨r, Subtype.ext hr⟩
    · 
      let ψ₁ :=
        RingHom.comp extψ
          (RingHom.comp (RingEquiv.subfieldCongr h).symm.toRingHom
            (@Subfield.topEquiv ℂ _).symm.toRingHom)
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using hψ.comp (continuous_id.subtype_mk _)
      cases' ringHom_eq_id_or_conj_of_continuous hψ₁ with h h
      · left
        ext1 z
        convert RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
      · right
        ext1 z
        convert RingHom.congr_fun h z using 1
        exact (IsDenseInducing.extend_eq di hc.continuous z).symm
  · let j : { x // x ∈ closure (id '' { x | (K : Set ℂ) x }) } → (K.topologicalClosure : Set ℂ) :=
      fun x =>
      ⟨x, by
        convert x.prop
        simp only [id, Set.image_id']
        rfl ⟩
    convert DenseRange.comp (Function.Surjective.denseRange _)
      (IsDenseEmbedding.id.subtype (K : Set ℂ)).dense (by continuity : Continuous j)
    rintro ⟨y, hy⟩
    use
      ⟨y, by
        convert hy
        simp only [id, Set.image_id']
        rfl ⟩
end ComplexSubfield