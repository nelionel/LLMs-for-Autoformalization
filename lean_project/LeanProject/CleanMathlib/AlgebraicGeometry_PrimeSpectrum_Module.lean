import Mathlib.RingTheory.Support
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
variable {R A M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A] [Module A M]
section support
lemma LocalizedModule.subsingleton_iff_disjoint {f : R} :
    Subsingleton (LocalizedModule (.powers f) M) ↔
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R M) := by
  rw [subsingleton_iff_support_subset, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    disjoint_compl_left_iff]
  rfl
lemma Module.stableUnderSpecialization_support :
    StableUnderSpecialization (Module.support R M) := by
  intros x y e H
  rw [mem_support_iff_exists_annihilator] at H ⊢
  obtain ⟨m, hm⟩ := H
  exact ⟨m, hm.trans ((PrimeSpectrum.le_iff_specializes _ _).mpr e)⟩
lemma Module.isClosed_support [Module.Finite R M] :
    IsClosed (Module.support R M) := by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus
lemma Module.support_subset_preimage_comap [IsScalarTower R A M] :
    Module.support A M ⊆ PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M := by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e ↦ hm _ (by simpa)⟩
end support