import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
open CategoryTheory Module
namespace ModuleCat
variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}
open CategoryTheory Submodule Set
section LinearIndependent
variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)
section
include hS hw huv
theorem disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl)))
    (span R (range (u ∘ Sum.inr))) := by
  rw [huv, disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.range_coe, span_eq (LinearMap.range S.f), hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw
include hv hm in
theorem linearIndependent_leftExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g hw, disjoint_span_sum hS hw huv⟩
  rw [huv, LinearMap.linearIndependent_iff S.f]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv
end
include hS' hv in
theorem linearIndependent_shortExact {w : ι' → S.X₃} (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.toFun.invFun ∘ w)) := by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)
end LinearIndependent
section Span
include hS in
theorem span_exact {β : Type*} {u : ι ⊕ β → S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
    (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range (S.g ∘ u ∘ Sum.inr))) :
    ⊤ ≤ span R (range u) := by
  intro m _
  have hgm : S.g m ∈ span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j))
  have hsub : m - m' ∈ LinearMap.range S.f := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsupp_sum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsupp_sum] at hnm
  rw [← sub_add_cancel m m', ← hnm,]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • S.f (v a)) =
      (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
include hS in
theorem span_rightExact {w : ι' → S.X₃} (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range w)) (hE : Epi S.g) :
    ⊤ ≤ span R (range (Sum.elim (S.f ∘ v) (S.g.toFun.invFun ∘ w))) := by
  refine span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE),
      Function.id_comp]
end Span
noncomputable
def Basis.ofShortExact
    (bN : Basis ι R S.X₁) (bP : Basis ι' R S.X₃) : Basis (ι ⊕ ι') R S.X₂ :=
  Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)
include hS'
theorem free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] :
    Module.Free R S.X₂ :=
  Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))
theorem free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃]
    [StrongRankCondition R] :
    Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃ := by
  haveI := free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex, Module.Free.rank_eq_card_chooseBasisIndex R S.X₁,
    Module.Free.rank_eq_card_chooseBasisIndex R S.X₃, Cardinal.add_def, Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩
theorem free_shortExact_finrank_add {n p : ℕ} [Module.Free R S.X₁] [Module.Free R S.X₃]
    [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    (hN : Module.finrank R S.X₁ = n)
    (hP : Module.finrank R S.X₃ = p)
    [StrongRankCondition R] :
    finrank R S.X₂ = n + p := by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS', ← hN, ← hP]
  simp only [Nat.cast_add, finrank_eq_rank]
end ModuleCat