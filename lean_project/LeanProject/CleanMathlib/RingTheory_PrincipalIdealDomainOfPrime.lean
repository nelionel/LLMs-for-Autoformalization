import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.PrincipalIdealDomain
open Ideal
variable {R : Type*} [CommRing R]
theorem IsPrincipalIdealRing.of_prime (H : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) :
    IsPrincipalIdealRing R := by
  rw [← nonPrincipals_eq_empty_iff, Set.eq_empty_iff_forall_not_mem]
  intro J hJ
  obtain ⟨I, hJI, hI⟩ := zorn_le_nonempty₀ (nonPrincipals R) nonPrincipals_zorn _ hJ
  have Imax' : ∀ {J}, I < J → J.IsPrincipal := by
    intro K hK
    simpa [nonPrincipals] using hI.not_prop_of_gt hK
  by_cases hI1 : I = ⊤
  · subst hI1
    exact hI.prop top_isPrincipal
  refine hI.prop (H I ⟨hI1, fun {x y} hxy => or_iff_not_imp_right.mpr fun hy => ?_⟩)
  obtain ⟨a, ha⟩ : (I ⊔ span {y}).IsPrincipal :=
    Imax' (left_lt_sup.mpr (mt I.span_singleton_le_iff_mem.mp hy))
  suffices He : ¬(I.colon (span {y})).IsPrincipal by
    rw [hI.eq_of_le ((nonPrincipals_def R).2 He) fun a ha ↦
      Ideal.mem_colon_singleton.2 (mul_mem_right _ _ ha)]
    exact Ideal.mem_colon_singleton.2 hxy
  rintro ⟨b, hb⟩
  refine (nonPrincipals_def _).1 hI.prop ⟨a * b, ?_⟩
  refine
    le_antisymm (α := Ideal R) (fun i hi => ?_) <|
      (span_singleton_mul_span_singleton a b).ge.trans ?_
  · have hisup : i ∈ I ⊔ span {y} := Ideal.mem_sup_left hi
    have : y ∈ I ⊔ span {y} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
    erw [ha, mem_span_singleton'] at hisup this
    obtain ⟨v, rfl⟩ := this
    obtain ⟨u, rfl⟩ := hisup
    have hucolon : u ∈ I.colon (span {v * a}) := by
      rw [Ideal.mem_colon_singleton, mul_comm v, ← mul_assoc]
      exact mul_mem_right _ _ hi
    erw [hb, mem_span_singleton'] at hucolon
    obtain ⟨z, rfl⟩ := hucolon
    exact mem_span_singleton'.2 ⟨z, by ring⟩
  · rw [← Ideal.submodule_span_eq, ← ha, Ideal.sup_mul, sup_le_iff,
      span_singleton_mul_span_singleton, mul_comm y, Ideal.span_singleton_le_iff_mem]
    exact ⟨mul_le_right, Ideal.mem_colon_singleton.1 <| hb.symm ▸ Ideal.mem_span_singleton_self b⟩