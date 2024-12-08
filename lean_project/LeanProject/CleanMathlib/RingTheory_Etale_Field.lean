import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.Field
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
open Algebra Polynomial
open scoped TensorProduct
namespace Algebra.FormallyEtale
theorem of_isSeparable_aux [Algebra.IsSeparable K L] [EssFiniteType K L] :
    FormallyEtale K L := by
  have := FormallyUnramified.of_isSeparable K L
  have := FormallyUnramified.finite_of_free (R := K) (S := L)
  constructor
  intros B _ _ I h
  refine ⟨FormallyUnramified.iff_comp_injective.mp (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
  have helper : ∀ x, IsScalarTower.toAlgHom K B (B ⧸ I) x = Ideal.Quotient.mk I x := fun _ ↦ rfl
  have hx' : Ideal.Quotient.mk I (aeval x (minpoly K pb.gen)) = 0 := by
    rw [← helper, ← aeval_algHom_apply, helper, hx, aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨u, hu⟩ : ∃ u, (aeval x) (derivative (minpoly K pb.gen)) * u + 1 ∈ I := by
    have := (isUnit_iff_ne_zero.mpr ((Algebra.IsSeparable.isSeparable K
      pb.gen).aeval_derivative_ne_zero (minpoly.aeval K _))).map f
    rw [← aeval_algHom_apply, ← hx, ← helper, aeval_algHom_apply, helper] at this
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (-this.unit⁻¹ : B ⧸ I)
    use u
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_one, hu, mul_neg,
      IsUnit.mul_val_inv, neg_add_cancel]
  use pb.liftEquiv.symm ⟨x + u * aeval x (minpoly K pb.gen), ?_⟩
  · apply pb.algHom_ext
    simp [hx, hx']
  · rw [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero, derivative_map,
      ← one_mul (eval x _), eval_map_algebraMap, eval_map_algebraMap, ← mul_assoc, ← add_mul,
      ← Ideal.mem_bot, ← h, pow_two, add_comm]
    · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    rw [← Ideal.mem_bot, ← h]
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hx', mul_zero]
open scoped IntermediateField in
lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L := by
  constructor
  intros B _ _ I h
  refine ⟨FormallyUnramified.iff_comp_injective.mp (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  have : ∀ k : L, ∃! g : K⟮k⟯ →ₐ[K] B,
      (Ideal.Quotient.mkₐ K I).comp g = f.comp (IsScalarTower.toAlgHom K _ L) := by
    intro k
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮k⟯) L)
    have := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsSeparable.isSeparable K k).isIntegral
    have := FormallyEtale.of_isSeparable_aux K (K⟮k⟯)
    have := FormallyEtale.comp_bijective (R := K) (A := K⟮k⟯) I h
    exact this.existsUnique _
  choose g hg₁ hg₂ using this
  have hg₃ : ∀ x y (h : x ∈ K⟮y⟯), g y ⟨x, h⟩ = g x (IntermediateField.AdjoinSimple.gen K x) := by
    intro x y h
    have e : K⟮x⟯ ≤ K⟮y⟯ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact h
    rw [← hg₂ _ ((g _).comp (IntermediateField.inclusion e))]
    · rfl
    apply AlgHom.ext
    intro ⟨a, _⟩
    rw [← AlgHom.comp_assoc, hg₁, AlgHom.comp_assoc]
    simp
  have H : ∀ x y : L, ∃ α : L, x ∈ K⟮α⟯ ∧ y ∈ K⟮α⟯ := by
    intro x y
    have : FiniteDimensional K K⟮x, y⟯ := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _; exact (Algebra.IsSeparable.isSeparable K x).isIntegral
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮x, y⟯) L)
    obtain ⟨⟨α, hα⟩, e⟩ := Field.exists_primitive_element K K⟮x,y⟯
    apply_fun (IntermediateField.map (IntermediateField.val _)) at e
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map] at e
    simp only [IntermediateField.coe_val, Set.image_singleton,
      IntermediateField.fieldRange_val] at e
    have hx : x ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    exact ⟨α, hx, hy⟩
  refine ⟨⟨⟨⟨⟨fun x ↦ g x (IntermediateField.AdjoinSimple.gen K x), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · show g 1 1 = 1; rw [map_one]
  · intros x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_mul, ← hg₃ _ _ (mul_mem hx hy)]
    rfl
  · show g 0 0 = 0; rw [map_zero]
  · intros x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_add, ← hg₃ _ _ (add_mem hx hy)]
    rfl
  · intro r
    show g _ (algebraMap K _ r) = _
    rw [AlgHom.commutes]
  · ext x
    simpa using AlgHom.congr_fun (hg₁ x) (IntermediateField.AdjoinSimple.gen K x)
theorem iff_isSeparable [EssFiniteType K L] :
    FormallyEtale K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ FormallyUnramified.isSeparable K L, fun _ ↦ of_isSeparable K L⟩
end Algebra.FormallyEtale