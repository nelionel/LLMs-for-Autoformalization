import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.LinearDisjoint
open scoped TensorProduct
open Module IntermediateField
noncomputable section
universe u v w
namespace IntermediateField
variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable (A B : IntermediateField F E)
variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
protected abbrev LinearDisjoint : Prop :=
  A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
theorem linearDisjoint_iff :
    A.LinearDisjoint L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range :=
  Iff.rfl
variable {A B L}
theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩
namespace LinearDisjoint
variable (A) in
theorem self_right : A.LinearDisjoint F := Subalgebra.LinearDisjoint.bot_right _
variable (A) in
theorem bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)
variable (F E L) in
theorem bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  Subalgebra.LinearDisjoint.bot_left _
theorem linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a) :=
  (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)
theorem of_basis_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_left _ _ a <| H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)
theorem linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb
theorem of_basis_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_right _ _ b H)
theorem linearIndependent_right' (H : A.LinearDisjoint L) {ι : Type*} {b : ι → L}
    (hb : LinearIndependent F b) : LinearIndependent A (algebraMap L E ∘ b) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
theorem of_basis_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A (algebraMap L E ∘ b)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H
theorem linearIndependent_mul (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ → A} {b : ι → B}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb
theorem linearIndependent_mul' (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ → A} {b : ι → L}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
theorem of_basis_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)
theorem of_basis_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H
theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' ≤ A) : A'.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_le_left_of_flat H h
theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)
theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_le_left hA |>.of_le_right hB
theorem of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (hA : A' ≤ A) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint L' :=
  H.of_le_left hA |>.of_le_right' L'
theorem inf_eq_bot (H : A.LinearDisjoint B) :
    A ⊓ B = ⊥ := toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_idem A ▸ H.inf_eq_bot
theorem rank_sup_of_isAlgebraic (H : A.LinearDisjoint B)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) :
    Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B :=
  have h := le_sup_toSubalgebra A B
  (rank_sup_le_of_isAlgebraic A B halg).antisymm <|
    (linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans <|
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)
theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
  by_cases h : FiniteDimensional F A
  · simpa only [map_mul] using
      congr(Cardinal.toNat $(H.rank_sup_of_isAlgebraic (.inl inferInstance)))
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule A.toSubalgebra ≤ Subalgebra.toSubmodule (A ⊔ B).toSubalgebra by simp
  rw [show finrank F A = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank F ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]
theorem of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B]
    (H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 <| .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
    inferInstanceAs <| Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
  letI : Field A.toSubalgebra := inferInstanceAs <| Field A
  Subalgebra.LinearDisjoint.of_finrank_coprime_of_free <| by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H
end LinearDisjoint
end IntermediateField