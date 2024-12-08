import Mathlib.Topology.Algebra.Module.Basic
section basics
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]
abbrev moduleTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}
class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  eq_moduleTopology' : τA = moduleTopology R A
theorem eq_moduleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.eq_moduleTopology' (R := R) (A := A)
theorem ModuleTopology.continuousSMul : @ContinuousSMul R A _ _ (moduleTopology R A) :=
  continuousSMul_sInf fun _ h ↦ h.1
theorem ModuleTopology.continuousAdd : @ContinuousAdd A (moduleTopology R A) _ :=
  continuousAdd_sInf fun _ h ↦ h.2
instance IsModuleTopology.toContinuousSMul [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousSMul R A := eq_moduleTopology R A ▸ ModuleTopology.continuousSMul R A
theorem IsModuleTopology.toContinuousAdd [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousAdd A := eq_moduleTopology R A ▸ ModuleTopology.continuousAdd R A
theorem moduleTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    moduleTopology R A ≤ τA := sInf_le ⟨inferInstance, inferInstance⟩
end basics
namespace IsModuleTopology
section basics
variable {R : Type*} [TopologicalSpace R]
  {A : Type*} [Add A] [SMul R A] [τA : TopologicalSpace A]
theorem of_continuous_id [ContinuousAdd A] [ContinuousSMul R A]
    (h : @Continuous A A τA (moduleTopology R A) id):
    IsModuleTopology R A where
  eq_moduleTopology' := le_antisymm (continuous_id_iff_le.1 h) (moduleTopology_le _ _)
instance instSubsingleton [Subsingleton A] : IsModuleTopology R A where
  eq_moduleTopology' := Subsingleton.elim _ _
end basics
section iso
variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]
theorem iso (e : A ≃L[R] B) : IsModuleTopology R B where
  eq_moduleTopology' := by
    let g : A →ₗ[R] B := e
    let g' : B →ₗ[R] A := e.symm
    let h : A →+ B := e
    let h' : B →+ A := e.symm
    simp_rw [e.toHomeomorph.symm.isInducing.1, eq_moduleTopology R A, moduleTopology, induced_sInf]
    apply congr_arg
    ext τ 
    rw [Set.mem_image]
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      exact ⟨continuousSMul_induced g'.toMulActionHom, continuousAdd_induced h'⟩
    · rintro ⟨h1, h2⟩
      use τ.induced e
      rw [induced_compose]
      refine ⟨⟨continuousSMul_induced g.toMulActionHom, continuousAdd_induced h⟩, ?_⟩
      nth_rw 2 [← induced_id (t := τ)]
      simp
end iso
section self
variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]
instance _root_.TopologicalSemiring.toIsModuleTopology : IsModuleTopology R R := by
  apply of_continuous_id
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  apply @Continuous.comp R (R × R) R τR (@instTopologicalSpaceProd R R τR (moduleTopology R R))
      (moduleTopology R R)
  · 
    exact @continuous_smul _ _ _ _ (moduleTopology R R) <| ModuleTopology.continuousSMul ..
  · 
    exact @Continuous.prod_mk _ _ _ _ (moduleTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (moduleTopology R R) _
end self
section MulOpposite
variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]
instance _root_.TopologicalSemiring.toOppositeIsModuleTopology : IsModuleTopology Rᵐᵒᵖ R :=
  .iso (MulOpposite.opContinuousLinearEquiv Rᵐᵒᵖ).symm
end MulOpposite
section function
variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B]
    [ContinuousAdd B] [ContinuousSMul R B]
@[fun_prop, continuity]
theorem continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ := by
  rw [eq_moduleTopology R A, continuous_iff_le_induced]
  exact sInf_le <| ⟨continuousSMul_induced (φ.toMulActionHom),
    continuousAdd_induced φ.toAddMonoidHom⟩
@[fun_prop, continuity]
theorem continuous_of_linearMap (φ : A →ₗ[R] B) : Continuous φ :=
  continuous_of_distribMulActionHom φ.toDistribMulActionHom
variable (R) in
theorem continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : Continuous (fun a ↦ -a : C → C) :=
  haveI : ContinuousAdd C := IsModuleTopology.toContinuousAdd R C
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap
@[fun_prop, continuity]
theorem continuous_of_ringHom {R A B} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [TopologicalSpace R] [TopologicalSpace A] [IsModuleTopology R A] [TopologicalSpace B]
    [TopologicalSemiring B]
    (φ : A →+* B) (hφ : Continuous (φ.comp (algebraMap R A))) : Continuous φ := by
  let inst := Module.compHom B (φ.comp (algebraMap R A))
  let φ' : A →ₗ[R] B := ⟨φ, fun r m ↦ by simp [Algebra.smul_def]; rfl⟩
  have : ContinuousSMul R B := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  exact continuous_of_linearMap φ'
end function
end IsModuleTopology