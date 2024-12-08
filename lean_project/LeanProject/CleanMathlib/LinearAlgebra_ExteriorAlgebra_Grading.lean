import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
namespace ExteriorAlgebra
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (R M)
open scoped DirectSum
protected def GradedAlgebra.ι :
    M →ₗ[R] ⨁ i : ℕ, ⋀[R]^i M :=
  DirectSum.lof R ℕ (fun i => ⋀[R]^i M) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i : ℕ => ⋀[R]^i M) 1
        ⟨ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl
instance : SetLike.GradedMonoid fun i : ℕ ↦ ⋀[R]^i M :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))
attribute [local instance 1100] MulZeroClass.toZero in
theorem GradedAlgebra.ι_sq_zero (m : M) : GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0 := by
  rw [GradedAlgebra.ι_apply, DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)
def GradedAlgebra.liftι :
    ExteriorAlgebra R M →ₐ[R] ⨁ i : ℕ, ⋀[R]^i M :=
  lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩
theorem GradedAlgebra.liftι_eq (i : ℕ) (x : ⋀[R]^i M) :
    GradedAlgebra.liftι R M x = DirectSum.of (fun i => ⋀[R]^i M) i x := by
  cases' x with x hx
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← AddMonoidHom.map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
instance gradedAlgebra : GradedAlgebra (fun i : ℕ ↦ ⋀[R]^i M) :=
  GradedAlgebra.ofAlgHom _
    (
    by apply GradedAlgebra.liftι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, GradedAlgebra.liftι]
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    (by apply GradedAlgebra.liftι_eq R M)
lemma ιMulti_span :
    Submodule.span R (Set.range fun x : Σ n, (Fin n → M) => ιMulti R x.1 x.2) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
  | h_zero => exact Submodule.zero_mem _
  | h_add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
  | h_homogeneous hm =>
    let ⟨m, hm⟩ := hm
    apply Set.mem_of_mem_of_subset hm
    rw [← ιMulti_span_fixedDegree]
    refine Submodule.span_mono fun _ hx ↦ ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨_, y⟩, rfl⟩
end ExteriorAlgebra