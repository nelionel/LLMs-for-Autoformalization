import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
universe u v
open LinearMap hiding id
open Finsupp
class Module.Projective (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P] :
    Prop where
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.linearCombination R id) s
namespace Module
section Semiring
variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]
theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
theorem projective_def' :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.linearCombination R id ∘ₗ s = .id := by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]
theorem projective_lifting_property [h : Projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ h : P →ₗ[R] M, f ∘ₗ h = g := by
  let φ : (P →₀ R) →ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  cases' h.out with s hs
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsupp_sum]
theorem _root_.LinearMap.exists_rightInverse_of_surjective [Projective R P]
    (f : M →ₗ[R] P) (hf_surj : range f = ⊤) : ∃ g : P →ₗ[R] M, f ∘ₗ g = LinearMap.id :=
  projective_lifting_property f (.id : P →ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)
theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : ∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective f →
      ∃ h : P →ₗ[R] (P →₀ R), f.comp h = .id) :
    Projective R P :=
  projective_def'.2 <| huniv (Finsupp.linearCombination R (id : P → P))
    (linearCombination_surjective _ Function.surjective_id)
variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
instance [Projective R P] [Projective R Q] : Projective R (P × Q) := by
  refine .of_lifting_property'' fun f hf ↦ ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod, hg₁, hg₂, LinearMap.coprod_inl_inr]
variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]
instance [h : ∀ i : ι, Projective R (A i)] : Projective R (Π₀ i, A i) :=
  .of_lifting_property'' fun f hf ↦ by
    classical
      choose g hg using fun i ↦ projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : ∀ i x, f (g i x) = DFinsupp.single i x := fun i ↦ DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]
theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsupp_sum]
  exact b.linearCombination_repr m
instance (priority := 100) Projective.of_free [Module.Free R P] : Module.Projective R P :=
  .of_basis <| Module.Free.chooseBasis R P
theorem Projective.of_split [Module.Projective R M]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x ↦ ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply, hg,
    ← LinearMap.comp_apply, H, LinearMap.id_apply]
theorem Projective.of_equiv [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P :=
  Projective.of_split e.symm e.toLinearMap (by ext; simp)
theorem Projective.iff_split_of_projective [Module.Projective R M] (s : M →ₗ[R] P)
    (hs : Function.Surjective s) :
    Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id :=
  ⟨fun _ ↦ projective_lifting_property _ _ hs, fun ⟨i, H⟩ ↦ Projective.of_split i s H⟩
attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem Projective.of_ringEquiv {R S} [Semiring R] [Semiring S] {M N}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N)
    [Projective R M] : Projective S N := by
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N →ₗ[S] N →₀ S :=
  { toFun := fun x ↦ (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y ↦ by ext; simp
    map_smul' := fun r v ↦ by ext i; simp [e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x ↦ ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsupp_sum, e₂.map_smulₛₗ] using hf
end Semiring
section Ring
variable {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P]
variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]
variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]
theorem Projective.iff_split : Module.Projective R P ↔
    ∃ (M : Type max u v) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id :=
  ⟨fun ⟨i, hi⟩ ↦ ⟨P →₀ R, _, _, inferInstance, i, Finsupp.linearCombination R id, LinearMap.ext hi⟩,
    fun ⟨_, _, _, _, i, s, H⟩ ↦ Projective.of_split i s H⟩
set_option maxSynthPendingDepth 2 in
open TensorProduct in
instance Projective.tensorProduct [hM : Module.Projective R M] [hN : Module.Projective R₀ N] :
    Module.Projective R (M ⊗[R₀] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M ⊗[R₀] (N →₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M →₀ R) ⊗[R₀] (N →₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M ⊗[R₀] (N →₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (linearCombination R₀ id))
  · ext; simp [hsN _]
end Ring
section OfLiftingProperty
theorem Projective.of_lifting_property' {R : Type u} [Semiring R] {P : Type max u v}
    [AddCommMonoid P] [Module R P]
    (huniv : ∀ {M : Type max v u} {N : Type max u v} [AddCommMonoid M] [AddCommMonoid N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    Projective R P :=
  .of_lifting_property'' (huniv · _)
theorem Projective.of_lifting_property {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P]
    (huniv : ∀ {M : Type max v u} {N : Type max u v} [AddCommGroup M] [AddCommGroup N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    Projective R P :=
  .of_lifting_property'' (huniv · _)
end OfLiftingProperty
end Module