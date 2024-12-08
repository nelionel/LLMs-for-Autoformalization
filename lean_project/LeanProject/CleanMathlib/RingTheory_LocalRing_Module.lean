import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.Free
variable {R} [CommRing R]
section
variable {M N} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
open Function (Injective Surjective Exact)
open IsLocalRing TensorProduct
local notation "k" => ResidueField R
local notation "𝔪" => maximalIdeal R
variable {P} [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
namespace IsLocalRing
variable [IsLocalRing R]
theorem map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ ≤ 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp
theorem map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.out, Submodule.map_top, Submodule.range_mkQ]
theorem map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    letI : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    letI : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this, LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
theorem subsingleton_tensorProduct [Module.Finite R M] :
    Subsingleton (k ⊗[R] M) ↔ Subsingleton M := by
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← map_tensorProduct_mk_eq_top (M := M), Submodule.map_bot]
theorem span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← map_tensorProduct_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]
end IsLocalRing
@[deprecated (since := "2024-11-11")]
alias LocalRing.map_mkQ_eq := IsLocalRing.map_mkQ_eq
@[deprecated (since := "2024-11-11")]
alias LocalRing.map_mkQ_eq_top := IsLocalRing.map_mkQ_eq_top
@[deprecated (since := "2024-11-11")]
alias LocalRing.map_tensorProduct_mk_eq_top := IsLocalRing.map_tensorProduct_mk_eq_top
@[deprecated (since := "2024-11-11")]
alias LocalRing.subsingleton_tensorProduct := IsLocalRing.subsingleton_tensorProduct
@[deprecated (since := "2024-11-11")]
alias LocalRing.span_eq_top_of_tmul_eq_basis := IsLocalRing.span_eq_top_of_tmul_eq_basis
open Function in
theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hfexact : Exact f₁ f₂) (hfsurj : Surjective f₂)
    (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂)
    (hfinj : Injective (f₁.rTensor N₃)) (hginj : Injective (g₁.lTensor M₂)) :
    Injective (g₁.lTensor M₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfexact.linearMap_comp_eq_zero]
  simp
namespace Module
variable [IsLocalRing R]
theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    Module.Free R M := by
  let I := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  let b : Basis I k _ := Module.Free.chooseBasis k (k ⊗[R] M)
  letI : IsNoetherian k (k ⊗[R] (I →₀ R)) :=
    isNoetherian_of_isNoetherianRing_of_finite k (k ⊗[R] (I →₀ R))
  choose f hf using TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  let i := Finsupp.linearCombination R (f ∘ b)
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := f ∘ b) b (fun _ ↦ hf _)
  have : Module.Finite R (LinearMap.ker i) := by
    constructor
    exact (Submodule.fg_top _).mpr (Module.FinitePresentation.fg_ker i hi)
  refine Module.Free.of_equiv (LinearEquiv.ofBijective i ⟨?_, hi⟩)
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    ← IsLocalRing.subsingleton_tensorProduct (R := R), subsingleton_iff_forall_eq 0]
  have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
  have hi' : Function.Bijective (i.baseChange k) := by
    refine ⟨?_, this⟩
    rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (I →₀ R)) (f := i.baseChange k),
      ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (I →₀ R)),
      ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
      LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (I →₀ R)),
      LinearMap.range_eq_top.mpr this, finrank_top]
    simp only [Module.finrank_tensorProduct, Module.finrank_self,
      Module.finrank_finsupp_self, one_mul, add_zero]
    rw [Module.finrank_eq_card_chooseBasisIndex]
  intro x
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (N₁ := LinearMap.ker i) (N₂ := I →₀ R) (N₃ := M)
    (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
    (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
  · apply Module.Flat.lTensor_preserves_injective_linearMap
      (N := LinearMap.ker i) (N' := I →₀ R)
      (L := (LinearMap.ker i).subtype)
    exact Subtype.val_injective
  · apply hi'.injective
    rw [LinearMap.baseChange_eq_ltensor]
    erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
    rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
    simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
theorem free_of_flat_of_isLocalRing [Module.FinitePresentation R P] [Module.Flat R P] :
    Module.Free R P :=
  free_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
@[deprecated (since := "2024-11-12")] alias free_of_flat_of_localRing := free_of_flat_of_isLocalRing
theorem free_of_lTensor_residueField_injective (hg : Surjective g) (h : Exact f g)
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (hf : Function.Injective (f.lTensor k)) :
    Module.Free R P := by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.out).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
end Module
theorem IsLocalRing.split_injective_iff_lTensor_residueField_injective [IsLocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (l : M →ₗ[R] N) :
    (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    obtain ⟨l', hl'⟩ : ∃ l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    have : Subsingleton (k ⊗[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y ↦ H (h ?_)
      rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← IsLocalRing.subsingleton_tensorProduct (R := R)]
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)
@[deprecated (since := "2024-11-09")]
alias LocalRing.split_injective_iff_lTensor_residueField_injective :=
  IsLocalRing.split_injective_iff_lTensor_residueField_injective
end