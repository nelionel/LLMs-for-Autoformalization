import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.TensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Basic
open Finsupp
section Semiring
variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
class Module.FinitePresentation : Prop where
  out : ∃ (s : Finset M), Submodule.span R (s : Set M) = ⊤ ∧
    (LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))).FG
instance (priority := 100) [h : Module.FinitePresentation R M] : Module.Finite R M := by
  obtain ⟨s, hs₁, _⟩ := h
  exact ⟨s, hs₁⟩
end Semiring
section Ring
variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
universe u in
variable (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] in
theorem Module.FinitePresentation.equiv_quotient [fp : Module.FinitePresentation R M] :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module R L) (K : Submodule R L) (_ : M ≃ₗ[R] L ⧸ K),
      Module.Free R L ∧ Module.Finite R L ∧ K.FG := by
  obtain ⟨ι, ⟨hι₁, hι₂⟩⟩ := fp
  use ι →₀ R, inferInstance, inferInstance
  use LinearMap.ker (Finsupp.linearCombination R Subtype.val)
  refine ⟨(LinearMap.quotKerEquivOfSurjective _ ?_).symm, inferInstance, inferInstance, hι₂⟩
  apply LinearMap.range_eq_top.mp
  simpa only [Finsupp.range_linearCombination, Subtype.range_coe_subtype, Finset.setOf_mem]
lemma Module.finitePresentation_of_finite [IsNoetherianRing R] [h : Module.Finite R M] :
    Module.FinitePresentation R M := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs, IsNoetherian.noetherian _⟩
lemma Module.finitePresentation_iff_finite [IsNoetherianRing R] :
    Module.FinitePresentation R M ↔ Module.Finite R M :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ finitePresentation_of_finite R M⟩
variable {R M N}
lemma Module.finitePresentation_of_free_of_surjective [Module.Free R M] [Module.Finite R M]
    (l : M →ₗ[R] N)
    (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    Module.FinitePresentation R N := by
  classical
  let b := Module.Free.chooseBasis R M
  let π : Free.ChooseBasisIndex R M → (Set.finite_range (l ∘ b)).toFinset :=
    fun i ↦ ⟨l (b i), by simp⟩
  have : π.Surjective := fun ⟨x, hx⟩ ↦ by
    obtain ⟨y, rfl⟩ : ∃ a, l (b a) = x := by simpa using hx
    exact ⟨y, rfl⟩
  choose σ hσ using this
  have hπ : Subtype.val ∘ π = l ∘ b := rfl
  have hσ₁ : π ∘ σ = id := by ext i; exact congr_arg Subtype.val (hσ i)
  have hσ₂ : l ∘ b ∘ σ = Subtype.val := by ext i; exact congr_arg Subtype.val (hσ i)
  refine ⟨(Set.finite_range (l ∘ b)).toFinset,
    by simpa [Set.range_comp, LinearMap.range_eq_top], ?_⟩
  let f : M →ₗ[R] (Set.finite_range (l ∘ b)).toFinset →₀ R :=
    Finsupp.lmapDomain _ _ π ∘ₗ b.repr.toLinearMap
  convert hl'.map f
  ext x; simp only [LinearMap.mem_ker, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨b.repr.symm (x.mapDomain σ), ?_, ?_⟩
    · simp [Finsupp.apply_linearCombination, hσ₂, hx]
    · simp only [f, LinearMap.comp_apply, b.repr.apply_symm_apply,
        LinearEquiv.coe_toLinearMap, Finsupp.lmapDomain_apply]
      rw [← Finsupp.mapDomain_comp, hσ₁, Finsupp.mapDomain_id]
  · rintro ⟨y, hy, rfl⟩
    simp [f, hπ, ← Finsupp.apply_linearCombination, hy]
variable (R M) in
lemma Module.finitePresentation_of_projective [Projective R M] [Module.Finite R M] :
    FinitePresentation R M :=
  have ⟨_n, _f, _g, surj, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  Module.finitePresentation_of_free_of_surjective _ surj
    (Finite.iff_fg.mp <| LinearMap.ker_eq_range_of_comp_eq_id hfg ▸ inferInstance)
@[deprecated (since := "2024-11-06")]
alias Module.finitePresentation_of_free := Module.finitePresentation_of_projective
variable {ι} [Finite ι]
instance : Module.FinitePresentation R R := Module.finitePresentation_of_projective _ _
instance : Module.FinitePresentation R (ι →₀ R) := Module.finitePresentation_of_projective _ _
instance : Module.FinitePresentation R (ι → R) := Module.finitePresentation_of_projective _ _
lemma Module.finitePresentation_of_surjective [h : Module.FinitePresentation R M] (l : M →ₗ[R] N)
    (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    Module.FinitePresentation R N := by
  classical
  obtain ⟨s, hs, hs'⟩ := h
  obtain ⟨t, ht⟩ := hl'
  have H : Function.Surjective (Finsupp.linearCombination R ((↑) : s → M)) :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hs]; rfl)
  apply Module.finitePresentation_of_free_of_surjective (l ∘ₗ linearCombination R Subtype.val)
    (hl.comp H)
  choose σ hσ using (show _ from H)
  have : Finsupp.linearCombination R Subtype.val '' (σ '' t) = t := by
    simp only [Set.image_image, hσ, Set.image_id']
  rw [LinearMap.ker_comp, ← ht, ← this, ← Submodule.map_span, Submodule.comap_map_eq,
    ← Finset.coe_image]
  exact Submodule.FG.sup ⟨_, rfl⟩ hs'
lemma Module.FinitePresentation.fg_ker [Module.Finite R M]
    [h : Module.FinitePresentation R N] (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    (LinearMap.ker l).FG := by
  classical
  obtain ⟨s, hs, hs'⟩ := h
  have H : Function.Surjective (Finsupp.linearCombination R ((↑) : s → N)) :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hs]; rfl)
  obtain ⟨f, hf⟩ : ∃ f : (s →₀ R) →ₗ[R] M, l ∘ₗ f = (Finsupp.linearCombination R Subtype.val) := by
    choose f hf using show _ from hl
    exact ⟨Finsupp.linearCombination R (fun i ↦ f i), by ext; simp [hf]⟩
  have : (LinearMap.ker l).map (LinearMap.range f).mkQ = ⊤ := by
    rw [← top_le_iff]
    rintro x -
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, hy⟩ := H (l x)
    rw [← hf, LinearMap.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub] at hy
    exact ⟨_, hy, by simp⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f.range.mkQ
  · rw [this]
    exact Module.Finite.out
  · rw [Submodule.ker_mkQ, inf_comm, ← Submodule.map_comap_eq, ← LinearMap.ker_comp, hf]
    exact hs'.map f
lemma Module.FinitePresentation.fg_ker_iff [Module.FinitePresentation R M]
    (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    Submodule.FG (LinearMap.ker l) ↔ Module.FinitePresentation R N :=
  ⟨finitePresentation_of_surjective l hl, fun _ ↦ fg_ker l hl⟩
lemma Module.finitePresentation_of_ker [Module.FinitePresentation R N]
    (l : M →ₗ[R] N) (hl : Function.Surjective l) [Module.FinitePresentation R (LinearMap.ker l)] :
    Module.FinitePresentation R M := by
  obtain ⟨s, hs⟩ : (⊤ : Submodule R M).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker l
    · rw [Submodule.map_top, LinearMap.range_eq_top.mpr hl]; exact Module.Finite.out
    · rw [top_inf_eq, ← Submodule.fg_top]; exact Module.Finite.out
  refine ⟨s, hs, ?_⟩
  let π := Finsupp.linearCombination R ((↑) : s → M)
  have H : Function.Surjective π :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hs]; rfl)
  have inst : Module.Finite R (LinearMap.ker (l ∘ₗ π)) := by
    constructor
    rw [Submodule.fg_top]; exact Module.FinitePresentation.fg_ker _ (hl.comp H)
  letI : AddCommGroup (LinearMap.ker (l ∘ₗ π)) := inferInstance
  let f : LinearMap.ker (l ∘ₗ π) →ₗ[R] LinearMap.ker l := LinearMap.restrict π (fun x ↦ id)
  have e : π ∘ₗ Submodule.subtype _ = Submodule.subtype _ ∘ₗ f := by ext; rfl
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.map_injective_of_injective (Submodule.injective_subtype _)
    rw [Submodule.map_top, Submodule.range_subtype, ← LinearMap.range_comp, ← e,
      LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
      Submodule.map_comap_eq_of_surjective H]
  show (LinearMap.ker π).FG
  have : LinearMap.ker π ≤ LinearMap.ker (l ∘ₗ π) :=
    Submodule.comap_mono (f := π) (bot_le (a := LinearMap.ker l))
  rw [← inf_eq_right.mpr this, ← Submodule.range_subtype (LinearMap.ker _),
    ← Submodule.map_comap_eq, ← LinearMap.ker_comp, e, LinearMap.ker_comp f,
    LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype (LinearMap.ker l)), Submodule.comap_bot]
  exact (Module.FinitePresentation.fg_ker f hf).map (Submodule.subtype _)
end Ring
section CommRing
variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]
open TensorProduct in
instance {A} [CommRing A] [Algebra R A] [Module.FinitePresentation R M] :
    Module.FinitePresentation A (A ⊗[R] M) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have inst := Module.finitePresentation_of_projective A (A ⊗[R] (Fin n → R))
  apply Module.finitePresentation_of_surjective (f.baseChange A)
    (LinearMap.lTensor_surjective A hf)
  have : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
    lTensor_exact A f.exact_subtype_ker_map hf
  rw [LinearMap.exact_iff] at this
  rw [this, ← Submodule.map_top]
  apply Submodule.FG.map
  have : Module.Finite R (LinearMap.ker f) :=
    ⟨(Submodule.fg_top _).mpr (Module.FinitePresentation.fg_ker f hf)⟩
  exact Module.Finite.out (R := A) (M := A ⊗[R] LinearMap.ker f)
open TensorProduct in
lemma FinitePresentation.of_isBaseChange
    {A} [CommRing A] [Algebra R A] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) (h : IsBaseChange A f) [Module.FinitePresentation R M] :
    Module.FinitePresentation A N :=
  Module.finitePresentation_of_surjective
    h.equiv.toLinearMap h.equiv.surjective (by simpa using Submodule.fg_bot)
open TensorProduct in
instance (S : Submonoid R) [Module.FinitePresentation R M] :
    Module.FinitePresentation (Localization S) (LocalizedModule S M) :=
  FinitePresentation.of_isBaseChange (LocalizedModule.mkLinearMap S M)
    ((isLocalizedModule_iff_isBaseChange S _ _).mp inferInstance)
lemma Module.FinitePresentation.exists_lift_of_isLocalizedModule
    [h : Module.FinitePresentation R M] (g : M →ₗ[R] N') :
    ∃ (h : M →ₗ[R] N) (s : S), f ∘ₗ h = s • g := by
  obtain ⟨σ, hσ, τ, hτ⟩ := h
  let π := Finsupp.linearCombination R ((↑) : σ → M)
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp
      (by rw [range_linearCombination, Subtype.range_val, ← hσ]; rfl)
  classical
  choose s hs using IsLocalizedModule.surj S f
  let i : σ → N :=
    fun x ↦ (∏ j ∈ σ.erase x.1, (s (g j)).2) • (s (g x)).1
  let s₀ := ∏ j ∈ σ, (s (g j)).2
  have hi : f ∘ₗ Finsupp.linearCombination R i = (s₀ • g) ∘ₗ π := by
    ext j
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      linearCombination_single, one_smul, LinearMap.map_smul_of_tower, ← hs, LinearMap.smul_apply,
      i, s₀, π]
    rw [← mul_smul, Finset.prod_erase_mul]
    exact j.prop
  have : ∀ x : τ, ∃ s : S, s • (Finsupp.linearCombination R i x) = 0 := by
    intros x
    convert_to ∃ s : S, s • (Finsupp.linearCombination R i x) = s • 0
    · simp only [smul_zero]
    apply IsLocalizedModule.exists_of_eq (S := S) (f := f)
    rw [← LinearMap.comp_apply, map_zero, hi, LinearMap.comp_apply]
    convert map_zero (s₀ • g)
    rw [← LinearMap.mem_ker, ← hτ]
    exact Submodule.subset_span x.prop
  choose s' hs' using this
  let s₁ := ∏ i : τ, s' i
  have : LinearMap.ker π ≤ LinearMap.ker (s₁ • Finsupp.linearCombination R i) := by
    rw [← hτ, Submodule.span_le]
    intro x hxσ
    simp only [s₁]
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨x, hxσ⟩), mul_smul]
    convert smul_zero _
    exact hs' ⟨x, hxσ⟩
  refine ⟨Submodule.liftQ _ _ this ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hπ).symm.toLinearMap, s₁ * s₀, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := hπ x
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, mul_smul, LinearMap.smul_comp, ← hi,
    ← LinearMap.comp_smul, LinearMap.comp_assoc, LinearMap.comp_assoc]
  congr 2
  convert Submodule.liftQ_mkQ _ _ this using 2
  ext x
  apply (LinearMap.quotKerEquivOfSurjective _ hπ).injective
  simp [LinearMap.quotKerEquivOfSurjective]
lemma Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    [hM : Module.Finite R M] (g₁ g₂ : M →ₗ[R] N) (h : f.comp g₁ = f.comp g₂) :
    ∃ (s : S), s • g₁ = s • g₂ := by
  classical
  have : ∀ x, ∃ s : S, s • g₁ x = s • g₂ x := fun x ↦
    IsLocalizedModule.exists_of_eq (S := S) (f := f) (LinearMap.congr_fun h x)
  choose s hs using this
  obtain ⟨σ, hσ⟩ := hM
  use σ.prod s
  rw [← sub_eq_zero, ← LinearMap.ker_eq_top, ← top_le_iff, ← hσ, Submodule.span_le]
  intro x hx
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    sub_eq_zero, ← Finset.prod_erase_mul σ s hx, mul_smul, hs]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]
lemma exists_bijective_map_powers [Module.Finite R M] [Module.FinitePresentation R N]
    (l : M →ₗ[R] N) (hf : Function.Bijective (IsLocalizedModule.map S f g l)) :
    ∃ r, r ∈ S ∧ ∀ t, r ∣ t → Function.Bijective (LocalizedModule.map (.powers t) l) := by
  let e : M' ≃ₗ[R] N' := LinearEquiv.ofBijective _ hf
  obtain ⟨l', s₀, H⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S f
    (e.symm.toLinearMap.comp g)
  have H₁ : g ∘ₗ l ∘ₗ l' = g ∘ₗ (s₀ • LinearMap.id) := by
    ext a; simpa [-EmbeddingLike.apply_eq_iff_eq, e] using congr(e ($H a))
  obtain ⟨s₁, hs₁⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S g _ _ H₁
  have H₂ : f ∘ₗ l' ∘ₗ l = f ∘ₗ (s₀ • LinearMap.id) := by
    rw [← LinearMap.comp_assoc, H, LinearMap.smul_comp, LinearMap.comp_assoc,
      ← IsLocalizedModule.map_comp S f g l, ← LinearMap.comp_assoc]
    show s₀ • (e.symm.toLinearMap ∘ₗ e.toLinearMap) ∘ₗ _ = _
    simp [LinearMap.comp_smul]
  obtain ⟨s₂, hs₂⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S f _ _ H₂
  refine ⟨s₀ * s₁ * s₂, (s₀ * s₁ * s₂).2, fun t ht ↦ ?_⟩
  let Rₛ := Localization (.powers t)
  let lₛ := LocalizedModule.map (.powers t) l
  have hu₀ : IsUnit (algebraMap R Rₛ s₀) := isUnit_of_dvd_unit
      (hu := IsLocalization.map_units (M := .powers t) Rₛ ⟨t, Submonoid.mem_powers t⟩)
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₁ * s₂, by simp [mul_assoc]⟩ ht))
  have hu₁ : IsUnit (algebraMap R Rₛ s₁) := isUnit_of_dvd_unit
      (hu := IsLocalization.map_units (M := .powers t) Rₛ ⟨t, Submonoid.mem_powers t⟩)
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₀ * s₂, by ring⟩ ht))
  have hu₂ : IsUnit (algebraMap R Rₛ s₂) := isUnit_of_dvd_unit
      (hu := IsLocalization.map_units (M := .powers t) Rₛ ⟨t, Submonoid.mem_powers t⟩)
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₀ * s₁, by ring⟩ ht))
  let lₛ' := LocalizedModule.map (.powers t) l'
  have H_left : ((hu₀.unit⁻¹).1 • lₛ') ∘ₗ lₛ = LinearMap.id := by
    apply ((Module.End_isUnit_iff _).mp (hu₂.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    apply ((Module.End_isUnit_iff _).mp (hu₀.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    simp only [Module.algebraMap_end_apply, algebraMap_smul, LinearMap.map_smul_of_tower]
    rw [LinearMap.smul_comp, ← smul_assoc s₀.1, Algebra.smul_def s₀.1, IsUnit.mul_val_inv, one_smul]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ringHom_ext (.powers t) (LocalizedModule.mkLinearMap (.powers t) M)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers t) M))
    ext x
    have : s₂.1 • l' (l x) = s₂.1 • s₀.1 • x := congr($hs₂ x)
    simp [lₛ, lₛ', LocalizedModule.smul'_mk, this]
  have H_right : lₛ ∘ₗ ((hu₀.unit⁻¹).1 • lₛ') = LinearMap.id := by
    apply ((Module.End_isUnit_iff _).mp (hu₁.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    apply ((Module.End_isUnit_iff _).mp (hu₀.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    simp only [Module.algebraMap_end_apply, algebraMap_smul, LinearMap.map_smul_of_tower]
    rw [LinearMap.comp_smul, ← smul_assoc s₀.1, Algebra.smul_def s₀.1, IsUnit.mul_val_inv, one_smul]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ringHom_ext (.powers t) (LocalizedModule.mkLinearMap (.powers t) N)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers t) N))
    ext x
    have : s₁.1 • l (l' x) = s₁.1 • s₀.1 • x := congr($hs₁ x)
    simp [lₛ, lₛ', LocalizedModule.smul'_mk, this]
  let eₛ : LocalizedModule (.powers t) M ≃ₗ[Rₛ] LocalizedModule (.powers t) N :=
    { __ := lₛ,
      invFun := ((hu₀.unit⁻¹).1 • lₛ'),
      left_inv := fun x ↦ congr($H_left x),
      right_inv := fun x ↦ congr($H_right x) }
  exact eₛ.bijective
open IsLocalizedModule in
lemma Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (l : M' ≃ₗ[R] N') :
    ∃ (r : R) (hr : r ∈ S)
      (l' : LocalizedModule (.powers r) M ≃ₗ[Localization (.powers r)]
        LocalizedModule (.powers r) N),
      (LocalizedModule.lift (.powers r) g fun s ↦ map_units g ⟨s.1, SetLike.le_def.mp
        (Submonoid.powers_le.mpr hr) s.2⟩) ∘ₗ l'.toLinearMap =
        l ∘ₗ (LocalizedModule.lift (.powers r) f fun s ↦ map_units f ⟨s.1, SetLike.le_def.mp
        (Submonoid.powers_le.mpr hr) s.2⟩) := by
  obtain ⟨l', s, H⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S g (l ∘ₗ f)
  have : Function.Bijective (IsLocalizedModule.map S f g l') := by
    have : IsLocalizedModule.map S f g l' = (s • LinearMap.id) ∘ₗ l := by
      apply IsLocalizedModule.ringHom_ext S f (IsLocalizedModule.map_units g)
      apply LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply,
        Basis.coe_repr_symm, LinearMap.coe_restrictScalars]
      rw [← LinearMap.comp_apply, H]
      simp
    rw [this]
    exact ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units g s)).comp l.bijective
  obtain ⟨r, hr, hr'⟩ := exists_bijective_map_powers S f g _ this
  let rs : Submonoid R := (.powers <| r * s)
  let Rᵣₛ := Localization rs
  have hsu : IsUnit (algebraMap R Rᵣₛ s) := isUnit_of_dvd_unit
      (hu := IsLocalization.map_units (M := rs) Rᵣₛ ⟨_, Submonoid.mem_powers _⟩)
      (map_dvd (algebraMap R Rᵣₛ) ⟨r, mul_comm _ _⟩)
  have : Function.Bijective ((hsu.unit⁻¹).1 • LocalizedModule.map rs l') :=
    ((Module.End_isUnit_iff _).mp ((hsu.unit⁻¹).isUnit.map (algebraMap _ (End Rᵣₛ
      (LocalizedModule rs N))))).comp (hr' (r * s) (dvd_mul_right _ _))
  refine ⟨r * s, mul_mem hr s.2, LinearEquiv.ofBijective _ this, ?_⟩
  apply IsLocalizedModule.ringHom_ext rs (LocalizedModule.mkLinearMap rs M) fun x ↦ map_units g
    ⟨x.1, SetLike.le_def.mp (Submonoid.powers_le.mpr (mul_mem hr s.2)) x.2⟩
  ext x
  apply ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
  have : ∀ x, g (l' x) = s.1 • (l (f x)) := LinearMap.congr_fun H
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.ofBijective_apply,
    LinearMap.smul_apply, LocalizedModule.map_mk, algebraMap_end_apply]
  rw [← map_smul, ← smul_assoc, Algebra.smul_def s.1, hsu.mul_val_inv, one_smul]
  simp only [LocalizedModule.lift_mk, OneMemClass.coe_one, map_one, IsUnit.unit_one,
    inv_one, Units.val_one, LinearMap.one_apply, this]
instance Module.FinitePresentation.isLocalizedModule_map [Module.FinitePresentation R M] :
      IsLocalizedModule S (IsLocalizedModule.map S f g) := by
  constructor
  · intro s
    rw [Module.End_isUnit_iff]
    have := (Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units (S := S) (f := g) s)
    constructor
    · exact fun _ _ e ↦ LinearMap.ext fun m ↦ this.left (LinearMap.congr_fun e m)
    · intro h
      use ((IsLocalizedModule.map_units (S := S) (f := g) s).unit⁻¹).1 ∘ₗ h
      ext x
      exact Module.End_isUnit_apply_inv_apply_of_isUnit
        (IsLocalizedModule.map_units (S := S) (f := g) s) (h x)
  · intro h
    obtain ⟨h', s, e⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S g (h ∘ₗ f)
    refine ⟨⟨h', s⟩, ?_⟩
    apply IsLocalizedModule.ringHom_ext S f (IsLocalizedModule.map_units g)
    refine e.symm.trans (by ext; simp)
  · intro h₁ h₂ e
    apply Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S g
    ext x
    simpa using LinearMap.congr_fun e (f x)
instance Module.FinitePresentation.isLocalizedModule_mapExtendScalars
    (Rₛ) [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [Module Rₛ N']
    [IsScalarTower R Rₛ M'] [IsScalarTower R Rₛ N'] [IsLocalization S Rₛ]
    [Module.FinitePresentation R M] :
      IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S f g Rₛ) :=
  IsLocalizedModule.of_linearEquiv _ _ _
instance [Module.FinitePresentation R M] :
    IsLocalizedModule S (LocalizedModule.map S (M := M) (N := N)) :=
  Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
end CommRing