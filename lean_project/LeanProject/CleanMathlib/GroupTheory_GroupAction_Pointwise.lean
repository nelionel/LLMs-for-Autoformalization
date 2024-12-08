import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.GroupTheory.GroupAction.Hom
open Set Pointwise
theorem MulAction.smul_bijective_of_is_unit
    {M : Type*} [Monoid M] {α : Type*} [MulAction M α] {m : M} (hm : IsUnit m) :
    Function.Bijective (fun (a : α) ↦ m • a) := by
  lift m to Mˣ using hm
  rw [Function.bijective_iff_has_inverse]
  use fun a ↦ m⁻¹ • a
  constructor
  · intro x; simp [← Units.smul_def]
  · intro x; simp [← Units.smul_def]
variable {R S : Type*} (M M₁ M₂ N : Type*)
variable [Monoid R] [Monoid S] (σ : R → S)
variable [MulAction R M] [MulAction S N] [MulAction R M₁] [MulAction R M₂]
variable {F : Type*} (h : F)
section MulActionSemiHomClass
variable [FunLike F M N] [MulActionSemiHomClass F σ M N]
    (c : R) (s : Set M) (t : Set N)
theorem image_smul_setₛₗ :
    h '' (c • s) = σ c • h '' s := by
  simp only [← image_smul, image_image, map_smulₛₗ h]
theorem smul_preimage_set_leₛₗ :
    c • h ⁻¹' t ⊆ h ⁻¹' (σ c • t) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨h y, hy, by rw [map_smulₛₗ]⟩
variable {c}
theorem preimage_smul_setₛₗ'
    (hc : Function.Surjective (fun (m : M) ↦ c • m))
    (hc' : Function.Injective (fun (n : N) ↦ σ c • n)) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t := by
  apply le_antisymm
  · intro m
    obtain ⟨m', rfl⟩ := hc m
    rintro ⟨n, hn, hn'⟩
    refine ⟨m', ?_, rfl⟩
    rw [map_smulₛₗ] at hn'
    rw [mem_preimage, ← hc' hn']
    exact hn
  · exact smul_preimage_set_leₛₗ M N σ h c t
theorem preimage_smul_setₛₗ_of_units (hc : IsUnit c) (hc' : IsUnit (σ c)) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t := by
  apply preimage_smul_setₛₗ'
  · exact (MulAction.smul_bijective_of_is_unit hc).surjective
  · exact (MulAction.smul_bijective_of_is_unit hc').injective
theorem MonoidHom.preimage_smul_setₛₗ (σ : R →* S)
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F ⇑σ M N] (h : F)
    {c : R} (hc : IsUnit c) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units M N σ h t hc (IsUnit.map σ hc)
theorem preimage_smul_setₛₗ
    {G : Type*} [FunLike G R S] [MonoidHomClass G R S] (σ : G)
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N] (h : F)
    {c : R} (hc : IsUnit c) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
 MonoidHom.preimage_smul_setₛₗ M N (σ : R →* S) h hc t
theorem Group.preimage_smul_setₛₗ
    {R S : Type*} [Group R] [Group S] (σ : R → S)
    [MulAction R M] [MulAction S N]
    {F : Type*} [FunLike F M N] [MulActionSemiHomClass F σ M N] (h : F)
    (c : R) (t : Set N) :
    h ⁻¹' (σ c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units M N σ h t (Group.isUnit _) (Group.isUnit _)
end MulActionSemiHomClass
section MulActionHomClass
variable (R)
variable [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂]
    (c : R) (s : Set M₁) (t : Set M₂)
@[simp] 
theorem image_smul_set :
    h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s
theorem smul_preimage_set_le :
    c • h ⁻¹' t ⊆ h ⁻¹' (c • t) :=
  smul_preimage_set_leₛₗ _ _ _ h c t
variable {c}
theorem preimage_smul_set (hc : IsUnit c) :
    h ⁻¹' (c • t) = c • h ⁻¹' t :=
  preimage_smul_setₛₗ_of_units _ _ _ h t hc hc
theorem Group.preimage_smul_set
    {R : Type*} [Group R] (M₁ M₂ : Type*)
    [MulAction R M₁] [MulAction R M₂]
    {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (h : F)
    (c : R) (t : Set M₂) :
    h ⁻¹' (c • t) = c • h ⁻¹' t :=
  _root_.preimage_smul_set R M₁ M₂ h t (Group.isUnit c)
end MulActionHomClass