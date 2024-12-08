import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finsupp.Basic
assert_not_exists Submodule
noncomputable section
open Set LinearMap
namespace Finsupp
variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
section LinearEquivFunOnFinite
variable (R : Type*) {S : Type*} (M : Type*) (α : Type*)
variable [Finite α] [AddCommMonoid M] [Semiring R] [Module R M]
@[simps apply]
noncomputable def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
@[simp]
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m
@[simp]
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m
@[simp]
theorem linearEquivFunOnFinite_symm_coe (f : α →₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f
end LinearEquivFunOnFinite
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
@[ext high]
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }
section LSubtypeDomain
variable (s : Set α)
def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl
theorem lsubtypeDomain_apply (f : α →₀ M) :
    (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtypeDomain (fun x => x ∈ s) f :=
  rfl
end LSubtypeDomain
@[simp]
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl
@[simp]
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl
@[simp]
theorem lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M →ₗ[R] M) := by ext; simp
@[simp]
theorem lapply_comp_lsingle_of_ne (a a' : α) (h : a ≠ a') :
    lapply a ∘ₗ lsingle a' = (0 : M →ₗ[R] M) := by ext; simp [h.symm]
section LMapDomain
variable {α' : Type*} {α'' : Type*} (M R)
def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul
@[simp]
theorem lmapDomain_apply (f : α → α') (l : α →₀ M) :
    (lmapDomain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = mapDomain f l :=
  rfl
@[simp]
theorem lmapDomain_id : (lmapDomain M R _root_.id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext fun _ => mapDomain_id
theorem lmapDomain_comp (f : α → α') (g : α' → α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun _ => mapDomain_comp
end LMapDomain
section LComapDomain
variable {β : Type*}
def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M where
  toFun l := Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
end LComapDomain
def mapRange.linearMap (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] α →₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    map_smul' := fun c v => mapRange_smul (hf := f.map_zero) c v (f.map_smul c) }
@[simp]
theorem mapRange.linearMap_apply (f : M →ₗ[R] N) (g : α →₀ M) :
    mapRange.linearMap f g = mapRange f f.map_zero g := rfl
@[simp]
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext mapRange_id
theorem mapRange.linearMap_comp (f : N →ₗ[R] P) (f₂ : M →ₗ[R] N) :
    (mapRange.linearMap (f.comp f₂) : (α →₀ _) →ₗ[R] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero
@[simp]
theorem mapRange.linearMap_toAddMonoidHom (f : M →ₗ[R] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext fun _ => rfl
def mapRange.linearEquiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }
@[simp]
theorem mapRange.linearEquiv_apply (e : M ≃ₗ[R] N) (g : α →₀ M) :
    mapRange.linearEquiv e g = mapRange.linearMap e.toLinearMap g := rfl
@[simp]
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext mapRange_id
theorem mapRange.linearEquiv_trans (f : M ≃ₗ[R] N) (f₂ : N ≃ₗ[R] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α →₀ _) ≃ₗ[R] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero
@[simp]
theorem mapRange.linearEquiv_symm (f : M ≃ₗ[R] N) :
    ((mapRange.linearEquiv f).symm : (α →₀ _) ≃ₗ[R] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun _x => rfl
@[simp 1500]
theorem mapRange.linearEquiv_toAddEquiv (f : M ≃ₗ[R] N) :
    (mapRange.linearEquiv f).toAddEquiv = (mapRange.addEquiv f.toAddEquiv : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => rfl
@[simp]
theorem mapRange.linearEquiv_toLinearMap (f : M ≃ₗ[R] N) :
    (mapRange.linearEquiv f).toLinearMap = (mapRange.linearMap f.toLinearMap : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext fun _ => rfl
section Prod
noncomputable def finsuppProdLEquiv {α β : Type*} (R : Type*) {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M :=
  { finsuppProdEquiv with
    map_add' := fun f g => by
      ext
      simp [finsuppProdEquiv, curry_apply]
    map_smul' := fun c f => by
      ext
      simp [finsuppProdEquiv, curry_apply] }
@[simp]
theorem finsuppProdLEquiv_apply {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α × β →₀ M) (x y) : finsuppProdLEquiv R f x y = f (x, y) := by
  rw [finsuppProdLEquiv, LinearEquiv.coe_mk, finsuppProdEquiv, Finsupp.curry_apply]
@[simp]
theorem finsuppProdLEquiv_symm_apply {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α →₀ β →₀ M) (xy) : (finsuppProdLEquiv R).symm f xy = f xy.1 xy.2 := by
  conv_rhs =>
    rw [← (finsuppProdLEquiv R).apply_symm_apply f, finsuppProdLEquiv_apply]
end Prod
end Finsupp
variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
open Finsupp
section
variable (R)
@[simps]
def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m := by
    letI := Module.subsingleton R M
    simp only [eq_iff_true_of_subsingleton]
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
end