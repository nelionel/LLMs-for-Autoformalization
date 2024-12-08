import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
include p in
theorem IsLocalization.flat : Module.Flat R S :=
  (Module.Flat.iff_lTensor_injective' _ _).mpr fun I ↦ by
    have h := (I.isLocalizedModule S p (Algebra.linearMap R S)).isBaseChange _ S _
    have : I.subtype.lTensor S = (TensorProduct.rid R S).symm.comp
        ((Submodule.subtype _ ∘ₗ h.equiv.toLinearMap).restrictScalars R) := by
      rw [LinearEquiv.eq_toLinearMap_symm_comp]; ext
      simp [h.equiv_tmul, Algebra.smul_def, mul_comm, Algebra.ofId_apply]
    simpa [this, - Subtype.val_injective] using Subtype.val_injective
instance Localization.flat : Module.Flat R (Localization p) := IsLocalization.flat _ p