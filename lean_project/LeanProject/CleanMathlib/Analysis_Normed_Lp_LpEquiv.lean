import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.ContinuousMap.Bounded.Basic
open scoped ENNReal
section LpPiLp
variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}
section Finite
variable [Finite α]
theorem Memℓp.all (f : ∀ i, E i) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | _h)
  · exact memℓp_zero_iff.mpr { i : α | f i ≠ 0 }.toFinite
  · exact memℓp_infty_iff.mpr (Set.Finite.bddAbove (Set.range fun i : α ↦ ‖f i‖).toFinite)
  · cases nonempty_fintype α; exact memℓp_gen ⟨Finset.univ.sum _, hasSum_fintype _⟩
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := ⇑f
  invFun f := ⟨f, Memℓp.all f⟩
  left_inv _f := rfl
  right_inv _f := rfl
theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f :=
  rfl
theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
def AddEquiv.lpPiLp : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun _f _g ↦ rfl }
theorem coe_addEquiv_lpPiLp (f : lp E p) : AddEquiv.lpPiLp f = ⇑f :=
  rfl
theorem coe_addEquiv_lpPiLp_symm (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
end Finite
theorem equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl
section Equivₗᵢ
variable [Fintype α] (𝕜 : Type*) [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
variable (E)
noncomputable def lpPiLpₗᵢ [Fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun _k _f ↦ rfl
    norm_map' := equiv_lpPiLp_norm }
variable {𝕜 E}
theorem coe_lpPiLpₗᵢ [Fact (1 ≤ p)] (f : lp E p) : (lpPiLpₗᵢ E 𝕜 f : ∀ i, E i) = ⇑f :=
  rfl
theorem coe_lpPiLpₗᵢ_symm [Fact (1 ≤ p)] (f : PiLp p E) :
    ((lpPiLpₗᵢ E 𝕜).symm f : ∀ i, E i) = f :=
  rfl
end Equivₗᵢ
end LpPiLp
section LpBCF
open scoped BoundedContinuousFunction
open BoundedContinuousFunction
variable {α E : Type*} (R A 𝕜 : Type*) [TopologicalSpace α] [DiscreteTopology α]
variable [NormedRing A] [NormOneClass A] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NonUnitalNormedRing R]
section NormedAddCommGroup
noncomputable def AddEquiv.lpBCF : lp (fun _ : α ↦ E) ∞ ≃+ (α →ᵇ E) where
  toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ <| le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  left_inv _f := lp.ext rfl
  right_inv _f := rfl
  map_add' _f _g := rfl
@[deprecated (since := "2024-03-16")] alias AddEquiv.lpBcf := AddEquiv.lpBCF
theorem coe_addEquiv_lpBCF (f : lp (fun _ : α ↦ E) ∞) : (AddEquiv.lpBCF f : α → E) = f :=
  rfl
theorem coe_addEquiv_lpBCF_symm (f : α →ᵇ E) : (AddEquiv.lpBCF.symm f : α → E) = f :=
  rfl
variable (E)
noncomputable def lpBCFₗᵢ : lp (fun _ : α ↦ E) ∞ ≃ₗᵢ[𝕜] α →ᵇ E :=
  { AddEquiv.lpBCF with
    map_smul' := fun _ _ ↦ rfl
    norm_map' := fun f ↦ by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }
@[deprecated (since := "2024-03-16")] alias lpBcfₗᵢ := lpBCFₗᵢ
variable {𝕜 E}
theorem coe_lpBCFₗᵢ (f : lp (fun _ : α ↦ E) ∞) : (lpBCFₗᵢ E 𝕜 f : α → E) = f :=
  rfl
theorem coe_lpBCFₗᵢ_symm (f : α →ᵇ E) : ((lpBCFₗᵢ E 𝕜).symm f : α → E) = f :=
  rfl
end NormedAddCommGroup
section RingAlgebra
noncomputable def RingEquiv.lpBCF : lp (fun _ : α ↦ R) ∞ ≃+* (α →ᵇ R) :=
  { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }
@[deprecated (since := "2024-03-16")] alias RingEquiv.lpBcf := RingEquiv.lpBCF
variable {R}
theorem coe_ringEquiv_lpBCF (f : lp (fun _ : α ↦ R) ∞) : (RingEquiv.lpBCF R f : α → R) = f :=
  rfl
theorem coe_ringEquiv_lpBCF_symm (f : α →ᵇ R) : ((RingEquiv.lpBCF R).symm f : α → R) = f :=
  rfl
variable (α)
noncomputable def AlgEquiv.lpBCF : lp (fun _ : α ↦ A) ∞ ≃ₐ[𝕜] α →ᵇ A :=
  { RingEquiv.lpBCF A with commutes' := fun _k ↦ rfl }
@[deprecated (since := "2024-03-16")] alias AlgEquiv.lpBcf := AlgEquiv.lpBCF
variable {α A 𝕜}
theorem coe_algEquiv_lpBCF (f : lp (fun _ : α ↦ A) ∞) : (AlgEquiv.lpBCF α A 𝕜 f : α → A) = f :=
  rfl
theorem coe_algEquiv_lpBCF_symm (f : α →ᵇ A) : ((AlgEquiv.lpBCF α A 𝕜).symm f : α → A) = f :=
  rfl
end RingAlgebra
end LpBCF