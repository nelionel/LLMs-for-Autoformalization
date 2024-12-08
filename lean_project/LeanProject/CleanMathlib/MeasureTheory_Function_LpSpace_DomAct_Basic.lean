import Mathlib.MeasureTheory.Function.AEEqFun.DomAct
import Mathlib.MeasureTheory.Function.LpSpace
open MeasureTheory Filter
open scoped ENNReal
namespace DomMulAct
variable {M N α E : Type*} [MeasurableSpace M] [MeasurableSpace N]
  [MeasurableSpace α] [NormedAddCommGroup E] {μ : MeasureTheory.Measure α} {p : ℝ≥0∞}
section SMul
variable [SMul M α] [SMulInvariantMeasure M α μ] [MeasurableSMul M α]
@[to_additive]
instance : SMul Mᵈᵐᵃ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f
@[to_additive (attr := simp)]
theorem smul_Lp_val (c : Mᵈᵐᵃ) (f : Lp E p μ) : (c • f).1 = c • f.1 := rfl
@[to_additive]
theorem smul_Lp_ae_eq (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  Lp.coeFn_compMeasurePreserving _ _
@[to_additive]
theorem mk_smul_toLp (c : M) {f : α → E} (hf : Memℒp f p μ) :
    mk c • hf.toLp f =
      (hf.comp_measurePreserving <| measurePreserving_smul c μ).toLp (f <| c • ·) :=
  rfl
@[to_additive (attr := simp)]
theorem smul_Lp_const [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E) :
    c • Lp.const p μ a = Lp.const p μ a :=
  rfl
@[to_additive]
theorem mk_smul_indicatorConstLp (c : M)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (b : E) :
    mk c • indicatorConstLp p hs hμs b =
      indicatorConstLp p (hs.preimage <| measurable_const_smul c)
        (by rwa [SMulInvariantMeasure.measure_preimage_smul c hs]) b :=
  rfl
instance [SMul N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableSMul N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl
instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E] :
    SMulCommClass Mᵈᵐᵃ 𝕜 (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl
instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E] :
    SMulCommClass 𝕜 Mᵈᵐᵃ (Lp E p μ) :=
  .symm _ _ _
@[to_additive]
theorem smul_Lp_add (c : Mᵈᵐᵃ) : ∀ f g : Lp E p μ, c • (f + g) = c • f + c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
attribute [simp] DomAddAct.vadd_Lp_add
@[to_additive (attr := simp 1001)]
theorem smul_Lp_zero (c : Mᵈᵐᵃ) : c • (0 : Lp E p μ) = 0 := rfl
@[to_additive]
theorem smul_Lp_neg (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • (-f) = -(c • f) := by
  rcases f with ⟨⟨_⟩, _⟩; rfl
@[to_additive]
theorem smul_Lp_sub (c : Mᵈᵐᵃ) : ∀ f g : Lp E p μ, c • (f - g) = c • f - c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
instance : DistribSMul Mᵈᵐᵃ (Lp E p μ) where
  smul_zero _ := rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
@[to_additive (attr := simp)]
theorem norm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _
@[to_additive (attr := simp)]
theorem nnnorm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖₊ = ‖f‖₊ :=
  NNReal.eq <| Lp.norm_compMeasurePreserving _ _
@[to_additive (attr := simp)]
theorem dist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : dist (c • f) (c • g) = dist f g := by
  simp only [dist, ← smul_Lp_sub, norm_smul_Lp]
@[to_additive (attr := simp)]
theorem edist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : edist (c • f) (c • g) = edist f g := by
  simp only [Lp.edist_dist, dist_smul_Lp]
variable [Fact (1 ≤ p)]
@[to_additive]
instance : IsometricSMul Mᵈᵐᵃ (Lp E p μ) := ⟨edist_smul_Lp⟩
end SMul
section MulAction
variable [Monoid M] [MulAction M α] [SMulInvariantMeasure M α μ] [MeasurableSMul M α]
@[to_additive]
instance : MulAction Mᵈᵐᵃ (Lp E p μ) := Subtype.val_injective.mulAction _ fun _ _ ↦ rfl
instance : DistribMulAction Mᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl
end MulAction
end DomMulAct