import Mathlib.Analysis.Convex.Normed
variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
open TopologicalSpace Topology
def TopologicalSpace.deltaGenerated (X : Type*) [TopologicalSpace X] : TopologicalSpace X :=
  ⨆ f : (n : ℕ) × C(((Fin n) → ℝ), X), coinduced f.2 inferInstance
lemma deltaGenerated_eq_coinduced : deltaGenerated X = coinduced
    (fun x : (f : (n : ℕ) × C(Fin n → ℝ, X)) × (Fin f.1 → ℝ) ↦ x.1.2 x.2) inferInstance := by
  rw [deltaGenerated, instTopologicalSpaceSigma, coinduced_iSup]; rfl
lemma deltaGenerated_le : deltaGenerated X ≤ tX :=
  iSup_le_iff.mpr fun f ↦ f.2.continuous.coinduced_le
lemma isOpen_deltaGenerated_iff {u : Set X} :
    IsOpen[deltaGenerated X] u ↔ ∀ n (p : C(Fin n → ℝ, X)), IsOpen (p ⁻¹' u) := by
  simp_rw [deltaGenerated, isOpen_iSup_iff, isOpen_coinduced, Sigma.forall]
private lemma continuous_euclidean_to_deltaGenerated {n : ℕ} {f : (Fin n → ℝ) → X} :
    Continuous[_, deltaGenerated X] f ↔ Continuous f := by
  simp_rw [continuous_iff_coinduced_le]
  refine ⟨fun h ↦ h.trans deltaGenerated_le, fun h ↦ ?_⟩
  simp_rw [deltaGenerated]
  exact le_iSup_of_le (i := ⟨n, f, continuous_iff_coinduced_le.mpr h⟩) le_rfl
lemma deltaGenerated_deltaGenerated_eq :
    @deltaGenerated X (deltaGenerated X) = deltaGenerated X := by
  ext u; simp_rw [isOpen_deltaGenerated_iff]; refine forall_congr' fun n ↦ ?_
  refine ⟨fun h p ↦ h <| @ContinuousMap.mk _ _ _ (_) p ?_, fun h p ↦ h ⟨p, ?_⟩⟩
  · exact continuous_euclidean_to_deltaGenerated.mpr p.2
  · exact continuous_euclidean_to_deltaGenerated.mp <| @ContinuousMap.continuous_toFun _ _ _ (_) p
class DeltaGeneratedSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  le_deltaGenerated : t ≤ deltaGenerated X
lemma eq_deltaGenerated [DeltaGeneratedSpace X] : tX = deltaGenerated X :=
  eq_of_le_of_le DeltaGeneratedSpace.le_deltaGenerated deltaGenerated_le
lemma DeltaGeneratedSpace.isOpen_iff [DeltaGeneratedSpace X] {u : Set X} :
    IsOpen u ↔ ∀ (n : ℕ) (p : ContinuousMap ((Fin n) → ℝ) X), IsOpen (p ⁻¹' u) := by
  nth_rewrite 1 [eq_deltaGenerated (X := X)]; exact isOpen_deltaGenerated_iff
lemma DeltaGeneratedSpace.continuous_iff [DeltaGeneratedSpace X] {f : X → Y} :
    Continuous f ↔ ∀ (n : ℕ) (p : C(((Fin n) → ℝ), X)), Continuous (f ∘ p) := by
  simp_rw [continuous_iff_coinduced_le]
  nth_rewrite 1 [eq_deltaGenerated (X := X), deltaGenerated]
  simp [coinduced_compose]
  constructor
  · intro h n p; apply h ⟨n, p⟩
  · rintro h ⟨n, p⟩; apply h n p
lemma continuous_to_deltaGenerated [DeltaGeneratedSpace X] {f : X → Y} :
    Continuous[_, deltaGenerated Y] f ↔ Continuous f := by
  simp_rw [DeltaGeneratedSpace.continuous_iff, continuous_euclidean_to_deltaGenerated]
lemma deltaGeneratedSpace_deltaGenerated {X : Type*} {t : TopologicalSpace X} :
    @DeltaGeneratedSpace X (@deltaGenerated X t) := by
  let _ := @deltaGenerated X t; constructor; rw [@deltaGenerated_deltaGenerated_eq X t]
lemma deltaGenerated_mono {X : Type*} {t₁ t₂ : TopologicalSpace X} (h : t₁ ≤ t₂) :
    @deltaGenerated X t₁ ≤ @deltaGenerated X t₂ := by
  rw [← continuous_id_iff_le, @continuous_to_deltaGenerated _ _
    (@deltaGenerated X t₁) t₂ deltaGeneratedSpace_deltaGenerated id]
  exact continuous_id_iff_le.2 <| (@deltaGenerated_le X t₁).trans h
namespace DeltaGeneratedSpace
def of (X : Type*) := X
instance : TopologicalSpace (of X) := deltaGenerated X
instance : DeltaGeneratedSpace (of X) :=
  deltaGeneratedSpace_deltaGenerated
def counit : (of X) → X := id
lemma continuous_counit : Continuous (counit : _ → X) := by
  rw [continuous_iff_coinduced_le]; exact deltaGenerated_le
instance [DeltaGeneratedSpace X] : LocPathConnectedSpace X := by
  rw [eq_deltaGenerated (X := X), deltaGenerated_eq_coinduced]
  exact LocPathConnectedSpace.coinduced _
instance [DeltaGeneratedSpace X] : SequentialSpace X := by
  rw [eq_deltaGenerated (X := X)]
  exact SequentialSpace.iSup fun p ↦ SequentialSpace.coinduced p.2
end DeltaGeneratedSpace
omit tY in
lemma DeltaGeneratedSpace.coinduced [DeltaGeneratedSpace X] (f : X → Y) :
    @DeltaGeneratedSpace Y (tX.coinduced f) :=
  let _ := tX.coinduced f
  ⟨(continuous_to_deltaGenerated.2 continuous_coinduced_rng).coinduced_le⟩
protected lemma DeltaGeneratedSpace.iSup {X : Type*} {ι : Sort*} {t : ι → TopologicalSpace X}
    (h : ∀ i, @DeltaGeneratedSpace X (t i)) : @DeltaGeneratedSpace X (⨆ i, t i) :=
  let _ := ⨆ i, t i
  ⟨iSup_le_iff.2 fun i ↦ (h i).le_deltaGenerated.trans <| deltaGenerated_mono <| le_iSup t i⟩
protected lemma DeltaGeneratedSpace.sup {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @DeltaGeneratedSpace X t₁) (h₂ : @DeltaGeneratedSpace X t₂) :
    @DeltaGeneratedSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
  exact .iSup <| Bool.forall_bool.2 ⟨h₂, h₁⟩
lemma Topology.IsQuotientMap.deltaGeneratedSpace [DeltaGeneratedSpace X]
    {f : X → Y} (h : IsQuotientMap f) : DeltaGeneratedSpace Y :=
  h.2 ▸ DeltaGeneratedSpace.coinduced f
instance Quot.deltaGeneratedSpace [DeltaGeneratedSpace X] {r : X → X → Prop} :
    DeltaGeneratedSpace (Quot r) :=
  isQuotientMap_quot_mk.deltaGeneratedSpace
instance Quotient.deltaGeneratedSpace [DeltaGeneratedSpace X] {s : Setoid X} :
    DeltaGeneratedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.deltaGeneratedSpace
instance Sum.deltaGeneratedSpace [DeltaGeneratedSpace X] [DeltaGeneratedSpace Y] :
    DeltaGeneratedSpace (X ⊕ Y) :=
  DeltaGeneratedSpace.sup (.coinduced Sum.inl) (.coinduced Sum.inr)
instance Sigma.deltaGeneratedSpace {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, DeltaGeneratedSpace (X i)] : DeltaGeneratedSpace (Σ i, X i) :=
  .iSup fun _ ↦ .coinduced _