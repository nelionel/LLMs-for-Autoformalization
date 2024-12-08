import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.PiSystem
assert_not_exists MeasureTheory.Measure
noncomputable section
open Set MeasurableSpace
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
theorem generateFrom_prod_eq {α β} {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) :
    @Prod.instMeasurableSpace _ _ (generateFrom C) (generateFrom D) =
      generateFrom (image2 (· ×ˢ ·) C D) := by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [comap_generateFrom] <;> apply generateFrom_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ, ← h2t, prod_iUnion]
      apply MeasurableSet.iUnion
      intro n
      apply measurableSet_generateFrom
      exact ⟨s, hs, t n, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod, ← h2t, iUnion_prod_const]
      apply MeasurableSet.iUnion
      rintro n
      apply measurableSet_generateFrom
      exact mem_image2_of_mem (h1t n) hs
  · apply generateFrom_le
    rintro _ ⟨s, hs, t, ht, rfl⟩
    dsimp only
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurableSet_generateFrom hs
    · exact measurableSet_generateFrom ht
theorem generateFrom_eq_prod {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom C = ‹_›)
    (hD : generateFrom D = ‹_›) (h2C : IsCountablySpanning C) (h2D : IsCountablySpanning D) :
    generateFrom (image2 (· ×ˢ ·) C D) = Prod.instMeasurableSpace := by
  rw [← hC, ← hD, generateFrom_prod_eq h2C h2D]
lemma generateFrom_prod :
    generateFrom (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) =
      Prod.instMeasurableSpace :=
  generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet
lemma isPiSystem_prod :
    IsPiSystem (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) :=
  isPiSystem_measurableSet.prod isPiSystem_measurableSet
lemma MeasurableEmbedding.prod_mk {α β γ δ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : α → β}
    {g : γ → δ} (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding fun x : γ × α => (g x.1, f x.2) := by
  have h_inj : Function.Injective fun x : γ × α => (g x.fst, f x.snd) := by
    intro x y hxy
    rw [← @Prod.mk.eta _ _ x, ← @Prod.mk.eta _ _ y]
    simp only [Prod.mk.inj_iff] at hxy ⊢
    exact ⟨hg.injective hxy.1, hf.injective hxy.2⟩
  refine ⟨h_inj, ?_, ?_⟩
  · exact (hg.measurable.comp measurable_fst).prod_mk (hf.measurable.comp measurable_snd)
  · 
    refine fun s hs =>
      @MeasurableSpace.induction_on_inter _
        (fun s => MeasurableSet ((fun x : γ × α => (g x.fst, f x.snd)) '' s)) _ _
        generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ _ hs
    · simp only [Set.image_empty, MeasurableSet.empty]
    · rintro t ⟨t₁, ht₁, t₂, ht₂, rfl⟩
      rw [← Set.prod_image_image_eq]
      exact (hg.measurableSet_image.mpr ht₁).prod (hf.measurableSet_image.mpr ht₂)
    · intro t _ ht_m
      rw [← Set.range_diff_image h_inj, ← Set.prod_range_range_eq]
      exact
        MeasurableSet.diff (MeasurableSet.prod hg.measurableSet_range hf.measurableSet_range) ht_m
    · intro g _ _ hg
      simp_rw [Set.image_iUnion]
      exact MeasurableSet.iUnion hg
lemma MeasurableEmbedding.prod_mk_left {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    (x : α) {f : γ → β} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (fun y ↦ (x, f y)) where
  injective := by
    intro y y'
    simp only [Prod.mk.injEq, true_and]
    exact fun h ↦ hf.injective h
  measurable := Measurable.prod_mk measurable_const hf.measurable
  measurableSet_image' := by
    intro s hs
    convert (MeasurableSet.singleton x).prod (hf.measurableSet_image.mpr hs)
    ext x
    simp
lemma measurableEmbedding_prod_mk_left [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (Prod.mk x : β → α × β) :=
  MeasurableEmbedding.prod_mk_left x MeasurableEmbedding.id
lemma MeasurableEmbedding.prod_mk_right {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {f : γ → β} (hf : MeasurableEmbedding f) (x : α) :
    MeasurableEmbedding (fun y ↦ (f y, x)) where
  injective := by
    intro y y'
    simp only [Prod.mk.injEq, and_true]
    exact fun h ↦ hf.injective h
  measurable := Measurable.prod_mk hf.measurable measurable_const
  measurableSet_image' := by
    intro s hs
    convert (hf.measurableSet_image.mpr hs).prod (MeasurableSet.singleton x)
    ext x
    simp
lemma measurableEmbedding_prod_mk_right [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (fun y ↦ (y, x) : β → β × α) :=
  MeasurableEmbedding.prod_mk_right MeasurableEmbedding.id x