import Mathlib.Topology.PartialHomeomorph
noncomputable section
open TopologicalSpace Topology
universe u
variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}
scoped[Manifold] infixr:100 " ≫ₕ " => PartialHomeomorph.trans
scoped[Manifold] infixr:100 " ≫ " => PartialEquiv.trans
open Set PartialHomeomorph Manifold  
section Groupoid
structure StructureGroupoid (H : Type u) [TopologicalSpace H] where
  members : Set (PartialHomeomorph H H)
  trans' : ∀ e e' : PartialHomeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members
  symm' : ∀ e : PartialHomeomorph H H, e ∈ members → e.symm ∈ members
  id_mem' : PartialHomeomorph.refl H ∈ members
  locality' : ∀ e : PartialHomeomorph H H,
    (∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ members) → e ∈ members
  mem_of_eqOnSource' : ∀ e e' : PartialHomeomorph H H, e ∈ members → e' ≈ e → e' ∈ members
variable [TopologicalSpace H]
instance : Membership (PartialHomeomorph H H) (StructureGroupoid H) :=
  ⟨fun (G : StructureGroupoid H) (e : PartialHomeomorph H H) ↦ e ∈ G.members⟩
instance (H : Type u) [TopologicalSpace H] :
    SetLike (StructureGroupoid H) (PartialHomeomorph H H) where
  coe s := s.members
  coe_injective' N O h := by cases N; cases O; congr
instance : Min (StructureGroupoid H) :=
  ⟨fun G G' => StructureGroupoid.mk
    (members := G.members ∩ G'.members)
    (trans' := fun e e' he he' =>
      ⟨G.trans' e e' he.left he'.left, G'.trans' e e' he.right he'.right⟩)
    (symm' := fun e he => ⟨G.symm' e he.left, G'.symm' e he.right⟩)
    (id_mem' := ⟨G.id_mem', G'.id_mem'⟩)
    (locality' := by
      intro e hx
      apply (mem_inter_iff e G.members G'.members).mpr
      refine And.intro (G.locality' e ?_) (G'.locality' e ?_)
      all_goals
        intro x hex
        rcases hx x hex with ⟨s, hs⟩
        use s
        refine And.intro hs.left (And.intro hs.right.left ?_)
      · exact hs.right.right.left
      · exact hs.right.right.right)
    (mem_of_eqOnSource' := fun e e' he hee' =>
      ⟨G.mem_of_eqOnSource' e e' he.left hee', G'.mem_of_eqOnSource' e e' he.right hee'⟩)⟩
instance : InfSet (StructureGroupoid H) :=
  ⟨fun S => StructureGroupoid.mk
    (members := ⋂ s ∈ S, s.members)
    (trans' := by
      simp only [mem_iInter]
      intro e e' he he' i hi
      exact i.trans' e e' (he i hi) (he' i hi))
    (symm' := by
      simp only [mem_iInter]
      intro e he i hi
      exact i.symm' e (he i hi))
    (id_mem' := by
      simp only [mem_iInter]
      intro i _
      exact i.id_mem')
    (locality' := by
      simp only [mem_iInter]
      intro e he i hi
      refine i.locality' e ?_
      intro x hex
      rcases he x hex with ⟨s, hs⟩
      exact ⟨s, ⟨hs.left, ⟨hs.right.left, hs.right.right i hi⟩⟩⟩)
    (mem_of_eqOnSource' := by
      simp only [mem_iInter]
      intro e e' he he'e
      exact fun i hi => i.mem_of_eqOnSource' e e' (he i hi) he'e)⟩
theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : PartialHomeomorph H H}
    (he : e ∈ G) (he' : e' ∈ G) : e ≫ₕ e' ∈ G :=
  G.trans' e e' he he'
theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : PartialHomeomorph H H} (he : e ∈ G) :
    e.symm ∈ G :=
  G.symm' e he
theorem StructureGroupoid.id_mem (G : StructureGroupoid H) : PartialHomeomorph.refl H ∈ G :=
  G.id_mem'
theorem StructureGroupoid.locality (G : StructureGroupoid H) {e : PartialHomeomorph H H}
    (h : ∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ G) : e ∈ G :=
  G.locality' e h
theorem StructureGroupoid.mem_of_eqOnSource (G : StructureGroupoid H) {e e' : PartialHomeomorph H H}
    (he : e ∈ G) (h : e' ≈ e) : e' ∈ G :=
  G.mem_of_eqOnSource' e e' he h
theorem StructureGroupoid.mem_iff_of_eqOnSource {G : StructureGroupoid H}
    {e e' : PartialHomeomorph H H} (h : e ≈ e') : e ∈ G ↔ e' ∈ G :=
  ⟨fun he ↦ G.mem_of_eqOnSource he (Setoid.symm h), fun he' ↦ G.mem_of_eqOnSource he' h⟩
instance StructureGroupoid.partialOrder : PartialOrder (StructureGroupoid H) :=
  PartialOrder.lift StructureGroupoid.members fun a b h ↦ by
    cases a
    cases b
    dsimp at h
    induction h
    rfl
theorem StructureGroupoid.le_iff {G₁ G₂ : StructureGroupoid H} : G₁ ≤ G₂ ↔ ∀ e, e ∈ G₁ → e ∈ G₂ :=
  Iff.rfl
def idGroupoid (H : Type u) [TopologicalSpace H] : StructureGroupoid H where
  members := {PartialHomeomorph.refl H} ∪ { e : PartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    cases' he with he he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ e' ∈ { e : PartialHomeomorph H H | e.source = ∅ } := eq_bot_iff.2 this
      exact (mem_union _ _ _).2 (Or.inr this)
  symm' e he := by
    cases' (mem_union _ _ _).1 he with E E
    · simp [mem_singleton_iff.mp E]
    · right
      simpa only [e.toPartialEquiv.image_source_eq_target.symm, mfld_simps] using E
  id_mem' := mem_union_left _ rfl
  locality' e he := by
    rcases e.source.eq_empty_or_nonempty with h | h
    · right
      exact h
    · left
      rcases h with ⟨x, hx⟩
      rcases he x hx with ⟨s, open_s, xs, hs⟩
      have x's : x ∈ (e.restr s).source := by
        rw [restr_source, open_s.interior_eq]
        exact ⟨hx, xs⟩
      cases' hs with hs hs
      · replace hs : PartialHomeomorph.restr e s = PartialHomeomorph.refl H := by
          simpa only using hs
        have : (e.restr s).source = univ := by
          rw [hs]
          simp
        have : e.toPartialEquiv.source ∩ interior s = univ := this
        have : univ ⊆ interior s := by
          rw [← this]
          exact inter_subset_right
        have : s = univ := by rwa [open_s.interior_eq, univ_subset_iff] at this
        simpa only [this, restr_univ] using hs
      · exfalso
        rw [mem_setOf_eq] at hs
        rwa [hs] at x's
  mem_of_eqOnSource' e e' he he'e := by
    cases' he with he he
    · left
      have : e = e' := by
        refine eq_of_eqOnSource_univ (Setoid.symm he'e) ?_ ?_ <;>
          rw [Set.mem_singleton_iff.1 he] <;> rfl
      rwa [← this]
    · right
      have he : e.toPartialEquiv.source = ∅ := he
      rwa [Set.mem_setOf_eq, EqOnSource.source_eq he'e]
instance instStructureGroupoidOrderBot : OrderBot (StructureGroupoid H) where
  bot := idGroupoid H
  bot_le := by
    intro u f hf
    have hf : f ∈ {PartialHomeomorph.refl H} ∪ { e : PartialHomeomorph H H | e.source = ∅ } := hf
    simp only [singleton_union, mem_setOf_eq, mem_insert_iff] at hf
    cases' hf with hf hf
    · rw [hf]
      apply u.id_mem
    · apply u.locality
      intro x hx
      rw [hf, mem_empty_iff_false] at hx
      exact hx.elim
instance : Inhabited (StructureGroupoid H) := ⟨idGroupoid H⟩
structure Pregroupoid (H : Type*) [TopologicalSpace H] where
  property : (H → H) → Set H → Prop
  comp : ∀ {f g u v}, property f u → property g v →
    IsOpen u → IsOpen v → IsOpen (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  id_mem : property id univ
  locality :
    ∀ {f u}, IsOpen u → (∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u
  congr : ∀ {f g : H → H} {u}, IsOpen u → (∀ x ∈ u, g x = f x) → property f u → property g u
def Pregroupoid.groupoid (PG : Pregroupoid H) : StructureGroupoid H where
  members := { e : PartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.2 he.2 e'.open_target e.open_target
      apply e'.continuousOn_invFun.isOpen_inter_preimage e'.open_target e.open_target
  symm' _ he := ⟨he.2, he.1⟩
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩
  locality' e he := by
    constructor
    · refine PG.locality e.open_source fun x xu ↦ ?_
      rcases he x xu with ⟨s, s_open, xs, hs⟩
      refine ⟨s, s_open, xs, ?_⟩
      convert hs.1 using 1
      dsimp [PartialHomeomorph.restr]
      rw [s_open.interior_eq]
    · refine PG.locality e.open_target fun x xu ↦ ?_
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩
      refine ⟨e.target ∩ e.symm ⁻¹' s, ?_, ⟨xu, xs⟩, ?_⟩
      · exact ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target s_open
      · rw [← inter_assoc, inter_self]
        convert hs.2 using 1
        dsimp [PartialHomeomorph.restr]
        rw [s_open.interior_eq]
  mem_of_eqOnSource' e e' he ee' := by
    constructor
    · apply PG.congr e'.open_source ee'.2
      simp only [ee'.1, he.1]
    · have A := EqOnSource.symm' ee'
      apply PG.congr e'.symm.open_source A.2
      rw [A.1, symm_toPartialEquiv, PartialEquiv.symm_source]
      exact he.2
theorem mem_groupoid_of_pregroupoid {PG : Pregroupoid H} {e : PartialHomeomorph H H} :
    e ∈ PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
  Iff.rfl
theorem groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregroupoid H)
    (h : ∀ f s, PG₁.property f s → PG₂.property f s) : PG₁.groupoid ≤ PG₂.groupoid := by
  refine StructureGroupoid.le_iff.2 fun e he ↦ ?_
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩
theorem mem_pregroupoid_of_eqOnSource (PG : Pregroupoid H) {e e' : PartialHomeomorph H H}
    (he' : e ≈ e') (he : PG.property e e.source) : PG.property e' e'.source := by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he
abbrev continuousPregroupoid (H : Type*) [TopologicalSpace H] : Pregroupoid H where
  property _ _ := True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial
instance (H : Type*) [TopologicalSpace H] : Inhabited (Pregroupoid H) :=
  ⟨continuousPregroupoid H⟩
def continuousGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)
instance instStructureGroupoidOrderTop : OrderTop (StructureGroupoid H) where
  top := continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩
instance : CompleteLattice (StructureGroupoid H) :=
  { SetLike.instPartialOrder,
    completeLatticeOfInf _ (by
      exact fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_le
    top := instStructureGroupoidOrderTop.top
    le_top := instStructureGroupoidOrderTop.le_top
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }
class ClosedUnderRestriction (G : StructureGroupoid H) : Prop where
  closedUnderRestriction :
    ∀ {e : PartialHomeomorph H H}, e ∈ G → ∀ s : Set H, IsOpen s → e.restr s ∈ G
theorem closedUnderRestriction' {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e : PartialHomeomorph H H} (he : e ∈ G) {s : Set H} (hs : IsOpen s) : e.restr s ∈ G :=
  ClosedUnderRestriction.closedUnderRestriction he s hs
def idRestrGroupoid : StructureGroupoid H where
  members := { e | ∃ (s : Set H) (h : IsOpen s), e ≈ PartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s ∩ s', hs.inter hs', ?_⟩
    have := PartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [PartialHomeomorph.ofSet_trans_ofSet] at this
  symm' := by
    rintro e ⟨s, hs, hse⟩
    refine ⟨s, hs, ?_⟩
    rw [← ofSet_symm]
    exact PartialHomeomorph.EqOnSource.symm' hse
  id_mem' := ⟨univ, isOpen_univ, by simp only [mfld_simps, refl]⟩
  locality' := by
    intro e h
    refine ⟨e.source, e.open_source, by simp only [mfld_simps], ?_⟩
    intro x hx
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩
    have hes : x ∈ (e.restr s).source := by
      rw [e.restr_source]
      refine ⟨hx, ?_⟩
      rw [hs.interior_eq]
      exact hxs
    simpa only [mfld_simps] using PartialHomeomorph.EqOnSource.eqOn hes' hes
  mem_of_eqOnSource' := by
    rintro e e' ⟨s, hs, hse⟩ hee'
    exact ⟨s, hs, Setoid.trans hee' hse⟩
theorem idRestrGroupoid_mem {s : Set H} (hs : IsOpen s) : ofSet s hs ∈ @idRestrGroupoid H _ :=
  ⟨s, hs, refl _⟩
instance closedUnderRestriction_idRestrGroupoid : ClosedUnderRestriction (@idRestrGroupoid H _) :=
  ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' ∩ s, hs'.inter hs
    refine Setoid.trans (PartialHomeomorph.EqOnSource.restr he s) ?_
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩
theorem closedUnderRestriction_iff_id_le (G : StructureGroupoid H) :
    ClosedUnderRestriction G ↔ idRestrGroupoid ≤ G := by
  constructor
  · intro _i
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    refine G.mem_of_eqOnSource ?_ hes
    convert closedUnderRestriction' G.id_mem hs
    ext
    · rw [PartialHomeomorph.restr_apply, PartialHomeomorph.refl_apply, id, ofSet_apply, id_eq]
    · simp [hs]
    · simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : PartialHomeomorph H H) hs]
    refine G.trans ?_ he
    apply StructureGroupoid.le_iff.mp h
    exact idRestrGroupoid_mem hs
instance : ClosedUnderRestriction (continuousGroupoid H) :=
  (closedUnderRestriction_iff_id_le _).mpr le_top
end Groupoid
@[ext]
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  protected atlas : Set (PartialHomeomorph M H)
  protected chartAt : M → PartialHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas
abbrev atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Set (PartialHomeomorph M H) :=
  ChartedSpace.atlas
abbrev chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : PartialHomeomorph M H :=
  ChartedSpace.chartAt x
@[simp, mfld_simps]
lemma mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source :=
  ChartedSpace.mem_chart_source x
@[simp, mfld_simps]
lemma chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : chartAt H x ∈ atlas H M :=
  ChartedSpace.chart_mem_atlas x
section ChartedSpace
def ChartedSpace.empty (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [IsEmpty M] : ChartedSpace H M where
  atlas := ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim
instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
  atlas := {PartialHomeomorph.refl H}
  chartAt _ := PartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _
@[simp, mfld_simps]
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : PartialHomeomorph H H} :
    e ∈ atlas H H ↔ e = PartialHomeomorph.refl H :=
  Iff.rfl
theorem chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} :
    chartAt H x = PartialHomeomorph.refl H := rfl
section
variable (H) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
theorem mem_chart_target (x : M) : chartAt H x x ∈ (chartAt H x).target :=
  (chartAt H x).map_source (mem_chart_source _ _)
theorem chart_source_mem_nhds (x : M) : (chartAt H x).source ∈ 𝓝 x :=
  (chartAt H x).open_source.mem_nhds <| mem_chart_source H x
theorem chart_target_mem_nhds (x : M) : (chartAt H x).target ∈ 𝓝 (chartAt H x x) :=
  (chartAt H x).open_target.mem_nhds <| mem_chart_target H x
variable (M) in
@[simp]
theorem iUnion_source_chartAt : (⋃ x : M, (chartAt H x).source) = (univ : Set M) :=
  eq_univ_iff_forall.mpr fun x ↦ mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
theorem ChartedSpace.isOpen_iff (s : Set M) :
    IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s) := by
  rw [isOpen_iff_of_cover (fun i ↦ (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]
def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩
theorem achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl
@[simp, mfld_simps]
theorem coe_achart (x : M) : (achart H x : PartialHomeomorph M H) = chartAt H x :=
  rfl
@[simp, mfld_simps]
theorem achart_val (x : M) : (achart H x).1 = chartAt H x :=
  rfl
theorem mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
  mem_chart_source H x
open TopologicalSpace
theorem ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H] {s : Set M}
    (hs : ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ) (hsc : s.Countable) :
    SecondCountableTopology M := by
  haveI : ∀ x : M, SecondCountableTopology (chartAt H x).source :=
    fun x ↦ (chartAt (H := H) x).secondCountableTopology_source
  haveI := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s ↦ (chartAt H (x : M)).open_source) hs
variable (M)
theorem ChartedSpace.secondCountable_of_sigmaCompact [SecondCountableTopology H]
    [SigmaCompactSpace M] : SecondCountableTopology M := by
  obtain ⟨s, hsc, hsU⟩ : ∃ s, Set.Countable s ∧ ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M ↦ chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc
@[deprecated (since := "2024-11-13")] alias
ChartedSpace.secondCountable_of_sigma_compact := ChartedSpace.secondCountable_of_sigmaCompact
theorem ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactSpace M := by
  have : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s ⊆ (chartAt H x).target)
      fun s ↦ (chartAt H x).symm '' s := fun x ↦ by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((chartAt H x).continuousOn_symm.mono h₃)
theorem ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConnectedSpace M := by
  let e : M → PartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s ↦ (e x).symm '' s)
      (fun x s ↦ (IsOpen s ∧ e x x ∈ s ∧ IsConnected s) ∧ s ⊆ (e x).target) ?_ ?_
  · intro x
    simpa only [e, PartialHomeomorph.symm_map_nhds_eq, mem_chart_source] using
      ((LocallyConnectedSpace.open_connected_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target H x))).map (e x).symm
  · rintro x s ⟨⟨-, -, hsconn⟩, hssubset⟩
    exact hsconn.isPreconnected.image _ ((e x).continuousOn_symm.mono hssubset)
def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 PartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩
theorem chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] (x : M) :
    (letI := ChartedSpace.comp H H' M; chartAt H x) = chartAt H' x ≫ₕ chartAt H (chartAt H' x x) :=
  rfl
theorem ChartedSpace.t1Space [T1Space H] : T1Space M := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  by_cases hy : y ∈ (chartAt H x).source
  · refine ⟨(chartAt H x).source ∩ (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact PartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_compl, mem_inter_iff, mem_chart_source, mem_compl_iff, mem_preimage,
        mem_singleton_iff, true_and]
      exact (chartAt H x).injOn.ne (ChartedSpace.mem_chart_source x) hy hxy
  · exact ⟨(chartAt H x).source, (chartAt H x).open_source, ChartedSpace.mem_chart_source x, hy⟩
end
library_note "Manifold type tags" 
def ModelProd (H : Type*) (H' : Type*) :=
  H × H'
def ModelPi {ι : Type*} (H : ι → Type*) :=
  ∀ i, H i
section
instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
  instInhabitedProd
instance (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H'] :
    TopologicalSpace (ModelProd H H') :=
  instTopologicalSpaceProd
@[simp, mfld_simps, nolint simpNF]
theorem modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
    (range fun p : ModelProd H H' ↦ (f p.1, p.2)) = range f ×ˢ (univ : Set H') := by
  rw [prod_range_univ_eq]
  rfl
end
section
variable {ι : Type*} {Hi : ι → Type*}
instance modelPiInhabited [∀ i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
  Pi.instInhabited
instance [∀ i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
  Pi.topologicalSpace
end
instance prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [TopologicalSpace M']
    [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') where
  atlas := image2 PartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)
section prodChartedSpace
@[ext]
theorem ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
  Prod.ext h₁ h₂
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {x : M × M'}
@[simp, mfld_simps]
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) :=
  rfl
theorem chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H × H') := by
  ext1
  · simp [prodChartedSpace, atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl
end prodChartedSpace
instance piChartedSpace {ι : Type*} [Finite ι] (H : ι → Type*) [∀ i, TopologicalSpace (H i)]
    (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] :
    ChartedSpace (ModelPi H) (∀ i, M i) where
  atlas := PartialHomeomorph.pi '' Set.pi univ fun _ ↦ atlas (H _) (M _)
  chartAt f := PartialHomeomorph.pi fun i ↦ chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ ↦ chart_mem_atlas (H i) (f i)
@[simp, mfld_simps]
theorem piChartedSpace_chartAt {ι : Type*} [Finite ι] (H : ι → Type*)
    [∀ i, TopologicalSpace (H i)] (M : ι → Type*) [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (H i) (M i)] (f : ∀ i, M i) :
    chartAt (H := ModelPi H) f = PartialHomeomorph.pi fun i ↦ chartAt (H i) (f i) :=
  rfl
end ChartedSpace
structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  atlas : Set (PartialEquiv M H)
  chartAt : M → PartialEquiv M H
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas
  open_source : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').source
  continuousOn_toFun : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas →
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source
namespace ChartedSpaceCore
variable [TopologicalSpace H] (c : ChartedSpaceCore H M) {e : PartialEquiv M H}
protected def toTopologicalSpace : TopologicalSpace M :=
  TopologicalSpace.generateFrom <|
    ⋃ (e : PartialEquiv M H) (_ : e ∈ c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s ∩ e.source}
theorem open_source' (he : e ∈ c.atlas) : IsOpen[c.toTopologicalSpace] e.source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]
theorem open_target (he : e ∈ c.atlas) : IsOpen e.target := by
  have E : e.target ∩ e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx ↦
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he
protected def partialHomeomorph (e : PartialEquiv M H) (he : e ∈ c.atlas) :
    @PartialHomeomorph M H c.toTopologicalSpace _ :=
  { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert c.open_source' he
    open_target := by convert c.open_target he
    continuousOn_toFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
      rw [inter_comm]
      apply TopologicalSpace.GenerateOpen.basic
      simp only [exists_prop, mem_iUnion, mem_singleton_iff]
      exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
    continuousOn_invFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      apply continuousOn_isOpen_of_generateFrom
      intro t ht
      simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
      rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩
      rw [ts]
      let f := e.symm.trans e'
      have : IsOpen (f ⁻¹' s ∩ f.source) := by
        simpa [f, inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuousOn_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
          e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc, ← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [f, PartialEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e ∈ c.atlas), {c.partialHomeomorph e he}
    chartAt := fun x ↦ c.partialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}
end ChartedSpaceCore
section HasGroupoid
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible : ∀ {e e' : PartialHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G
theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : PartialHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) : e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible he he'
theorem hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ ≤ G₂) :
    HasGroupoid M G₂ :=
  ⟨fun he he' ↦ hle (h.compatible he he')⟩
theorem hasGroupoid_inf_iff {G₁ G₂ : StructureGroupoid H} : HasGroupoid M (G₁ ⊓ G₂) ↔
    HasGroupoid M G₁ ∧ HasGroupoid M G₂ :=
  ⟨(fun h ↦ ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ ↦ { compatible := fun he he' ↦ ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩
theorem hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : ∀ {e e' : PartialHomeomorph M H},
    e ∈ atlas H M → e' ∈ atlas H M → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    HasGroupoid M PG.groupoid :=
  ⟨fun he he' ↦ mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩
instance hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H) :
    HasGroupoid H G where
  compatible {e e'} he he' := by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]
instance hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H) := by
  refine ⟨fun _ _ ↦ ?_⟩
  rw [continuousGroupoid, mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]
theorem StructureGroupoid.trans_restricted {e e' : PartialHomeomorph M H} {G : StructureGroupoid H}
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] {s : Opens M} (hs : Nonempty s) :
    (e.subtypeRestr hs).symm ≫ₕ e'.subtypeRestr hs ∈ G :=
  G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')
section MaximalAtlas
variable (G : StructureGroupoid H)
variable (M) in
def StructureGroupoid.maximalAtlas : Set (PartialHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }
theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M ⊆ G.maximalAtlas M :=
  fun _ he _ he' ↦ ⟨G.compatible he he', G.compatible he' he⟩
theorem StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) :
    chartAt H x ∈ G.maximalAtlas M :=
  G.subset_maximalAtlas (chart_mem_atlas H x)
variable {G}
theorem mem_maximalAtlas_iff {e : PartialHomeomorph M H} :
    e ∈ G.maximalAtlas M ↔ ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G :=
  Iff.rfl
theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : PartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) (he' : e' ∈ G.maximalAtlas M) : e.symm ≫ₕ e' ∈ G := by
  refine G.locality fun x hx ↦ ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target ∩ e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x ∈ s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f ∈ G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ∈ G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)
open PartialHomeomorph in
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : PartialHomeomorph M H} (h : e' ≈ e)
    (he : e ∈ G.maximalAtlas M) : e' ∈ G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩
variable (G)
theorem StructureGroupoid.id_mem_maximalAtlas : PartialHomeomorph.refl H ∈ G.maximalAtlas H :=
  G.subset_maximalAtlas <| by simp
theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : PartialHomeomorph H H}
    (hf : f ∈ G) : f ∈ G.maximalAtlas H := by
  rintro e (rfl : e = PartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩
end MaximalAtlas
section Singleton
variable {α : Type*} [TopologicalSpace α]
namespace PartialHomeomorph
variable (e : PartialHomeomorph α H)
def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto
@[simp, mfld_simps]
theorem singletonChartedSpace_chartAt_eq (h : e.source = Set.univ) {x : α} :
    @chartAt H _ α _ (e.singletonChartedSpace h) x = e :=
  rfl
theorem singletonChartedSpace_chartAt_source (h : e.source = Set.univ) {x : α} :
    (@chartAt H _ α _ (e.singletonChartedSpace h) x).source = Set.univ :=
  h
theorem singletonChartedSpace_mem_atlas_eq (h : e.source = Set.univ) (e' : PartialHomeomorph α H)
    (h' : e' ∈ (e.singletonChartedSpace h).atlas) : e' = e :=
  h'
theorem singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G :=
  { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he',
        e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine G.mem_of_eqOnSource ?_ e.symm_trans_self
      have hle : idRestrGroupoid ≤ G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }
end PartialHomeomorph
namespace Topology.IsOpenEmbedding
variable [Nonempty α]
def singletonChartedSpace {f : α → H} (h : IsOpenEmbedding f) : ChartedSpace H α :=
  (h.toPartialHomeomorph f).singletonChartedSpace (toPartialHomeomorph_source _ _)
theorem singletonChartedSpace_chartAt_eq {f : α → H} (h : IsOpenEmbedding f) {x : α} :
    ⇑(@chartAt H _ α _ h.singletonChartedSpace x) = f :=
  rfl
theorem singleton_hasGroupoid {f : α → H} (h : IsOpenEmbedding f) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ h.singletonChartedSpace G :=
  (h.toPartialHomeomorph f).singleton_hasGroupoid (toPartialHomeomorph_source _ _) G
end Topology.IsOpenEmbedding
end Singleton
namespace TopologicalSpace.Opens
open TopologicalSpace
variable (G : StructureGroupoid H) [HasGroupoid M G]
variable (s : Opens M)
protected instance instChartedSpace : ChartedSpace H s where
  atlas := ⋃ x : s, {(chartAt H x.1).subtypeRestr ⟨x⟩}
  chartAt x := (chartAt H x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x
lemma chart_eq {s : Opens M} (hs : Nonempty s) {e : PartialHomeomorph s H} (he : e ∈ atlas H s) :
    ∃ x : s, e = (chartAt H (x : M)).subtypeRestr hs := by
  rcases he with ⟨xset, ⟨x, hx⟩, he⟩
  exact ⟨x, mem_singleton_iff.mp (by convert he)⟩
lemma chart_eq' {t : Opens H} (ht : Nonempty t) {e' : PartialHomeomorph t H}
    (he' : e' ∈ atlas H t) : ∃ x : t, e' = (chartAt H ↑x).subtypeRestr ht := by
  rcases he' with ⟨xset, ⟨x, hx⟩, he'⟩
  exact ⟨x, mem_singleton_iff.mp (by convert he')⟩
protected instance instHasGroupoid [ClosedUnderRestriction G] : HasGroupoid s G where
  compatible := by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    rw [hc.symm, mem_singleton_iff] at he
    rw [hc'.symm, mem_singleton_iff] at he'
    rw [he, he']
    refine G.mem_of_eqOnSource ?_
      (subtypeRestr_symm_trans_subtypeRestr (s := s) _ (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact isOpen_inter_preimage_symm (chartAt _ _) s.2
theorem chartAt_subtype_val_symm_eventuallyEq (U : Opens M) {x : U} :
    (chartAt H x.val).symm =ᶠ[𝓝 (chartAt H x.val x.val)] Subtype.val ∘ (chartAt H x).symm := by
  set e := chartAt H x.val
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target ∈ 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn ⟨x⟩)
theorem chartAt_inclusion_symm_eventuallyEq {U V : Opens M} (hUV : U ≤ V) {x : U} :
    (chartAt H (Opens.inclusion hUV x)).symm
    =ᶠ[𝓝 (chartAt H (Opens.inclusion hUV x) (Set.inclusion hUV x))]
    Opens.inclusion hUV ∘ (chartAt H x).symm := by
  set e := chartAt H (x : M)
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target ∈ 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds <| e.subtypeRestr_symm_eqOn_of_le ⟨x⟩
    ⟨Opens.inclusion hUV x⟩ hUV
end TopologicalSpace.Opens
lemma StructureGroupoid.restriction_in_maximalAtlas {e : PartialHomeomorph M H}
    (he : e ∈ atlas H M) {s : Opens M} (hs : Nonempty s) {G : StructureGroupoid H} [HasGroupoid M G]
    [ClosedUnderRestriction G] : e.subtypeRestr hs ∈ G.maximalAtlas s := by
  intro e' he'
  obtain ⟨x, this⟩ := Opens.chart_eq hs he'
  rw [this]
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) hs,
         G.trans_restricted (chart_mem_atlas H (x : M)) he hs⟩
structure Structomorph (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M'] extends Homeomorph M M' where
  mem_groupoid : ∀ c : PartialHomeomorph M H, ∀ c' : PartialHomeomorph M' H, c ∈ atlas H M →
    c' ∈ atlas H M' → c.symm ≫ₕ toHomeomorph.toPartialHomeomorph ≫ₕ c' ∈ G
variable [TopologicalSpace M'] [TopologicalSpace M''] {G : StructureGroupoid H} [ChartedSpace H M']
  [ChartedSpace H M'']
def Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' ↦ by
      change PartialHomeomorph.symm c ≫ₕ PartialHomeomorph.refl M ≫ₕ c' ∈ G
      rw [PartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }
def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
  { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toPartialHomeomorph ≫ₕ c).symm ∈ G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }
def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
    Structomorph G M M'' :=
  { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      intro c c' hc hc'
      refine G.locality fun x hx ↦ ?_
      let f₁ := e.toHomeomorph.toPartialHomeomorph
      let f₂ := e'.toHomeomorph.toPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toPartialHomeomorph _ _
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source ∩ c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x ∈ s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine ⟨s, open_s, this, ?_⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ ∈ G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s := by
          simp only [EqOnSource.restr, trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ ∈ G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }
theorem StructureGroupoid.restriction_mem_maximalAtlas_subtype
    {e : PartialHomeomorph M H} (he : e ∈ atlas H M)
    (hs : Nonempty e.source) [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s := { carrier := e.source, is_open' := e.open_source : Opens M }
    let t := { carrier := e.target, is_open' := e.open_target : Opens H }
    ∀ c' ∈ atlas H t, e.toHomeomorphSourceTarget.toPartialHomeomorph ≫ₕ c' ∈ G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := nonempty_coe_sort.mpr (e.mapsTo.nonempty (nonempty_coe_sort.mp hs))
  obtain ⟨x, hc'⟩ := Opens.chart_eq this hc'
  rw [hc', (chartAt_self_eq)]
  rw [PartialHomeomorph.subtypeRestr_def, PartialHomeomorph.trans_refl]
  let goal := e.toHomeomorphSourceTarget.toPartialHomeomorph ≫ₕ (t.partialHomeomorphSubtypeCoe this)
  have : goal ≈ e.subtypeRestr (s := s) hs :=
    (goal.eqOnSource_iff (e.subtypeRestr (s := s) hs)).mpr
      ⟨by
        simp only [trans_toPartialEquiv, PartialEquiv.trans_source,
          Homeomorph.toPartialHomeomorph_source, toFun_eq_coe, Homeomorph.toPartialHomeomorph_apply,
          Opens.partialHomeomorphSubtypeCoe_source, preimage_univ, inter_self, subtypeRestr_source,
          goal, s]
        exact Subtype.coe_preimage_self _ |>.symm, by intro _ _; rfl⟩
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.restriction_in_maximalAtlas he hs)
def PartialHomeomorph.toStructomorph {e : PartialHomeomorph M H} (he : e ∈ atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s : Opens M := { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases h : Nonempty e.source
  · exact { e.toHomeomorphSourceTarget with
      mem_groupoid :=
        fun c c' hc hc' ↦ G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_mem_maximalAtlas_subtype he h c' hc') }
  · have : IsEmpty s := not_nonempty_iff.mp h
    have : IsEmpty t := isEmpty_coe_sort.mpr
      (by convert e.image_source_eq_target ▸ image_eq_empty.mpr (isEmpty_coe_sort.mp this))
    exact { Homeomorph.empty with
      mem_groupoid := fun _ c' _ ⟨_, ⟨x, _⟩, _⟩ ↦ (this.false x).elim }
end HasGroupoid