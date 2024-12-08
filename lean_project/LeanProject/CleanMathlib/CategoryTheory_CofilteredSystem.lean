import Mathlib.Topology.Category.TopCat.Limits.Konig
universe u v w
open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes
section FiniteKonig
theorem nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : ∀ j, Finite (F.obj j)]
    [hne : ∀ j, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  haveI : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  haveI : ∀ j, Finite (F'.obj j) := hf
  haveI : ∀ j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u, hu⟩
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  haveI : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  cases isEmpty_or_nonempty J
  · fconstructor <;> apply isEmptyElim
  haveI : IsCofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [F', down, AsSmall.down, Functor.comp_map, uliftFunctor_map, Functor.op_map] at h
  simp_rw [← h]
theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Finite (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := by
  cases isEmpty_or_nonempty J
  · haveI : IsEmpty Jᵒᵖ := ⟨fun j => isEmptyElim j.unop⟩ 
    exact ⟨isEmptyElim, by apply isEmptyElim⟩
  · exact nonempty_sections_of_finite_cofiltered_system _
end FiniteKonig
namespace CategoryTheory
namespace Functor
variable {J : Type u} [Category J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)
theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_iInter₂
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
      ⟨fun h => (iInter₂_subset _ _).antisymm <| subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩
theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp_apply]⟩
theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp]
    apply range_comp_subset_range
theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩
@[simps]
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage, preimage_preimage, mem_preimage]
    convert h (g ≫ f); rw [F.map_comp]; rfl
  map_id j := by
    #adaptation_note 
    simp only [MapsTo.restrict, Subtype.map_def, F.map_id]
    ext
    rfl
  map_comp f g := by
    #adaptation_note 
    simp only [MapsTo.restrict, Subtype.map_def, F.map_comp]
    rfl
instance toPreimages_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite ((F.toPreimages s).obj j) :=
  fun _ => Subtype.finite
variable [IsCofilteredOrEmpty J]
theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← map_comp_apply, he, F.map_comp]
  exact ⟨_, rfl⟩
theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo'.1 (F.eventualRange_mapsTo f)
theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  rw [subset_antisymm_iff, eventualRange, and_iff_right (iInter₂_subset _ _), subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he, F.map_comp]
  apply range_comp_subset_range
theorem isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j),
    ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]
theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x ∈ F.eventualRange j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventualRange F (f₃ ≫ f₂) this
    refine ⟨⟨y, mem_iInter.2 fun g₂ => ?_⟩, Subtype.ext ?_⟩
    · obtain ⟨j₄, f₄, h₄⟩ := IsCofilteredOrEmpty.cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventualRange_iff.1 hy f₄
      rw [← map_comp_apply] at h₃
      rw [mem_preimage, ← map_comp_apply, h₄, ← Category.assoc, map_comp_apply, h₃,
        ← map_comp_apply]
      apply mem_iInter.1 hx
    · simp_rw [toPreimages_map, MapsTo.val_restrict_apply]
      rw [← Category.assoc, map_comp_apply, h₃, map_comp_apply]
theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _) (f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | ∃ (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (directedOn_range.mp <| F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ ?_ _ ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine (eq_of_le_of_not_lt hl ?_).ge
  have := hmin _ ⟨k', g', (m.finite_toSet.subset <| hm.substr hl).coe_toFinset⟩
  rwa [Finset.lt_iff_ssubset, ← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this
@[simps]
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := (F.eventualRange_mapsTo f).restrict _ _ _
  map_id i := by
    #adaptation_note 
    simp only [MapsTo.restrict, Subtype.map_def, F.map_id]
    ext
    rfl
  map_comp _ _ := by
    #adaptation_note 
    simp only [MapsTo.restrict, Subtype.map_def, F.map_comp]
    rfl
instance toEventualRanges_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite (F.toEventualRanges.obj j) :=
  fun _ => Subtype.finite
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections where
  toFun s := ⟨_, fun f => Subtype.coe_inj.2 <| s.prop f⟩
  invFun s :=
    ⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext <| s.prop f⟩
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    (F.toEventualRanges.map f).Surjective := fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) := by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj, h]
  infer_instance
theorem thin_diagram_of_surjective (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) {i j}
    (f g : i ⟶ j) : F.map f = F.map g :=
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  (Fsur φ).injective_comp_right <| by simp_rw [← types_comp, ← F.map_comp, hφ]
theorem toPreimages_nonempty_of_surjective [hFn : ∀ j : J, Nonempty (F.obj j)]
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) := by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩
theorem eval_section_injective_of_eventually_injective {j}
    (Finj : ∀ (i) (f : i ⟶ j), (F.map f).Injective) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective := by
  refine fun s₀ s₁ h => Subtype.ext <| funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f), ← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk, ← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)
section FiniteCofilteredSystem
variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective)
include Fsur
theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  haveI := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using h jk⟩, ?_⟩
  · have := (sec i).prop
    simp only [mem_iInter, mem_preimage, mem_singleton_iff] at this
    have := this (𝟙 i)
    rwa [map_id_apply] at this
theorem eventually_injective [Nonempty J] [Finite F.sections] :
    ∃ j, ∀ (i) (f : i ⟶ j), (F.map f).Injective := by
  haveI : ∀ j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  haveI : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : ∀ j, Fintype.card (F.obj j) ≤ Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  refine ⟨fn.argmin Nat.lt_wfRel.wf,
    fun i f => ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨Fsur f, le_antisymm ?_ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_le_sub_iff_left (card_le i)]
  apply fn.argmin_le
end FiniteCofilteredSystem
end Functor
end CategoryTheory