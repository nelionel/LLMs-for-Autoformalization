import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Sets.Opens
open Function Set Filter Topology
variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']
structure PartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
  [TopologicalSpace Y] extends PartialEquiv X Y where
  open_source : IsOpen source
  open_target : IsOpen target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target
namespace PartialHomeomorph
variable (e : PartialHomeomorph X Y)
section Basic
@[coe] def toFun' : X → Y := e.toFun
instance : CoeFun (PartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩
@[symm]
protected def symm : PartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  open_source := e.open_target
  open_target := e.open_source
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun
def Simps.apply (e : PartialHomeomorph X Y) : X → Y := e
def Simps.symm_apply (e : PartialHomeomorph X Y) : Y → X := e.symm
initialize_simps_projections PartialHomeomorph (toFun → apply, invFun → symm_apply)
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun
@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv X Y) (a b c d) : (PartialHomeomorph.mk e a b c d : X → Y) = e :=
  rfl
@[simp, mfld_simps]
theorem mk_coe_symm (e : PartialEquiv X Y) (a b c d) :
    ((PartialHomeomorph.mk e a b c d).symm : Y → X) = e.symm :=
  rfl
theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : PartialHomeomorph X Y → PartialEquiv X Y)
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl
@[simp, mfld_simps]
theorem toFun_eq_coe (e : PartialHomeomorph X Y) : e.toFun = e :=
  rfl
@[simp, mfld_simps]
theorem invFun_eq_coe (e : PartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl
@[simp, mfld_simps]
theorem coe_coe : (e.toPartialEquiv : X → Y) = e :=
  rfl
@[simp, mfld_simps]
theorem coe_coe_symm : (e.toPartialEquiv.symm : Y → X) = e.symm :=
  rfl
@[simp, mfld_simps]
theorem map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)
@[simp, mfld_simps]
theorem map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
@[simp, mfld_simps]
theorem left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
@[simp, mfld_simps]
theorem right_inv {x : Y} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
theorem eq_symm_apply {x : X} {y : Y} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn
end Basic
@[simps! (config := .asFn) apply symm_apply toPartialEquiv,
  simps! (config := .lemmasOnly) source target]
def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn
@[simps! (config := mfld_cfg)]
def _root_.Homeomorph.toPartialHomeomorph (e : X ≃ₜ Y) : PartialHomeomorph X Y :=
  e.toPartialHomeomorphOfImageEq univ isOpen_univ univ <| by rw [image_univ, e.surjective.range_eq]
def replaceEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y) (h : e.toPartialEquiv = e') :
    PartialHomeomorph X Y where
  toPartialEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun
theorem replaceEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl
theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
theorem eventually_left_inverse {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
theorem eventually_left_inverse' {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
theorem eventually_right_inverse {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
theorem eventually_right_inverse' {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
theorem eventually_ne_nhdsWithin {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set X) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set Y) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s
theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h
theorem image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s
theorem image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s
theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s
theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s
theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
@[ext]
protected theorem ext (e' : PartialHomeomorph X Y) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)
@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl
theorem symm_source : e.symm.source = e.target :=
  rfl
theorem symm_target : e.symm.target = e.source :=
  rfl
@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl
theorem symm_bijective : Function.Bijective
    (PartialHomeomorph.symm : PartialHomeomorph X Y → PartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
protected theorem continuousAt {x : X} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)
theorem continuousAt_symm {x : Y} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h
theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)
theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.continuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set X} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
theorem map_nhdsWithin_eq {x} (hx : x ∈ e.source) (s : Set X) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt
theorem map_nhdsWithin_preimage_eq {x} (hx : x ∈ e.source) (s : Set Y) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhdsWithin_target_inter (e.map_source hx)]
theorem eventually_nhds {x : X} (p : Y → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
theorem eventually_nhds' {x : X} (p : X → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]
theorem eventually_nhdsWithin {x : X} (p : Y → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.nhdsWithin_target_inter (e.mapsTo hx)]
theorem eventually_nhdsWithin' {x : X} (p : X → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
  refine eventually_congr <|
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : PartialHomeomorph X Y} {s : Set X}
    {t : Set Z} {x : X} {f : X → Z} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set Y) := by
  rw [eventuallyEq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
theorem isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs
theorem isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs
lemma isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s ⊆ e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs
theorem isOpen_image_source_inter {s : Set X} (hs : IsOpen s) :
    IsOpen (e '' (e.source ∩ s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left
lemma isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)
lemma isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t ⊆ e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'
theorem isOpen_image_iff_of_subset_source {s : Set X} (hs : s ⊆ e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs, e.symm_symm]
section IsImage
def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
namespace IsImage
variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}
theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm
theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq
alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'
theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
theorem leftInvOn_piecewise {e' : PartialHomeomorph X Y} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'
theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
theorem symm_eqOn_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx, h.image_eq, e.nhdsWithin_target_inter (e.map_source hx)]
protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]
protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior
theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩
@[simps toPartialEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : PartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left
end IsImage
theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target
theorem isImage_source_target_of_disjoint (e' : PartialHomeomorph X Y)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht
theorem preimage_interior (s : Set Y) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
theorem preimage_closure (s : Set Y) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
theorem preimage_frontier (s : Set Y) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
end IsImage
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : PartialHomeomorph X Y where
  toPartialEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
protected def restrOpen (s : Set X) (hs : IsOpen s) : PartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
@[simp, mfld_simps]
theorem restrOpen_toPartialEquiv (s : Set X) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl
theorem restrOpen_source (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
@[simps! (config := mfld_cfg) apply symm_apply, simps! (config := .lemmasOnly) source target]
protected def restr (s : Set X) : PartialHomeomorph X Y :=
  e.restrOpen (interior s) isOpen_interior
@[simp, mfld_simps]
theorem restr_toPartialEquiv (s : Set X) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl
theorem restr_source' (s : Set X) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
theorem restr_toPartialEquiv' (s : Set X) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_toPartialEquiv, hs.interior_eq]
theorem restr_eq_of_source_subset {e : PartialHomeomorph X Y} {s : Set X} (h : e.source ⊆ s) :
    e.restr s = e :=
  toPartialEquiv_injective <| PartialEquiv.restr_eq_of_source_subset <|
    interior_maximal h e.open_source
@[simp, mfld_simps]
theorem restr_univ {e : PartialHomeomorph X Y} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
theorem restr_source_inter (s : Set X) : e.restr (e.source ∩ s) = e.restr s := by
  refine PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
protected def refl (X : Type*) [TopologicalSpace X] : PartialHomeomorph X X :=
  (Homeomorph.refl X).toPartialHomeomorph
@[simp, mfld_simps]
theorem refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl
@[simp, mfld_simps]
theorem refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X :=
  rfl
section ofSet
variable {s : Set X} (hs : IsOpen s)
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
def ofSet (s : Set X) (hs : IsOpen s) : PartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn
@[simp, mfld_simps]
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl
@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = PartialHomeomorph.refl X := by ext <;> simp
end ofSet
section trans
variable (e' : PartialHomeomorph Y Z)
@[simps! apply symm_apply toPartialEquiv, simps! (config := .lemmasOnly) source target]
protected def trans' (h : e.target = e'.source) : PartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo
@[trans]
protected def trans : PartialHomeomorph X Z :=
  PartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl
@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : X → Z) = e' ∘ e :=
  rfl
@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : Z → X) = e.symm ∘ e'.symm :=
  rfl
theorem trans_apply {x : X} : (e.trans e') x = e' (e x) :=
  rfl
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
theorem trans_assoc (e'' : PartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _
@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialHomeomorph.refl Y) = e :=
  toPartialEquiv_injective e.1.trans_refl
@[simp, mfld_simps]
theorem refl_trans : (PartialHomeomorph.refl X).trans e = e :=
  toPartialEquiv_injective e.1.refl_trans
theorem trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]
theorem trans_of_set' {s : Set Y} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]
theorem ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by simp [hs.interior_eq, inter_comm]
theorem ofSet_trans' {s : Set X} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]
@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)
end trans
section EqOnSource
def EqOnSource (e e' : PartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
theorem eqOnSource_iff (e e' : PartialHomeomorph X Y) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl
instance eqOnSourceSetoid : Setoid (PartialHomeomorph X Y) :=
  { PartialEquiv.eqOnSourceSetoid.comap toPartialEquiv with r := EqOnSource }
theorem eqOnSource_refl : e ≈ e := Setoid.refl _
theorem EqOnSource.symm' {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h
theorem EqOnSource.source_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.source = e'.source :=
  h.1
theorem EqOnSource.target_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
theorem EqOnSource.eqOn {e e' : PartialHomeomorph X Y} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
theorem EqOnSource.symm_eqOn_target {e e' : PartialHomeomorph X Y} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
theorem EqOnSource.trans' {e e' : PartialHomeomorph X Y} {f f' : PartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf
theorem EqOnSource.restr {e e' : PartialHomeomorph X Y} (he : e ≈ e') (s : Set X) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _
theorem Set.EqOn.restr_eqOn_source {e e' : PartialHomeomorph X Y}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]
theorem self_trans_symm : e.trans e.symm ≈ PartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _
theorem symm_trans_self : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm
theorem eq_of_eqOnSource_univ {e e' : PartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toPartialEquiv_injective <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t
end EqOnSource
section Prod
@[simps! (config := mfld_cfg) toPartialEquiv apply,
  simps! (config := .lemmasOnly) source target symm_apply]
def prod (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    PartialHomeomorph (X × Y) (X' × Y') where
  open_source := eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prod_map eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prod_map eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv
@[simp, mfld_simps]
theorem prod_symm (eX : PartialHomeomorph X X') (eY : PartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl
@[simp]
theorem refl_prod_refl :
    (PartialHomeomorph.refl X).prod (PartialHomeomorph.refl Y) = PartialHomeomorph.refl (X × Y) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ
@[simp, mfld_simps]
theorem prod_trans (e : PartialHomeomorph X Y) (f : PartialHomeomorph Y Z)
    (e' : PartialHomeomorph X' Y') (f' : PartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toPartialEquiv_injective <| e.1.prod_trans ..
theorem prod_eq_prod_of_nonempty {eX eX' : PartialHomeomorph X X'} {eY eY' : PartialHomeomorph Y Y'}
    (h : (eX.prod eY).source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty X := ⟨x⟩
  haveI : Nonempty X' := ⟨eX x⟩
  haveI : Nonempty Y := ⟨y⟩
  haveI : Nonempty Y' := ⟨eY y⟩
  simp_rw [PartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]
theorem prod_eq_prod_of_nonempty'
    {eX eX' : PartialHomeomorph X X'} {eY eY' : PartialHomeomorph Y Y'}
    (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ eY']
end Prod
section Pi
variable {ι : Type*} [Finite ι] {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)] (ei : ∀ i, PartialHomeomorph (X i) (Y i))
@[simps toPartialEquiv]
def pi : PartialHomeomorph (∀ i, X i) (∀ i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
end Pi
section Piecewise
@[simps! (config := .asFn) toPartialEquiv apply]
def piecewise (e e' : PartialHomeomorph X Y) (s : Set X) (t : Set Y) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)
@[simp]
theorem symm_piecewise (e e' : PartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl
def disjointUnion (e e' : PartialHomeomorph X Y) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : PartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
end Piecewise
section Continuity
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y → Z} {s : Set Y} {x : Y}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
theorem continuousAt_iff_continuousAt_comp_right {f : Y → Z} {x : Y} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right h,
    preimage_univ, continuousWithinAt_univ]
theorem continuousOn_iff_continuousOn_comp_right {f : Y → Z} {s : Set Y} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z → X} {s : Set Z} {x : Z}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
theorem continuousAt_iff_continuousAt_comp_left {f : Z → X} {x : Z} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']
theorem continuousOn_iff_continuousOn_comp_left {f : Z → X} {s : Set Z} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)
theorem continuous_iff_continuous_comp_left {f : Z → X} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset
end Continuity
@[simps]
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo'.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_subset e hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.eq <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).restrict_mapsTo h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).restrict_mapsTo h₃ }
@[simps!] 
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology
theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]
@[simps (config := mfld_cfg) apply symm_apply]
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuous_iff_continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuous_iff_continuousOn_univ, h'] using e.continuousOn_symm
theorem isOpenEmbedding_restrict : IsOpenEmbedding (e.source.restrict e) := by
  refine .of_continuous_injective_isOpenMap (e.continuousOn.comp_continuous
    continuous_subtype_val Subtype.prop) e.injOn.injective fun V hV ↦ ?_
  rw [Set.restrict_eq, Set.image_comp]
  exact e.isOpen_image_of_subset_source (e.open_source.isOpenMap_subtype_val V hV)
    fun _ ⟨x, _, h⟩ ↦ h ▸ x.2
@[deprecated (since := "2024-10-18")]
alias openEmbedding_restrict := isOpenEmbedding_restrict
theorem to_isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e :=
  e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding
@[deprecated (since := "2024-10-18")]
alias to_openEmbedding := to_isOpenEmbedding
end PartialHomeomorph
namespace Homeomorph
variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
@[simp, mfld_simps]
theorem refl_toPartialHomeomorph :
    (Homeomorph.refl X).toPartialHomeomorph = PartialHomeomorph.refl X :=
  rfl
@[simp, mfld_simps]
theorem symm_toPartialHomeomorph : e.symm.toPartialHomeomorph = e.toPartialHomeomorph.symm :=
  rfl
@[simp, mfld_simps]
theorem trans_toPartialHomeomorph :
    (e.trans e').toPartialHomeomorph = e.toPartialHomeomorph.trans e'.toPartialHomeomorph :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _
@[simps! (config := .asFn)]
def transPartialHomeomorph (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn
theorem transPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) :
    e.transPartialHomeomorph f' = e.toPartialHomeomorph.trans f' :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _
@[simp, mfld_simps]
theorem transPartialHomeomorph_trans (e : X ≃ₜ Y) (f : PartialHomeomorph Y Z)
    (f' : PartialHomeomorph Z Z') :
    (e.transPartialHomeomorph f).trans f' = e.transPartialHomeomorph (f.trans f') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc]
@[simp, mfld_simps]
theorem trans_transPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) (f'' : PartialHomeomorph Z Z') :
    (e.trans e').transPartialHomeomorph f'' =
      e.transPartialHomeomorph (e'.transPartialHomeomorph f'') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc,
    trans_toPartialHomeomorph]
end Homeomorph
namespace Topology.IsOpenEmbedding
variable (f : X → Y) (h : IsOpenEmbedding f)
@[simps! (config := mfld_cfg) apply source target]
noncomputable def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ
variable [Nonempty X]
lemma toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.left_inv]
  exact Set.mem_univ _
lemma toPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]
end Topology.IsOpenEmbedding
namespace TopologicalSpace.Opens
variable (s : Opens X) (hs : Nonempty s)
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  IsOpenEmbedding.toPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_coe : (s.partialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_source : (s.partialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_target : (s.partialHomeomorphSubtypeCoe hs).target = s := by
  simp only [partialHomeomorphSubtypeCoe, Subtype.range_coe_subtype, mfld_simps]
  rfl
end TopologicalSpace.Opens
namespace PartialHomeomorph
section transHomeomorph
@[simps! (config := .asFn)]
def transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) : PartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id
theorem transHomeomorph_eq_trans (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _
@[simp, mfld_simps]
theorem transHomeomorph_transHomeomorph (e : PartialHomeomorph X Y) (f' : Y ≃ₜ Z) (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]
@[simp, mfld_simps]
theorem trans_transHomeomorph (e : PartialHomeomorph X Y) (e' : PartialHomeomorph Y Z)
    (f'' : Z ≃ₜ Z') :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toPartialHomeomorph]
end transHomeomorph
section subtypeRestr
open TopologicalSpace
variable (e : PartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)
noncomputable def subtypeRestr : PartialHomeomorph s Y :=
  (s.partialHomeomorphSubtypeCoe hs).trans e
theorem subtypeRestr_def : e.subtypeRestr hs = (s.partialHomeomorphSubtypeCoe hs).trans e :=
  rfl
@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : PartialHomeomorph s Y) : s → Y) = Set.restrict ↑s (e : X → Y) :=
  rfl
@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]
theorem map_subtype_source {x : s} (hxe : (x : X) ∈ e.source) :
    e x ∈ (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.partialHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : PartialHomeomorph X Y) :
    (f.subtypeRestr hs).symm.trans (f'.subtypeRestr hs) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  have set_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set X) := s.2
  rw [ofSet_trans', set_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine EqOnSource.trans' (eqOnSource_refl _) ?_
  refine Setoid.trans (symm_trans_self (s.partialHomeomorphSubtypeCoe hs)) ?_
  simp only [mfld_simps, Setoid.refl]
theorem subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target := by
  intro y hy
  rw [eq_comm, eq_symm_apply _ _ hy.1]
  · change restrict _ e _ = _
    rw [← subtypeRestr_coe, (e.subtypeRestr hU).right_inv hy]
  · have := map_target _ hy; rwa [subtypeRestr_source] at this
theorem subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U ≤ V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [PartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ (V.partialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.partialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.partialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · rw [← PartialHomeomorph.symm_target]
    apply PartialHomeomorph.map_source
    rw [PartialHomeomorph.symm_source]
    exact hyV
  · rw [(V.partialHomeomorphSubtypeCoe hV).right_inv hyV]
    show _ = U.partialHomeomorphSubtypeCoe hU _
    rw [(U.partialHomeomorphSubtypeCoe hU).right_inv hy.2]
end subtypeRestr
end PartialHomeomorph