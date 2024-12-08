import Mathlib.Data.Bundle
import Mathlib.Data.Set.Image
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.Order.Basic
open TopologicalSpace Filter Set Bundle Function
open scoped Topology
variable {B : Type*} (F : Type*) {E : B → Type*}
variable {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}
structure Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p
namespace Pretrivialization
variable {F}
variable (e : Pretrivialization F proj) {x : Z}
@[coe] def toFun' : Z → (B × F) := e.toFun
instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩
@[ext]
lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr
lemma ext {e e' : Pretrivialization F proj} (h₁ : ∀ x, e x = e' x)
    (h₂ : ∀ x, e.toPartialEquiv.symm x = e'.toPartialEquiv.symm x) (h₃ : e.baseSet = e'.baseSet) :
    e = e' := by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]
lemma toPartialEquiv_injective [Nonempty F] :
    Injective (toPartialEquiv : Pretrivialization F proj → PartialEquiv Z (B × F)) := by
  refine fun e e' h ↦ ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h
@[simp, mfld_simps]
theorem coe_coe : ⇑e.toPartialEquiv = e :=
  rfl
@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex
theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]
theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _ hx => e.coe_fst hx
theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl
theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl
def setSymm : e.target → Z :=
  e.target.restrict e.toPartialEquiv.symm
theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet := by
  rw [e.target_eq, prod_univ, mem_preimage]
theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.toPartialEquiv.symm x) = x.1 := by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this
theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toPartialEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
  ⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target <| e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩
theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toPartialEquiv.symm x) = x :=
  e.toPartialEquiv.right_inv hx
theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toPartialEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)
theorem symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.toPartialEquiv.symm (e x) = x :=
  e.toPartialEquiv.left_inv hx
@[simp, mfld_simps]
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
    e.toPartialEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex, ← e.coe_coe, e.left_inv ex]
@[simp, mfld_simps]
theorem preimage_symm_proj_baseSet :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet) ∩ e.target = e.target := by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, PartialEquiv.invFun_as_coe, e.proj_symm_apply hx]
  exact e.mem_target.mp hx
@[simp, mfld_simps]
theorem preimage_symm_proj_inter (s : Set B) :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.baseSet ×ˢ univ = (s ∩ e.baseSet) ×ˢ univ := by
  ext ⟨x, y⟩
  suffices x ∈ e.baseSet → (proj (e.toPartialEquiv.symm (x, y)) ∈ s ↔ x ∈ s) by
    simpa only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]
theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.target ∩ f.toPartialEquiv.symm ⁻¹' e.source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]
theorem trans_source (e f : Pretrivialization F proj) :
    (f.toPartialEquiv.symm.trans e.toPartialEquiv).source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, e.target_inter_preimage_symm_source_eq]
theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).symm
      = e'.toPartialEquiv.symm.trans e.toPartialEquiv := by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.symm_symm]
theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, e'.source_eq, PartialEquiv.symm_source, e.target_eq, inter_comm,
    e.preimage_symm_proj_inter, inter_comm]
theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [← PartialEquiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]
variable (e' : Pretrivialization F (π F E)) {b : B} {y : E b}
@[simp]
theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source
@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)
theorem mk_mem_target {x : B} {y : F} : (x, y) ∈ e'.target ↔ x ∈ e'.baseSet :=
  e'.mem_target
theorem symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x ∈ e'.baseSet) :
    (e'.toPartialEquiv.symm (x, y)).1 = x :=
  e'.proj_symm_apply' h
section Zero
variable [∀ x, Zero (E x)]
open Classical in
protected noncomputable def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
  if hb : b ∈ e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else 0
theorem symm_apply (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialEquiv.symm (b, y)).2 :=
  dif_pos hb
theorem symm_apply_of_not_mem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
    (y : F) : e.symm b y = 0 :=
  dif_neg hb
theorem coe_symm_of_not_mem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) :
    (e.symm b : F → E b) = 0 :=
  funext fun _ => dif_neg hb
theorem mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toPartialEquiv.symm (b, y) := by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]
theorem symm_proj_apply (e : Pretrivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz, e.symm_apply_apply (e.mem_source.mpr hz)]
theorem symm_apply_apply_mk (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb
theorem apply_mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) := by
  rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]
end Zero
end Pretrivialization
variable [TopologicalSpace Z] [TopologicalSpace (TotalSpace F E)]
structure Trivialization (proj : Z → B) extends PartialHomeomorph Z (B × F) where
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toPartialHomeomorph p).1 = proj p
namespace Trivialization
variable {F}
variable (e : Trivialization F proj) {x : Z}
@[ext]
lemma ext' (e e' : Trivialization F proj) (h₁ : e.toPartialHomeomorph = e'.toPartialHomeomorph)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr
@[coe] def toFun' : Z → (B × F) := e.toFun
def toPretrivialization : Pretrivialization F proj :=
  { e with }
instance : CoeFun (Trivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩
instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩
theorem toPretrivialization_injective :
    Function.Injective fun e : Trivialization F proj => e.toPretrivialization := fun e e' h => by
  ext1
  exacts [PartialHomeomorph.toPartialEquiv_injective (congr_arg Pretrivialization.toPartialEquiv h),
    congr_arg Pretrivialization.baseSet h]
@[simp, mfld_simps]
theorem coe_coe : ⇑e.toPartialHomeomorph = e :=
  rfl
@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _x hx => e.coe_fst hx
theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]
theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl
theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl
theorem source_inter_preimage_target_inter (s : Set (B × F)) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialHomeomorph.source_inter_preimage_target_inter s
@[simp, mfld_simps]
theorem coe_mk (e : PartialHomeomorph Z (B × F)) (i j k l m) (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl
theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet :=
  e.toPretrivialization.mem_target
theorem map_target {x : B × F} (hx : x ∈ e.target) : e.toPartialHomeomorph.symm x ∈ e.source :=
  e.toPartialHomeomorph.map_target hx
theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
    proj (e.toPartialHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx
theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toPartialHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet :=
  e.toPretrivialization.proj_surjOn_baseSet
theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toPartialHomeomorph.symm x) = x :=
  e.toPartialHomeomorph.right_inv hx
theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toPartialHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx
@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.source) : e.toPartialHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex
theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'
theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'
theorem coe_fst_eventuallyEq_proj (ex : x ∈ e.source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩
theorem coe_fst_eventuallyEq_proj' (ex : proj x ∈ e.baseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)
theorem map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventuallyEq_proj ex), ← map_map, ← e.coe_coe,
    e.map_nhds_eq ex, map_fst_nhds]
theorem preimage_subset_source {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ⊆ e.source :=
  fun _p hp => e.mem_source.mpr (hb hp)
theorem image_preimage_eq_prod_univ {s : Set B} (hb : s ⊆ e.baseSet) :
    e '' (proj ⁻¹' s) = s ×ˢ univ :=
  Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩
theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α → Z} {z : Z} (hz : z ∈ e.source) :
    Tendsto f l (𝓝 z) ↔
      Tendsto (proj ∘ f) l (𝓝 (proj z)) ∧ Tendsto (fun x ↦ (e (f x)).2) l (𝓝 (e z).2) := by
  rw [e.nhds_eq_comap_inf_principal hz, tendsto_inf, tendsto_comap_iff, Prod.tendsto_iff, coe_coe,
    tendsto_principal, coe_fst _ hz]
  by_cases hl : ∀ᶠ x in l, f x ∈ e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mono fun x ↦ e.coe_fst
  · simp only [hl, and_false, false_iff, not_and]
    rw [e.source_eq] at hl hz
    exact fun h _ ↦ hl <| h <| e.open_baseSet.mem_nhds hz
theorem nhds_eq_inf_comap {z : Z} (hz : z ∈ e.source) :
    𝓝 z = comap proj (𝓝 (proj z)) ⊓ comap (Prod.snd ∘ e) (𝓝 (e z).2) := by
  refine eq_of_forall_le_iff fun l ↦ ?_
  rw [le_inf_iff, ← tendsto_iff_comap, ← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz
def preimageHomeomorph {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))
@[simp]
theorem preimageHomeomorph_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : proj ⁻¹' s) :
    e.preimageHomeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
  Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl
protected def preimageHomeomorph_symm_apply.aux {s : Set B} (hb : s ⊆ e.baseSet) :=
  (e.preimageHomeomorph hb).symm
@[simp]
theorem preimageHomeomorph_symm_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : s × F) :
    (e.preimageHomeomorph hb).symm p =
      ⟨e.symm (p.1, p.2), ((preimageHomeomorph_symm_apply.aux e hb) p).2⟩ :=
  rfl
def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)
@[simp]
theorem sourceHomeomorphBaseSetProd_apply (p : e.source) :
    e.sourceHomeomorphBaseSetProd p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
  e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩
protected def sourceHomeomorphBaseSetProd_symm_apply.aux := e.sourceHomeomorphBaseSetProd.symm
@[simp]
theorem sourceHomeomorphBaseSetProd_symm_apply (p : e.baseSet × F) :
    e.sourceHomeomorphBaseSetProd.symm p =
      ⟨e.symm (p.1, p.2), (sourceHomeomorphBaseSetProd_symm_apply.aux e p).2⟩ :=
  rfl
def preimageSingletonHomeomorph {b : B} (hb : b ∈ e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
  .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb)) <|
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)
@[simp]
theorem preimageSingletonHomeomorph_apply {b : B} (hb : b ∈ e.baseSet) (p : proj ⁻¹' {b}) :
    e.preimageSingletonHomeomorph hb p = (e p).2 :=
  rfl
@[simp]
theorem preimageSingletonHomeomorph_symm_apply {b : B} (hb : b ∈ e.baseSet) (p : F) :
    (e.preimageSingletonHomeomorph hb).symm p =
      ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
  rfl
theorem continuousAt_proj (ex : x ∈ e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le
protected def compHomeomorph {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h) where
  toPartialHomeomorph := h.toPartialHomeomorph.trans e.toPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p ∈ e.source := by simpa using hp
    simp [hp]
theorem continuousAt_of_comp_right {X : Type*} [TopologicalSpace X] {f : Z → X} {z : Z}
    (e : Trivialization F proj) (he : proj z ∈ e.baseSet)
    (hf : ContinuousAt (f ∘ e.toPartialEquiv.symm) (e z)) : ContinuousAt f z := by
  have hez : z ∈ e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target, e.mem_source]
    exact he
  rwa [e.toPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    PartialHomeomorph.symm_symm]
theorem continuousAt_of_comp_left {X : Type*} [TopologicalSpace X] {f : X → Z} {x : X}
    (e : Trivialization F proj) (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) ∈ e.baseSet)
    (hf : ContinuousAt (e ∘ f) x) : ContinuousAt f x := by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq, ← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)
variable (e' : Trivialization F (π F E)) {b : B} {y : E b}
protected theorem continuousOn : ContinuousOn e' e'.source :=
  e'.continuousOn_toFun
theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source
@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)
theorem mk_mem_target {y : F} : (b, y) ∈ e'.target ↔ b ∈ e'.baseSet :=
  e'.toPretrivialization.mem_target
theorem symm_apply_apply {x : TotalSpace F E} (hx : x ∈ e'.source) :
    e'.toPartialHomeomorph.symm (e' x) = x :=
  e'.toPartialEquiv.left_inv hx
@[simp, mfld_simps]
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization F (π F E)) (h : x ∈ e.baseSet) :
    (e.toPartialHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h
section Zero
variable [∀ x, Zero (E x)]
protected noncomputable def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y
theorem symm_apply (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialHomeomorph.symm (b, y)).2 :=
  dif_pos hb
theorem symm_apply_of_not_mem (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = 0 :=
  dif_neg hb
theorem mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toPartialHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y
theorem symm_proj_apply (e : Trivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz
theorem symm_apply_apply_mk (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb
theorem apply_mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y
theorem continuousOn_symm (e : Trivialization F (π F E)) :
    ContinuousOn (fun z : B × F => TotalSpace.mk' F z.1 (e.symm z.1 z.2)) (e.baseSet ×ˢ univ) := by
  have : ∀ z ∈ e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 ∈ e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toPartialHomeomorph.continuousOn_symm
end Zero
def transFiberHomeomorph {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj where
  toPartialHomeomorph := e.toPartialHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun
@[simp]
theorem transFiberHomeomorph_apply {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toPartialHomeomorph.symm (b, x)).2
theorem mk_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toPartialHomeomorph.symm (b, x)) := by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
theorem coordChange_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p ∈ e₁.baseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coordChange, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]
theorem coordChange_same_apply (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) (x : F) :
    e.coordChange e b x = x := by rw [coordChange, e.apply_symm_apply' h]
theorem coordChange_same (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) :
    e.coordChange e b = id :=
  funext <| e.coordChange_same_apply h
theorem coordChange_coordChange (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x := by
  rw [coordChange, e₁.mk_coordChange _ h₁ h₂, ← e₂.coe_coe, e₂.left_inv, coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
theorem continuous_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : Continuous (e₁.coordChange e₂ b) := by
  refine continuous_snd.comp (e₂.toPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · exact continuous_const.prod_mk continuous_id
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
protected def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.continuous_coordChange e₁ h₂ h₁
@[simp]
theorem coordChangeHomeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl
theorem isImage_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toPartialHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ univ) := fun x hx => by simp [e.coe_fst', hx]
protected def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj where
  toPartialHomeomorph :=
    ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet ∩ s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1
section Piecewise
theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.source ∩ frontier (proj ⁻¹' s) = proj ⁻¹' (e.baseSet ∩ frontier s) := by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq, frontier_prod_univ_eq,
    (e.isImage_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]
open Classical in
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet ∩ frontier s)) : Trivialization F proj where
  toPartialHomeomorph :=
    e.toPartialHomeomorph.piecewise e'.toPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet := e.open_baseSet.ite e'.open_baseSet Hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p := by
    rintro (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]
noncomputable def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) (Heq : ∀ p, proj p = a → e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2
noncomputable def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <| by
    rintro p rfl
    ext1
    · simp [e.coe_fst', e'.coe_fst', *]
    · simp [coordChange_apply_snd, *]
open Classical in
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj where
  toPartialHomeomorph :=
    e.toPartialHomeomorph.disjointUnion e'.toPartialHomeomorph
      (by
        rw [e.source_eq, e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet ∪ e'.baseSet
  open_baseSet := IsOpen.union e.open_baseSet e'.open_baseSet
  source_eq := congr_arg₂ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_toFun := by
    rintro p (hp | hp')
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_not_mem, e'.coe_fst hp']
      simp only [source_eq] at hp' ⊢
      exact fun h => H.le_bot ⟨h, hp'⟩
end Piecewise
end Trivialization