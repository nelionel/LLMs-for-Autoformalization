import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.LowerUpperTopology
open Set TopologicalSpace
variable {α β γ : Type*}
namespace Topology
def upperSet (α :  Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion
def lowerSet (α :  Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion
def WithUpperSet (α : Type*) := α
namespace WithUpperSet
@[match_pattern] def toUpperSet : α ≃ WithUpperSet α := Equiv.refl _
@[match_pattern] def ofUpperSet : WithUpperSet α ≃ α := Equiv.refl _
@[simp] lemma to_WithUpperSet_symm_eq : (@toUpperSet α).symm = ofUpperSet := rfl
@[simp] lemma of_WithUpperSet_symm_eq : (@ofUpperSet α).symm = toUpperSet := rfl
@[simp] lemma toUpperSet_ofUpperSet (a : WithUpperSet α) : toUpperSet (ofUpperSet a) = a := rfl
@[simp] lemma ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl
lemma toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl
lemma ofUpperSet_inj {a b : WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = b := Iff.rfl
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithUpperSet α → Sort*} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
  fun a => h (ofUpperSet a)
instance [Nonempty α] : Nonempty (WithUpperSet α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithUpperSet α) := ‹Inhabited α›
variable [Preorder α] [Preorder β]
instance : Preorder (WithUpperSet α) := ‹Preorder α›
instance : TopologicalSpace (WithUpperSet α) := upperSet α
lemma ofUpperSet_le_iff {a b : WithUpperSet α} : ofUpperSet a ≤ ofUpperSet b ↔ a ≤ b := Iff.rfl
lemma toUpperSet_le_iff {a b : α} : toUpperSet a ≤ toUpperSet b ↔ a ≤ b := Iff.rfl
def ofUpperSetOrderIso : WithUpperSet α ≃o α where
  toEquiv := ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff
def toUpperSetOrderIso : α ≃o WithUpperSet α where
  toEquiv := toUpperSet
  map_rel_iff' := toUpperSet_le_iff
end WithUpperSet
def WithLowerSet (α : Type*) := α
namespace WithLowerSet
@[match_pattern] def toLowerSet : α ≃ WithLowerSet α := Equiv.refl _
@[match_pattern] def ofLowerSet : WithLowerSet α ≃ α := Equiv.refl _
@[simp] lemma to_WithLowerSet_symm_eq : (@toLowerSet α).symm = ofLowerSet := rfl
@[simp] lemma of_WithLowerSet_symm_eq : (@ofLowerSet α).symm = toLowerSet := rfl
@[simp] lemma toLowerSet_ofLowerSet (a : WithLowerSet α) : toLowerSet (ofLowerSet a) = a := rfl
@[simp] lemma ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl
lemma toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl
lemma ofLowerSet_inj {a b : WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = b := Iff.rfl
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithLowerSet α → Sort*} (h : ∀ a, β (toLowerSet a)) : ∀ a, β a :=
  fun a => h (ofLowerSet a)
instance [Nonempty α] : Nonempty (WithLowerSet α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLowerSet α) := ‹Inhabited α›
variable [Preorder α]
instance : Preorder (WithLowerSet α) := ‹Preorder α›
instance : TopologicalSpace (WithLowerSet α) := lowerSet α
lemma ofLowerSet_le_iff {a b : WithLowerSet α} : ofLowerSet a ≤ ofLowerSet b ↔ a ≤ b := Iff.rfl
lemma toLowerSet_le_iff {a b : α} : toLowerSet a ≤ toLowerSet b ↔ a ≤ b := Iff.rfl
def ofLowerSetOrderIso : WithLowerSet α ≃o α where
  toEquiv := ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff
def toLowerSetOrderIso : α ≃o WithLowerSet α where
  toEquiv := toLowerSet
  map_rel_iff' := toLowerSet_le_iff
end WithLowerSet
def WithUpperSet.toDualHomeomorph [Preorder α] : WithUpperSet α ≃ₜ WithLowerSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng
protected class IsUpperSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSet α
attribute [nolint docBlame] IsUpperSet.topology_eq_upperSetTopology
instance [Preorder α] : Topology.IsUpperSet (WithUpperSet α) := ⟨rfl⟩
instance [Preorder α] : @Topology.IsUpperSet α (upperSet α) _ := by
  letI := upperSet α
  exact ⟨rfl⟩
protected class IsLowerSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = lowerSet α
attribute [nolint docBlame] IsLowerSet.topology_eq_lowerSetTopology
instance [Preorder α] : Topology.IsLowerSet (WithLowerSet α) := ⟨rfl⟩
instance [Preorder α] : @Topology.IsLowerSet α (lowerSet α) _ := by
  letI := lowerSet α
  exact ⟨rfl⟩
namespace IsUpperSet
section Preorder
variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] {s : Set α}
lemma topology_eq : ‹_› = upperSet α := topology_eq_upperSetTopology
variable {α}
instance _root_.OrderDual.instIsLowerSet [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] :
    Topology.IsLowerSet αᵒᵈ where
  topology_eq_lowerSetTopology := by ext; rw [IsUpperSet.topology_eq α]
def WithUpperSetHomeomorph : WithUpperSet α ≃ₜ α :=
  WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩
lemma isOpen_iff_isUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl
instance toAlexandrovDiscrete : AlexandrovDiscrete α where
  isOpen_sInter S := by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)
lemma isClosed_iff_isLower : IsClosed s ↔ IsLowerSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet,
    isLowerSet_compl.symm, compl_compl]
lemma closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s := by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [closure_eq_lowerClosure, lowerClosure_singleton]
  rfl
end Preorder
section maps
variable [Preorder α] [Preorder β]
open Topology
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [Topology.IsUpperSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs ↦ IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic, ← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]
lemma monotone_to_upperTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [IsUpper β] {f : α → β} (hf : Monotone f) : Continuous f := by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf
lemma upperSet_le_upper {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
    [@Topology.IsUpper α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs
end maps
end IsUpperSet
namespace IsLowerSet
section Preorder
variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {s : Set α}
lemma topology_eq : ‹_› = lowerSet α := topology_eq_lowerSetTopology
variable {α}
instance _root_.OrderDual.instIsUpperSet [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] :
    Topology.IsUpperSet αᵒᵈ where
  topology_eq_upperSetTopology := by ext; rw [IsLowerSet.topology_eq α]
def WithLowerSetHomeomorph : WithLowerSet α ≃ₜ α :=
  WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩
lemma isOpen_iff_isLowerSet : IsOpen s ↔ IsLowerSet s := by rw [topology_eq α]; rfl
instance toAlexandrovDiscrete : AlexandrovDiscrete α := IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)
lemma isClosed_iff_isUpper : IsClosed s ↔ IsUpperSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isLowerSet, isUpperSet_compl.symm, compl_compl]
lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)
@[simp] lemma closure_singleton {a : α} : closure {a} = Ici a := by
  rw [closure_eq_upperClosure, upperClosure_singleton]
  rfl
end Preorder
section maps
variable [Preorder α] [Preorder β]
open Topology
open OrderDual
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [Topology.IsLowerSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))
lemma monotone_to_lowerTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [IsLower β] {f : α → β} (hf : Monotone f) : Continuous f :=
  IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual
lemma lowerSet_le_lower {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
    [@IsLower α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs
end maps
end IsLowerSet
lemma isUpperSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α := by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet
lemma isLowerSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsLowerSet αᵒᵈ ↔ Topology.IsUpperSet α := isUpperSet_orderDual.symm
namespace WithUpperSet
variable [Preorder α] [Preorder β] [Preorder γ]
def map (f : α →o β) : C(WithUpperSet α, WithUpperSet β) where
  toFun := toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsUpperSet.preimage hs f.monotone
@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl
@[simp] lemma toUpperSet_specializes_toUpperSet {a b : α} :
    toUpperSet a ⤳ toUpperSet b ↔ b ≤ a := by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]
@[simp] lemma ofUpperSet_le_ofUpperSet {a b : WithUpperSet α} :
    ofUpperSet a ≤ ofUpperSet b ↔ b ⤳ a := toUpperSet_specializes_toUpperSet.symm
@[simp] lemma isUpperSet_toUpperSet_preimage {s : Set (WithUpperSet α)} :
    IsUpperSet (toUpperSet ⁻¹' s) ↔ IsOpen s := Iff.rfl
@[simp] lemma isOpen_ofUpperSet_preimage {s : Set α} :
    IsOpen (ofUpperSet ⁻¹' s) ↔ IsUpperSet s := isUpperSet_toUpperSet_preimage.symm
end WithUpperSet
namespace WithLowerSet
variable [Preorder α] [Preorder β] [Preorder γ]
def map (f : α →o β) : C(WithLowerSet α, WithLowerSet β) where
  toFun := toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsLowerSet.preimage hs f.monotone
@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl
@[simp] lemma toLowerSet_specializes_toLowerSet {a b : α} :
  toLowerSet a ⤳ toLowerSet b ↔ a ≤ b := by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]
@[simp] lemma ofLowerSet_le_ofLowerSet {a b : WithLowerSet α} :
    ofLowerSet a ≤ ofLowerSet b ↔ a ⤳ b := toLowerSet_specializes_toLowerSet.symm
@[simp] lemma isLowerSet_toLowerSet_preimage {s : Set (WithLowerSet α)} :
    IsLowerSet (toLowerSet ⁻¹' s) ↔ IsOpen s := Iff.rfl
@[simp] lemma isOpen_ofLowerSet_preimage {s : Set α} :
    IsOpen (ofLowerSet ⁻¹' s) ↔ IsLowerSet s := isLowerSet_toLowerSet_preimage.symm
end WithLowerSet
end Topology