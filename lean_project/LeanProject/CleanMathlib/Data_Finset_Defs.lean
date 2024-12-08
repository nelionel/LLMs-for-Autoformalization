import Mathlib.Data.Multiset.Nodup
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset
assert_not_exists DirectedSystem
assert_not_exists CompleteLattice
assert_not_exists OrderedCommMonoid
open Multiset Subtype Function
universe u
variable {α : Type*} {β : Type*} {γ : Type*}
structure Finset (α : Type*) where
  val : Multiset α
  nodup : Nodup val
instance Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Multiset.Nodup :=
  ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩
namespace Finset
theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
  | ⟨s, _⟩, ⟨t, _⟩, h => by cases h; rfl
theorem val_injective : Injective (val : Finset α → Multiset α) := fun _ _ => eq_of_veq
@[simp]
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  val_injective.eq_iff
instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | _, _ => decidable_of_iff _ val_inj
instance : Membership α (Finset α) :=
  ⟨fun s a => a ∈ s.1⟩
theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl
@[simp]
theorem mem_val {a : α} {s : Finset α} : a ∈ s.1 ↔ a ∈ s :=
  Iff.rfl
@[simp]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl
instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _
@[simp] lemma forall_mem_not_eq {s : Finset α} {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by aesop
@[simp] lemma forall_mem_not_eq' {s : Finset α} {a : α} : (∀ b ∈ s, ¬ b = a) ↔ a ∉ s := by aesop
@[coe] def toSet (s : Finset α) : Set α :=
  { a | a ∈ s }
instance : CoeTC (Finset α) (Set α) :=
  ⟨toSet⟩
@[simp, norm_cast]
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ (s : Finset α) :=
  Iff.rfl
@[simp]
theorem setOf_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl
@[simp]
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _
instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidableMem _
@[ext]
theorem ext {s₁ s₂ : Finset α} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) : s₁ = s₂ :=
  (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).mpr h
@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  Set.ext_iff.trans Finset.ext_iff.symm
theorem coe_injective {α} : Injective ((↑) : Finset α → Set α) := fun _s _t => coe_inj.1
instance {α : Type u} : CoeSort (Finset α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩
protected theorem forall_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∀ x : s, p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
protected theorem exists_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∃ x : s, p x) ↔ ∃ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
instance PiFinsetCoe.canLift (ι : Type*) (α : ι → Type*) [_ne : ∀ i, Nonempty (α i)]
    (s : Finset ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
instance PiFinsetCoe.canLift' (ι α : Type*) [_ne : Nonempty α] (s : Finset ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s
instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a ∈ s where
  prf a ha := ⟨⟨a, ha⟩, rfl⟩
@[simp, norm_cast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl
section Subset
variable {s t : Finset α}
instance : HasSubset (Finset α) :=
  ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩
instance : HasSSubset (Finset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩
instance partialOrder : PartialOrder (Finset α) where
  le := (· ⊆ ·)
  lt := (· ⊂ ·)
  le_refl _ _ := id
  le_trans _ _ _ hst htu _ ha := htu <| hst ha
  le_antisymm _ _ hst hts := ext fun _ => ⟨@hst _, @hts _⟩
theorem subset_of_le : s ≤ t → s ⊆ t := id
instance : IsRefl (Finset α) (· ⊆ ·) :=
  show IsRefl (Finset α) (· ≤ ·) by infer_instance
instance : IsTrans (Finset α) (· ⊆ ·) :=
  show IsTrans (Finset α) (· ≤ ·) by infer_instance
instance : IsAntisymm (Finset α) (· ⊆ ·) :=
  show IsAntisymm (Finset α) (· ≤ ·) by infer_instance
instance : IsIrrefl (Finset α) (· ⊂ ·) :=
  show IsIrrefl (Finset α) (· < ·) by infer_instance
instance : IsTrans (Finset α) (· ⊂ ·) :=
  show IsTrans (Finset α) (· < ·) by infer_instance
instance : IsAsymm (Finset α) (· ⊂ ·) :=
  show IsAsymm (Finset α) (· < ·) by infer_instance
instance : IsNonstrictStrictOrder (Finset α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩
theorem subset_def : s ⊆ t ↔ s.1 ⊆ t.1 :=
  Iff.rfl
theorem ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s :=
  Iff.rfl
theorem Subset.refl (s : Finset α) : s ⊆ s :=
  Multiset.Subset.refl _
protected theorem Subset.rfl {s : Finset α} : s ⊆ s :=
  Subset.refl _
protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ Subset.refl _
theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  Multiset.Subset.trans
theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h =>
  Subset.trans h h'
theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  Multiset.mem_of_subset
theorem not_mem_mono {s t : Finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s :=
  mt <| @h _
theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩
theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
@[gcongr] protected alias ⟨_, GCongr.coe_subset_coe⟩ := coe_subset
@[simp]
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2
theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iff
theorem not_subset : ¬s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by simp only [← coe_subset, Set.not_subset, mem_coe]
@[simp]
theorem le_eq_subset : ((· ≤ ·) : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl
@[simp]
theorem lt_eq_subset : ((· < ·) : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl
theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
  show (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁ by simp only [Set.ssubset_def, Finset.coe_subset]
@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff
lemma val_strictMono : StrictMono (val : Finset α → Multiset α) := fun _ _ ↦ val_lt_iff.2
theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t
theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h
theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃
theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃
theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ x ∈ s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h
instance isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2
instance wellFoundedLT : WellFoundedLT (Finset α) :=
  Finset.isWellFounded_ssubset
end Subset
attribute [local trans] Subset.trans Superset.trans
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨(↑), coe_injective⟩, coe_subset⟩
@[simp]
theorem coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α → Set α) :=
  rfl
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s := by
  cases s
  dsimp [SizeOf.sizeOf, SizeOf.sizeOf, Multiset.sizeOf]
  rw [add_comm]
  refine lt_trans ?_ (Nat.lt_succ_self _)
  exact Multiset.sizeOf_lt_sizeOf_of_mem hx
section DecidablePiExists
variable {s : Finset α}
instance decidableDforallFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset
instance instDecidableRelSubset [DecidableEq α] : @DecidableRel (Finset α) (· ⊆ ·) :=
  fun _ _ ↦ decidableDforallFinset
instance instDecidableRelSSubset [DecidableEq α] : @DecidableRel (Finset α) (· ⊂ ·) :=
  fun _ _ ↦ instDecidableAnd
instance instDecidableLE [DecidableEq α] : @DecidableRel (Finset α) (· ≤ ·) :=
  instDecidableRelSubset
instance instDecidableLT [DecidableEq α] : @DecidableRel (Finset α) (· < ·) :=
  instDecidableRelSSubset
instance decidableDExistsFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset
instance decidableExistsAndFinset {p : α → Prop} [_hp : ∀ (a), Decidable (p a)] :
    Decidable (∃ a ∈ s, p a) :=
  decidable_of_iff (∃ (a : _) (_ : a ∈ s), p a) (by simp)
instance decidableExistsAndFinsetCoe {p : α → Prop} [DecidablePred p] :
    Decidable (∃ a ∈ (s : Set α), p a) := decidableExistsAndFinset
instance decidableEqPiFinset {β : α → Type*} [_h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ s, β a) :=
  Multiset.decidableEqPiMultiset
end DecidablePiExists
end Finset
namespace List
variable [DecidableEq α] {a : α} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}
instance [DecidableEq β] : Decidable (Set.InjOn f s) :=
  inferInstanceAs (Decidable (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y))
instance [DecidablePred (· ∈ t)] : Decidable (Set.MapsTo f s t) :=
  inferInstanceAs (Decidable (∀ x ∈ s, f x ∈ t))
instance [DecidableEq β] : Decidable (Set.SurjOn f s t') :=
  inferInstanceAs (Decidable (∀ x ∈ t', ∃ y ∈ s, f y = x))
instance [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
end List
namespace Finset
section Pairwise
variable {s : Finset α}
theorem pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) :=
  pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)
theorem pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id
end Pairwise
end Finset