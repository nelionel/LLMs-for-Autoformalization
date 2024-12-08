import Mathlib.Data.Finset.Card
variable {α β : Type*}
open Function
namespace Option
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
@[simp]
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl
@[simp]
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl
@[simp]
theorem mem_toFinset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl
end Option
namespace Finset
def insertNone : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
    rw [le_iff_subset, cons_subset_cons, map_subset_map, le_iff_subset]
@[simp]
theorem mem_insertNone {s : Finset α} : ∀ {o : Option α}, o ∈ insertNone s ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp
lemma forall_mem_insertNone {s : Finset α} {p : Option α → Prop} :
    (∀ a ∈ insertNone s, p a) ↔ p none ∧ ∀ a ∈ s, p a := by simp [Option.forall]
theorem some_mem_insertNone {s : Finset α} {a : α} : some a ∈ insertNone s ↔ a ∈ s := by simp
lemma none_mem_insertNone {s : Finset α} : none ∈ insertNone s := by simp
@[aesop safe apply (rule_sets := [finsetNonempty])]
lemma insertNone_nonempty {s : Finset α} : insertNone s |>.Nonempty := ⟨none, none_mem_insertNone⟩
@[simp]
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insertNone]
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩
@[simp]
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x ∈ eraseNone s ↔ some x ∈ s := by
  simp [eraseNone]
lemma forall_mem_eraseNone {s : Finset (Option α)} {p : Option α → Prop} :
    (∀ a ∈ eraseNone s, p a) ↔ ∀ a : α, (a : Option α) ∈ s → p a := by simp [Option.forall]
theorem eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) :
    eraseNone s = s.biUnion Option.toFinset := by
  ext
  simp
@[simp]
theorem eraseNone_map_some (s : Finset α) : eraseNone (s.map Embedding.some) = s := by
  ext
  simp
@[simp]
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    eraseNone (s.image some) = s := by simpa only [map_eq_image] using eraseNone_map_some s
@[simp]
theorem coe_eraseNone (s : Finset (Option α)) : (eraseNone s : Set α) = some ⁻¹' s :=
  Set.ext fun _ => mem_eraseNone
@[simp]
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∪ t) = eraseNone s ∪ eraseNone t := by
  ext
  simp
@[simp]
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∩ t) = eraseNone s ∩ eraseNone t := by
  ext
  simp
@[simp]
theorem eraseNone_empty : eraseNone (∅ : Finset (Option α)) = ∅ := by
  ext
  simp
@[simp]
theorem eraseNone_none : eraseNone ({none} : Finset (Option α)) = ∅ := by
  ext
  simp
@[simp]
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).image some = s.erase none := by ext (_ | x) <;> simp
@[simp]
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).map Embedding.some = s.erase none := by
  rw [map_eq_image, Embedding.some_apply, image_some_eraseNone]
@[simp]
theorem insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp
@[simp]
theorem eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s := by
  ext
  simp
end Finset