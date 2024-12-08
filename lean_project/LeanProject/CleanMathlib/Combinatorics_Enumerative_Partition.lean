import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.ApplyFun
open Multiset
namespace Nat
@[ext]
structure Partition (n : ℕ) where
  parts : Multiset ℕ
  parts_pos : ∀ {i}, i ∈ parts → 0 < i
  parts_sum : parts.sum = n
namespace Partition
instance decidableEqPartition {n : ℕ} : DecidableEq (Partition n) :=
  fun _ _ => decidable_of_iff' _ Partition.ext_iff
@[simps]
def ofComposition (n : ℕ) (c : Composition n) : Partition n where
  parts := c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]
theorem ofComposition_surj {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩
@[simps]
def ofSums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : Partition n where
  parts := l.filter (· ≠ 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl
@[simps!]
def ofMultiset (l : Multiset ℕ) : Partition l.sum := ofSums _ l rfl
def ofSym {n : ℕ} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition where
  parts := s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    show ∑ a ∈ s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2
variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
@[simp] lemma ofSym_map (e : σ ≃ τ) (s : Sym σ n) :
    ofSym (s.map e) = ofSym s := by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, toFinset_val, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]
def ofSymShapeEquiv (μ : Partition n) (e : σ ≃ τ) :
    {x : Sym σ n // ofSym x = μ} ≃ {x : Sym τ n // ofSym x = μ} where
  toFun := fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp
def indiscrete (n : ℕ) : Partition n := ofSums n {n} rfl
instance {n : ℕ} : Inhabited (Partition n) := ⟨indiscrete n⟩
@[simp] lemma indiscrete_parts {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts = {n} := by
  simp [indiscrete, filter_eq_self, hn]
@[simp] lemma partition_zero_parts (p : Partition 0) : p.parts = 0 :=
  eq_zero_of_forall_not_mem fun _ h => (p.parts_pos h).ne' <| sum_eq_zero_iff.1 p.parts_sum _ h
instance UniquePartitionZero : Unique (Partition 0) where
  uniq _ := Partition.ext <| by simp
@[simp] lemma partition_one_parts (p : Partition 1) : p.parts = {1} := by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h, h', replicate_one]
instance UniquePartitionOne : Unique (Partition 1) where
  uniq _ := Partition.ext <| by simp
@[simp] lemma ofSym_one (s : Sym σ 1) : ofSym s = indiscrete 1 := by
  ext; simp
theorem count_ofSums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi
theorem count_ofSums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl
instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj
def odds (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => ∀ i ∈ c.parts, ¬Even i
def distincts (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => c.parts.Nodup
def oddDistincts (n : ℕ) : Finset (Partition n) :=
  odds n ∩ distincts n
end Partition
end Nat