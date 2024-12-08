import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
open Finset Function Sum3
variable {α β γ 𝕜 : Type*} [LinearOrderedField 𝕜] {t : Finset (α × β × γ)} {a a' : α} {b b' : β}
  {c c' : γ} {x : α × β × γ}
namespace SimpleGraph
namespace TripartiteFromTriangles
@[mk_iff] inductive Rel (t : Finset (α × β × γ)) : α ⊕ β ⊕ γ → α ⊕ β ⊕ γ → Prop
| in₀₁ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₀ a) (in₁ b)
| in₁₀ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₁ b) (in₀ a)
| in₀₂ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₀ a) (in₂ c)
| in₂₀ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₂ c) (in₀ a)
| in₁₂ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₁ b) (in₂ c)
| in₂₁ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₂ c) (in₁ b)
open Rel
lemma rel_irrefl : ∀ x, ¬ Rel t x x := fun _x hx ↦ nomatch hx
lemma rel_symm : Symmetric (Rel t) := fun x y h ↦  by cases h <;> constructor <;> assumption
def graph (t : Finset (α × β × γ)) : SimpleGraph (α ⊕ β ⊕ γ) := ⟨Rel t, rel_symm, rel_irrefl⟩
namespace Graph
@[simp] lemma not_in₀₀ : ¬ (graph t).Adj (in₀ a) (in₀ a') := fun h ↦ nomatch h
@[simp] lemma not_in₁₁ : ¬ (graph t).Adj (in₁ b) (in₁ b') := fun h ↦ nomatch h
@[simp] lemma not_in₂₂ : ¬ (graph t).Adj (in₂ c) (in₂ c') := fun h ↦ nomatch h
@[simp] lemma in₀₁_iff : (graph t).Adj (in₀ a) (in₁ b) ↔ ∃ c, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₀₁ h⟩
@[simp] lemma in₁₀_iff : (graph t).Adj (in₁ b) (in₀ a) ↔ ∃ c, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₁₀ h⟩
@[simp] lemma in₀₂_iff : (graph t).Adj (in₀ a) (in₂ c) ↔ ∃ b, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₀₂ h⟩
@[simp] lemma in₂₀_iff : (graph t).Adj (in₂ c) (in₀ a) ↔ ∃ b, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₂₀ h⟩
@[simp] lemma in₁₂_iff : (graph t).Adj (in₁ b) (in₂ c) ↔ ∃ a, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₁₂ h⟩
@[simp] lemma in₂₁_iff : (graph t).Adj (in₂ c) (in₁ b) ↔ ∃ a, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₂₁ h⟩
lemma in₀₁_iff' :
    (graph t).Adj (in₀ a) (in₁ b) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.1 = a ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
lemma in₁₀_iff' :
    (graph t).Adj (in₁ b) (in₀ a) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.1 = b ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
lemma in₀₂_iff' :
    (graph t).Adj (in₀ a) (in₂ c) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.1 = a ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
lemma in₂₀_iff' :
    (graph t).Adj (in₂ c) (in₀ a) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.2 = c ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
lemma in₁₂_iff' :
    (graph t).Adj (in₁ b) (in₂ c) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.1 = b ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
lemma in₂₁_iff' :
    (graph t).Adj (in₂ c) (in₁ b) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.2 = c ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
end Graph
open Graph
class ExplicitDisjoint (t : Finset (α × β × γ)) : Prop where
  inj₀ : ∀ ⦃a b c a'⦄, (a, b, c) ∈ t → (a', b, c) ∈ t → a = a'
  inj₁ : ∀ ⦃a b c b'⦄, (a, b, c) ∈ t → (a, b', c) ∈ t → b = b'
  inj₂ : ∀ ⦃a b c c'⦄, (a, b, c) ∈ t → (a, b, c') ∈ t → c = c'
class NoAccidental (t : Finset (α × β × γ)) : Prop where
  eq_or_eq_or_eq : ∀ ⦃a a' b b' c c'⦄, (a', b, c) ∈ t → (a, b', c) ∈ t → (a, b, c') ∈ t →
    a = a' ∨ b = b' ∨ c = c'
section DecidableEq
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]
instance graph.instDecidableRelAdj : DecidableRel (graph t).Adj
  | in₀ _a, in₀ _a' => Decidable.isFalse not_in₀₀
  | in₀ _a, in₁ _b' => decidable_of_iff' _ in₀₁_iff'
  | in₀ _a, in₂ _c' => decidable_of_iff' _ in₀₂_iff'
  | in₁ _b, in₀ _a' => decidable_of_iff' _ in₁₀_iff'
  | in₁ _b, in₁ _b' => Decidable.isFalse not_in₁₁
  | in₁ _b, in₂ _b' => decidable_of_iff' _ in₁₂_iff'
  | in₂ _c, in₀ _a' => decidable_of_iff' _ in₂₀_iff'
  | in₂ _c, in₁ _b' => decidable_of_iff' _ in₂₁_iff'
  | in₂ _c, in₂ _b' => Decidable.isFalse not_in₂₂
 lemma graph_triple ⦃x y z⦄ :
  (graph t).Adj x y → (graph t).Adj x z → (graph t).Adj y z → ∃ a b c,
    ({in₀ a, in₁ b, in₂ c} : Finset (α ⊕ β ⊕ γ)) = {x, y, z} ∧ (graph t).Adj (in₀ a) (in₁ b) ∧
      (graph t).Adj (in₀ a) (in₂ c) ∧ (graph t).Adj (in₁ b) (in₂ c) := by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    refine ⟨_, _, _, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto,
      ?_, ?_, ?_⟩ <;> constructor <;> assumption
@[simps] def toTriangle : α × β × γ ↪ Finset (α ⊕ β ⊕ γ) where
  toFun x := {in₀ x.1, in₁ x.2.1, in₂ x.2.2}
  inj' := fun ⟨a, b, c⟩ ⟨a', b', c'⟩ ↦ by simpa only [Finset.Subset.antisymm_iff, Finset.subset_iff,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Prod.mk.inj_iff, or_false, false_or,
    in₀, in₁, in₂, Sum.inl.inj_iff, Sum.inr.inj_iff, reduceCtorEq] using And.left
lemma toTriangle_is3Clique (hx : x ∈ t) : (graph t).IsNClique 3 (toTriangle x) := by
  simp only [toTriangle_apply, is3Clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff]
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩
lemma exists_mem_toTriangle {x y : α ⊕ β ⊕ γ} (hxy : (graph t).Adj x y) :
    ∃ z ∈ t, x ∈ toTriangle z ∧ y ∈ toTriangle z := by cases hxy <;> exact ⟨_, ‹_›, by simp⟩
nonrec lemma is3Clique_iff [NoAccidental t] {s : Finset (α ⊕ β ⊕ γ)} :
    (graph t).IsNClique 3 s ↔ ∃ x, x ∈ t ∧ toTriangle x = s := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [is3Clique_iff] at h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := graph_triple hxy hxz hyz
    refine ⟨(a, b, c), ?_, habc⟩
    obtain ⟨c', hc'⟩ := in₀₁_iff.1 hab
    obtain ⟨b', hb'⟩ := in₀₂_iff.1 hac
    obtain ⟨a', ha'⟩ := in₁₂_iff.1 hbc
    obtain rfl | rfl | rfl := NoAccidental.eq_or_eq_or_eq ha' hb' hc' <;> assumption
  · rintro ⟨x, hx, rfl⟩
    exact toTriangle_is3Clique hx
lemma toTriangle_surjOn [NoAccidental t] :
    (t : Set (α × β × γ)).SurjOn toTriangle ((graph t).cliqueSet 3) := fun _ ↦ is3Clique_iff.1
variable (t)
lemma map_toTriangle_disjoint [ExplicitDisjoint t] :
    (t.map toTriangle : Set (Finset (α ⊕ β ⊕ γ))).Pairwise
      fun x y ↦ (x ∩ y : Set (α ⊕ β ⊕ γ)).Subsingleton := by
  intro
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Prod.exists, Ne,
    forall_exists_index, and_imp]
  rintro a b c habc rfl e x y z hxyz rfl h'
  have := ne_of_apply_ne _ h'
  simp only [Ne, Prod.mk.inj_iff, not_and] at this
  simp only [toTriangle_apply, in₀, in₁, in₂, Set.mem_inter_iff, mem_insert, mem_singleton,
    mem_coe, and_imp, Sum.forall, or_false, forall_eq, false_or, eq_self_iff_true, imp_true_iff,
    true_and, and_true, Set.Subsingleton]
  suffices ¬ (a = x ∧ b = y) ∧ ¬ (a = x ∧ c = z) ∧ ¬ (b = y ∧ c = z) by aesop
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact this rfl rfl (ExplicitDisjoint.inj₂ habc hxyz)
  · rintro ⟨rfl, rfl⟩
    exact this rfl (ExplicitDisjoint.inj₁ habc hxyz) rfl
  · rintro ⟨rfl, rfl⟩
    exact this (ExplicitDisjoint.inj₀ habc hxyz) rfl rfl
lemma cliqueSet_eq_image [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '' t := by
  ext; exact is3Clique_iff
section Fintype
variable [Fintype α] [Fintype β] [Fintype γ]
lemma cliqueFinset_eq_image [NoAccidental t] : (graph t).cliqueFinset 3 = t.image toTriangle :=
  coe_injective <| by push_cast; exact cliqueSet_eq_image _
lemma cliqueFinset_eq_map [NoAccidental t] : (graph t).cliqueFinset 3 = t.map toTriangle := by
  simp [cliqueFinset_eq_image, map_eq_image]
@[simp] lemma card_triangles [NoAccidental t] : #((graph t).cliqueFinset 3) = #t := by
  rw [cliqueFinset_eq_map, card_map]
lemma farFromTriangleFree [ExplicitDisjoint t] {ε : 𝕜}
    (ht : ε * ((Fintype.card α + Fintype.card β + Fintype.card γ) ^ 2 : ℕ) ≤ #t) :
    (graph t).FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles (t.map toTriangle)
    (map_subset_iff_subset_preimage.2 fun x hx ↦ by simpa using toTriangle_is3Clique hx)
    (map_toTriangle_disjoint t) <| by simpa [add_assoc] using ht
end Fintype
end DecidableEq
variable (t)
lemma locallyLinear [ExplicitDisjoint t] [NoAccidental t] : (graph t).LocallyLinear := by
  classical
  refine ⟨?_, fun x y hxy ↦ ?_⟩
  · unfold EdgeDisjointTriangles
    convert map_toTriangle_disjoint t
    rw [cliqueSet_eq_image, coe_map]
  · obtain ⟨z, hz, hxy⟩ := exists_mem_toTriangle hxy
    exact ⟨_, toTriangle_is3Clique hz, hxy⟩
end TripartiteFromTriangles
end SimpleGraph