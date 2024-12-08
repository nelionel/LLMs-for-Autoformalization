import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.Tactic.Bound.Attribute
assert_not_exists Ring
open Function
variable {ι α β M N G k R : Type*}
namespace Finset
section OrderedCommMonoid
variable [CommMonoid M] [OrderedCommMonoid N]
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  rw [Multiset.map_map]
  rfl
add_decl_doc le_sum_nonempty_of_subadditive_on_pred
@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative (f : M → N) (h_mul : ∀ x y, f (x * y) ≤ f x * f y)
    {s : Finset ι} (hs : s.Nonempty) (g : ι → M) : f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ ↦ True) (fun x y _ _ ↦ h_mul x y)
    (fun _ _ _ _ ↦ trivial) g s hs fun _ _ ↦ trivial
add_decl_doc le_sum_nonempty_of_subadditive
@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred (f : M → N) (p : M → Prop) (h_one : f 1 = 1)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) : f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs
add_decl_doc le_sum_of_subadditive_on_pred
@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative (f : M → N) (h_one : f 1 = 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) ?_
  rw [Multiset.map_map]
  rfl
add_decl_doc le_sum_of_subadditive
variable {f g : ι → N} {s t : Finset ι}
@[to_additive (attr := gcongr) sum_le_sum]
theorem prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
  Multiset.prod_map_le_prod_map f g h
attribute [bound] sum_le_sum
add_decl_doc sum_le_sum
@[to_additive sum_nonneg]
theorem one_le_prod' (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)
@[to_additive Finset.sum_nonneg']
theorem one_le_prod'' (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.one_le_prod' fun i _ ↦ h i
@[to_additive sum_nonpos]
theorem prod_le_one' (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])
@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]
@[to_additive sum_mono_set_of_nonneg]
theorem prod_mono_set_of_one_le' (hf : ∀ x, 1 ≤ f x) : Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x
@[to_additive sum_le_univ_sum_of_nonneg]
theorem prod_le_univ_prod_of_one_le' [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a
@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_one_le' :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.not_mem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff_of_one_le (H _ <| mem_insert_self _ _) (one_le_prod' this),
      forall_mem_insert, ih this]
@[to_additive sum_eq_zero_iff_of_nonpos]
theorem prod_eq_one_iff_of_le_one' :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  @prod_eq_one_iff_of_one_le' _ Nᵒᵈ _ _ _
@[to_additive single_le_sum]
theorem single_le_prod' (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) : f a ≤ ∏ x ∈ s, f x :=
  calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi
@[to_additive]
lemma mul_le_prod {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k :=
  calc
    f i * f j = ∏ k ∈ .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k ∈ s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]
@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp
@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ #s ≤ s.prod f := @Finset.prod_le_pow_card _ Nᵒᵈ _ _ _ _ h
theorem card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, #(f a) ≤ n) : #(s.biUnion f) ≤ #s * n :=
  card_biUnion_le.trans <| sum_le_card_nsmul _ _ _ h
variable {ι' : Type*} [DecidableEq ι']
@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ y ∉ t, (1 : N) ≤ ∏ x ∈ s with g x = y, f x) :
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤ ∏ x ∈ s, f x :=
  calc
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤
        ∏ y ∈ t ∪ s.image g, ∏ x ∈ s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ ↦ h y
    _ = ∏ x ∈ s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _
@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ y ∉ t, ∏ x ∈ s with g x = y, f x ≤ 1) :
    ∏ x ∈ s, f x ≤ ∏ y ∈ t, ∏ x ∈ s with g x = y, f x :=
  @prod_fiberwise_le_prod_of_one_le_prod_fiber' _ Nᵒᵈ _ _ _ _ _ _ _ h
end OrderedCommMonoid
@[to_additive]
lemma max_prod_le [LinearOrderedCommMonoid M] {f g : ι → M} {s : Finset ι} :
    max (s.prod f) (s.prod g) ≤ s.prod (fun i ↦ max (f i) (g i)) :=
  Multiset.max_prod_le
@[to_additive]
lemma prod_min_le [LinearOrderedCommMonoid M] {f g : ι → M} {s : Finset ι} :
    s.prod (fun i ↦ min (f i) (g i)) ≤ min (s.prod f) (s.prod g) :=
  Multiset.prod_min_le
theorem abs_sum_le_sum_abs {G : Type*} [LinearOrderedAddCommGroup G] (f : ι → G) (s : Finset ι) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := le_sum_of_subadditive _ abs_zero abs_add s f
theorem abs_sum_of_nonneg {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i ∈ s, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]
theorem abs_sum_of_nonneg' {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]
section CommMonoid
variable [CommMonoid α] [LE α] [MulLeftMono α] {s : Finset ι} {f : ι → α}
@[to_additive (attr := simp)]
lemma mulLECancellable_prod :
    MulLECancellable (∏ i ∈ s, f i) ↔ ∀ ⦃i⦄, i ∈ s → MulLECancellable (f i) := by
  induction' s using Finset.cons_induction with i s hi ih <;> simp [*]
end CommMonoid
section Pigeonhole
variable [DecidableEq β]
theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #t :=
  calc
    #s = ∑ b ∈ t, #{a ∈ s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _b ∈ t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]
theorem card_le_mul_card_image {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #(s.image f) :=
  card_le_mul_card_image_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn
theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, n ≤ #{a ∈ s | f a = b}) :
    n * #t ≤ #s :=
  calc
    n * #t = ∑ _a ∈ t, n := by simp [mul_comm]
    _ ≤ ∑ b ∈ t, #{a ∈ s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]
theorem mul_card_image_le_card {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, n ≤ #{a ∈ s | f a = b}) : n * #(s.image f) ≤ #s :=
  mul_card_image_le_card_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn
end Pigeonhole
section DoubleCounting
variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}
theorem sum_card_inter_le (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} ≤ n) : (∑ t ∈ B, #(s ∩ t)) ≤ #s * n := by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
lemma sum_card_le [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} ≤ n) : ∑ s ∈ B, #s ≤ Fintype.card α * n :=
  calc
    ∑ s ∈ B, #s = ∑ s ∈ B, #(univ ∩ s) := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := sum_card_inter_le fun a _ ↦ h a
theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ #{b ∈ B | a ∈ b}) : #s * n ≤ ∑ t ∈ B, #(s ∩ t) := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ #{b ∈ B | a ∈ b}) :
    Fintype.card α * n ≤ ∑ s ∈ B, #s :=
  calc
    Fintype.card α * n ≤ ∑ s ∈ B, #(univ ∩ s) := le_sum_card_inter fun a _ ↦ h a
    _ = ∑ s ∈ B, #s := by simp_rw [univ_inter]
theorem sum_card_inter (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} = n) :
    (∑ t ∈ B, #(s ∩ t)) = #s * n :=
  (sum_card_inter_le fun a ha ↦ (h a ha).le).antisymm (le_sum_card_inter fun a ha ↦ (h a ha).ge)
theorem sum_card [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} = n) :
    ∑ s ∈ B, #s = Fintype.card α * n := by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ ↦ h a, univ_inter]
theorem card_le_card_biUnion {s : Finset ι} {f : ι → Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : ∀ i ∈ s, (f i).Nonempty) : #s ≤ #(s.biUnion f) := by
  rw [card_biUnion hs, card_eq_sum_ones]
  exact sum_le_sum fun i hi ↦ (hf i hi).card_pos
theorem card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι → Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + #{i ∈ s | f i = ∅} := by
  rw [← Finset.filter_card_add_filter_neg_card_eq_card fun i ↦ f i = ∅, add_comm]
  exact
    add_le_add_right
      ((card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi ↦
            nonempty_of_ne_empty <| (mem_filter.1 hi).2).trans <|
        card_le_card <| biUnion_subset_biUnion_of_subset_left _ <| filter_subset _ _)
      _
theorem card_le_card_biUnion_add_one {s : Finset ι} {f : ι → Finset α} (hf : Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + 1 :=
  (card_le_card_biUnion_add_card_fiber hs).trans <|
    add_le_add_left
      (card_le_one.2 fun _ hi _ hj ↦ hf <| (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) _
end DoubleCounting
section CanonicallyOrderedCommMonoid
variable [CanonicallyOrderedCommMonoid M] {f : ι → M} {s t : Finset ι}
@[to_additive "In a canonically-ordered additive monoid, a sum bounds each of its terms.
See also `Finset.single_le_sum`."]
lemma _root_.CanonicallyOrderedCommMonoid.single_le_prod {i : ι} (hi : i ∈ s) :
    f i ≤ ∏ j ∈ s, f j :=
  single_le_prod' (fun _ _ ↦ one_le _) hi
@[to_additive (attr := simp) sum_eq_zero_iff]
theorem prod_eq_one_iff' : ∏ x ∈ s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
  prod_eq_one_iff_of_one_le' fun x _ ↦ one_le (f x)
@[to_additive sum_le_sum_of_subset]
theorem prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x :=
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ ↦ one_le _
@[to_additive sum_mono_set]
theorem prod_mono_set' (f : ι → M) : Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hs ↦
  prod_le_prod_of_subset' hs
@[to_additive sum_le_sum_of_ne_zero]
theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  classical calc
    ∏ x ∈ s, f x = (∏ x ∈ s with f x = 1, f x) * ∏ x ∈ s with f x ≠ 1, f x := by
      rw [← prod_union, filter_union_filter_neg_eq]
      exact disjoint_filter.2 fun _ _ h n_h ↦ n_h h
    _ ≤ ∏ x ∈ t, f x :=
      mul_le_of_le_one_of_le
        (prod_le_one' <| by simp only [mem_filter, and_imp]; exact fun _ _ ↦ le_of_eq)
        (prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp] )
end CanonicallyOrderedCommMonoid
section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}
@[to_additive sum_lt_sum]
theorem prod_lt_prod' (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod' hle hlt
@[to_additive (attr := gcongr) sum_lt_sum_of_nonempty]
theorem prod_lt_prod_of_nonempty' (hs : s.Nonempty) (hlt : ∀ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt
add_decl_doc sum_lt_sum_of_nonempty
@[to_additive sum_lt_sum_of_subset]
theorem prod_lt_prod_of_subset' (h : s ⊆ t) {i : ι} (ht : i ∈ t) (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : ∏ j ∈ s, f j < ∏ j ∈ t, f j := by
  classical calc
    ∏ j ∈ s, f j < ∏ j ∈ insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j ∈ s, f j) hlt
    _ ≤ ∏ j ∈ t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2
@[to_additive single_lt_sum]
theorem single_lt_prod' {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s) (hlt : 1 < f j)
    (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k ∈ s, f k :=
  calc
    f i = ∏ k ∈ {i}, f k := by rw [prod_singleton]
    _ < ∏ k ∈ s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki ↦ hle k hks (mt mem_singleton.2 hki)
@[to_additive sum_pos]
theorem one_lt_prod (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i ∈ s, f i :=
  lt_of_le_of_lt (by rw [prod_const_one]) <| prod_lt_prod_of_nonempty' hs h
@[to_additive]
theorem prod_lt_one (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) : ∏ i ∈ s, f i < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])
@[to_additive sum_pos']
theorem one_lt_prod' (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) : 1 < ∏ i ∈ s, f i :=
  prod_const_one.symm.trans_lt <| prod_lt_prod' h hs
@[to_additive]
theorem prod_lt_one' (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) : ∏ i ∈ s, f i < 1 :=
  prod_const_one.le.trans_lt' <| prod_lt_prod' h hs
@[to_additive]
theorem prod_eq_prod_iff_of_le {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i ∈ s, f i) = ∏ i ∈ s, g i) ↔ ∀ i ∈ s, f i = g i := by
  classical
    revert h
    refine Finset.induction_on s (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.not_mem_empty _ h),
      fun _ ↦ rfl⟩) fun a s ha ih H ↦ ?_
    specialize ih fun i ↦ H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.forall_mem_insert, ← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i ↦ H i ∘ Finset.mem_insert_of_mem)
variable [DecidableEq ι]
@[to_additive] lemma prod_sdiff_le_prod_sdiff :
    ∏ i ∈ s \ t, f i ≤ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← mul_le_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s
@[to_additive] lemma prod_sdiff_lt_prod_sdiff :
    ∏ i ∈ s \ t, f i < ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i < ∏ i ∈ t, f i := by
  rw [← mul_lt_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s
end OrderedCancelCommMonoid
section LinearOrderedCancelCommMonoid
variable [LinearOrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}
@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' (Hlt : ∏ i ∈ s, f i < ∏ i ∈ s, g i) : ∃ i ∈ s, f i < g i := by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle
@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt
@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : ∏ i ∈ s, f i = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    ∏ j ∈ s, f j < ∏ j ∈ s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one
end LinearOrderedCancelCommMonoid
end Finset
namespace Fintype
section OrderedCommMonoid
variable [Fintype ι] [OrderedCommMonoid M] {f : ι → M}
@[to_additive (attr := mono) sum_mono]
theorem prod_mono' : Monotone fun f : ι → M ↦ ∏ i, f i := fun _ _ hfg ↦
  Finset.prod_le_prod' fun x _ ↦ hfg x
@[to_additive sum_nonneg]
lemma one_le_prod (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod' fun _ _ ↦ hf _
@[to_additive] lemma prod_le_one (hf : f ≤ 1) : ∏ i, f i ≤ 1 := Finset.prod_le_one' fun _ _ ↦ hf _
@[to_additive]
lemma prod_eq_one_iff_of_one_le (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_one_le' fun i _ ↦ hf i).trans <| by simp [funext_iff]
@[to_additive]
lemma prod_eq_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_le_one' fun i _ ↦ hf i).trans <| by simp [funext_iff]
end OrderedCommMonoid
section OrderedCancelCommMonoid
variable [Fintype ι] [OrderedCancelCommMonoid M] {f : ι → M}
@[to_additive sum_strictMono]
theorem prod_strictMono' : StrictMono fun f : ι → M ↦ ∏ x, f x :=
  fun _ _ hfg ↦
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ ↦ hle i) ⟨i, Finset.mem_univ i, hlt⟩
@[to_additive sum_pos]
lemma one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i :=
  Finset.one_lt_prod' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2
@[to_additive]
lemma prod_lt_one (hf : f < 1) : ∏ i, f i < 1 :=
  Finset.prod_lt_one' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2
@[to_additive sum_pos_iff_of_nonneg]
lemma one_lt_prod_iff_of_one_le (hf : 1 ≤ f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]
@[to_additive]
lemma prod_lt_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]
end OrderedCancelCommMonoid
end Fintype
namespace Multiset
theorem finset_sum_eq_sup_iff_disjoint [DecidableEq α] {i : Finset β} {f : β → Multiset α} :
    i.sum f = i.sup f ↔ ∀ x ∈ i, ∀ y ∈ i, x ≠ y → Disjoint (f x) (f y) := by
  induction' i using Finset.cons_induction_on with z i hz hr
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero, eq_self_iff_true]
  · simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne, not_true_eq_false, IsEmpty.forall_iff, true_and,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (H : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp +contextual only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finset_sum_left, ← disjoint_finset_sum_right, disjoint_comm, ← and_assoc,
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))
theorem sup_powerset_len [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x using 1
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)
end Multiset