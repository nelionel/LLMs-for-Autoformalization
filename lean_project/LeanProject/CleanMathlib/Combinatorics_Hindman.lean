import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Stream.Init
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.StoneCech
open Filter
@[to_additive
      "Addition of ultrafilters given by `∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`."]
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V
attribute [local instance] Ultrafilter.mul Ultrafilter.add
@[to_additive]
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl
@[to_additive
      "Additive semigroup structure on `Ultrafilter M` induced by an additive semigroup
      structure on `M`."]
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }
attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup
@[to_additive]
theorem Ultrafilter.continuous_mul_left {M} [Semigroup M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun s ↦
    ultrafilter_isOpen_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }
namespace Hindman
inductive FS {M} [AddSemigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FS a a.head
  | tail (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.head + m)
@[to_additive FS]
inductive FP {M} [Semigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FP a a.head
  | tail (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.head * m)
@[to_additive
      "If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`
      is obtained from a subsequence of `M` starting sufficiently late."]
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
    ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a := by
  induction' hm with a a m hm ih a m hm ih
  · exact ⟨1, fun m hm => FP.cons a m hm⟩
  · cases' ih with n hn
    use n + 1
    intro m' hm'
    exact FP.tail _ _ (hn _ hm')
  · cases' ih with n hn
    use n + 1
    intro m' hm'
    rw [mul_assoc]
    exact FP.cons _ _ (hn _ hm')
@[to_additive exists_idempotent_ultrafilter_le_FS]
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a := by
  let S : Set (Ultrafilter M) := ⋂ n, { U | ∀ᶠ m in U, m ∈ FP (a.drop n) }
  have h := exists_idempotent_in_compact_subsemigroup ?_ S ?_ ?_ ?_
  · rcases h with ⟨U, hU, U_idem⟩
    refine ⟨U, U_idem, ?_⟩
    convert Set.mem_iInter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n U hU
      filter_upwards [hU]
      rw [add_comm, ← Stream'.drop_drop, ← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n
      exact ⟨pure _, mem_pure.mpr <| FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).isCompact
    · intro n
      apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_setOf_eq, Ultrafilter.eventually_mul]
    filter_upwards [hU n] with m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    filter_upwards [hV (n' + n)] with m' hm'
    apply hn
    simpa only [Stream'.drop_drop] using hm'
@[to_additive exists_FS_of_large]
theorem exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
    (sU : s₀ ∈ U) : ∃ a, FP a ⊆ s₀ := by
  have exists_elem : ∀ {s : Set M} (_hs : s ∈ U), (s ∩ { m | ∀ᶠ m' in U, m * m' ∈ s }).Nonempty :=
    fun {s} hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rwa [← U_idem] at hs)
  let elem : { s // s ∈ U } → M := fun p => (exists_elem p.property).some
  let succ : {s // s ∈ U} → {s // s ∈ U} := fun (p : {s // s ∈ U}) =>
        ⟨p.val ∩ {m : M | elem p * m ∈ p.val},
         inter_mem p.property
           (show (exists_elem p.property).some ∈ {m : M | ∀ᶠ (m' : M) in ↑U, m * m' ∈ p.val} from
              p.val.inter_subset_right (exists_elem p.property).some_mem)⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices ∀ (a : Stream' M), ∀ m ∈ FP a, ∀ p, a = Stream'.corec elem succ p → m ∈ p.val by
    intro m hm
    exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction' h with b b n h ih b n h ih
  · rintro p rfl
    rw [Stream'.corec_eq, Stream'.head_cons]
    exact Set.inter_subset_left (Set.Nonempty.some_mem _)
  · rintro p rfl
    refine Set.inter_subset_left (ih (succ p) ?_)
    rw [Stream'.corec_eq, Stream'.tail_cons]
  · rintro p rfl
    have := Set.inter_subset_right (ih (succ p) ?_)
    · simpa only using this
    rw [Stream'.corec_eq, Stream'.tail_cons]
@[to_additive FS_partition_regular
      "The strong form of **Hindman's theorem**: in any finite cover of
      an FS-set, one the parts contains an FS-set."]
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ b : Stream' M, FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩
@[to_additive exists_FS_of_finite_cover
      "The weak form of **Hindman's theorem**: in any finite cover
      of a nonempty additive semigroup, one of the parts contains an FS-set."]
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ a : Stream' M, FP a ⊆ c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩
@[to_additive FS_iter_tail_sub_FS]
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : ℕ) : FP (a.drop n) ⊆ FP a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_comm, ← Stream'.drop_drop]
    exact _root_.trans (FP.tail _) ih
@[to_additive]
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : ℕ) : a.get i ∈ FP a := by
  induction i generalizing a with
  | zero => exact FP.head _
  | succ i ih => exact FP.tail _ _ (ih _)
@[to_additive]
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : ℕ) (ij : i < j) :
    a.get i * a.get j ∈ FP a := by
  refine FP_drop_subset_FP _ i ?_
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  change _ ∈ FP _
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop, Stream'.get_drop, Stream'.get_drop] at this
  convert this
  rw [hd, add_comm, Nat.succ_add, Nat.add_succ]
@[to_additive]
theorem FP.finset_prod {M} [CommMonoid M] (a : Stream' M) (s : Finset ℕ) (hs : s.Nonempty) :
    (s.prod fun i => a.get i) ∈ FP a := by
  refine FP_drop_subset_FP _ (s.min' hs) ?_
  induction' s using Finset.strongInduction with s ih
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs), ← Stream'.head_drop]
  rcases (s.erase (s.min' hs)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty, mul_one]
    exact FP.head _
  · apply FP.cons
    rw [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm]
    refine Set.mem_of_subset_of_mem ?_ (ih _ (Finset.erase_ssubset <| s.min'_mem hs) h)
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    cases' Nat.exists_eq_add_of_le this with d hd
    rw [hd, add_comm, ← Stream'.drop_drop]
    apply FP_drop_subset_FP
end Hindman