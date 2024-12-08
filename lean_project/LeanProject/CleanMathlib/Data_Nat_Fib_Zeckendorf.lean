import Mathlib.Data.Nat.Fib.Basic
open List Nat
@[nolint defLemma docBlame]
local instance : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba
namespace List
def IsZeckendorfRep (l : List ℕ) : Prop := (l ++ [0]).Chain' (fun a b ↦ b + 2 ≤ a)
@[simp]
lemma IsZeckendorfRep_nil : IsZeckendorfRep [] := by simp [IsZeckendorfRep]
lemma IsZeckendorfRep.sum_fib_lt : ∀ {n l}, IsZeckendorfRep l → (∀ a ∈ (l ++ [0]).head?, a < n) →
    (l.map fib).sum < fib n
  | _, [], _, hn => fib_pos.2 <| hn _ rfl
  | n, a :: l, hl, hn => by
    simp only [IsZeckendorfRep, cons_append, chain'_iff_pairwise, pairwise_cons] at hl
    have : ∀ b, b ∈ head? (l ++ [0]) → b < a - 1 :=
      fun b hb ↦ lt_tsub_iff_right.2 <| hl.1 _ <| mem_of_mem_head? hb
    simp only [mem_append, mem_singleton, ← chain'_iff_pairwise, or_imp, forall_and, forall_eq,
      zero_add] at hl
    simp only [map, List.sum_cons]
    refine (add_lt_add_left (sum_fib_lt hl.2 this) _).trans_le ?_
    rw [add_comm, ← fib_add_one (hl.1.2.trans_lt' zero_lt_two).ne']
    exact fib_mono (hn _ rfl)
end List
namespace Nat
variable {m n : ℕ}
def greatestFib (n : ℕ) : ℕ := (n + 1).findGreatest (fun k ↦ fib k ≤ n)
lemma fib_greatestFib_le (n : ℕ) : fib (greatestFib n) ≤ n :=
  findGreatest_spec (P := (fun k ↦ fib k ≤ n)) (zero_le _) <| zero_le _
lemma greatestFib_mono : Monotone greatestFib :=
  fun _a _b hab ↦ findGreatest_mono (fun _k ↦ hab.trans') <| add_le_add_right hab _
@[simp] lemma le_greatestFib : m ≤ greatestFib n ↔ fib m ≤ n :=
  ⟨fun h ↦ (fib_mono h).trans <| fib_greatestFib_le _,
    fun h ↦ le_findGreatest (m.le_fib_add_one.trans <| add_le_add_right h _) h⟩
@[simp] lemma greatestFib_lt : greatestFib m < n ↔ m < fib n :=
  lt_iff_lt_of_le_iff_le le_greatestFib
lemma lt_fib_greatestFib_add_one (n : ℕ) : n < fib (greatestFib n + 1) :=
  greatestFib_lt.1 <| lt_succ_self _
@[simp] lemma greatestFib_fib : ∀ {n}, n ≠ 1 → greatestFib (fib n) = n
  | 0, _ => rfl
  | _n + 2, _ => findGreatest_eq_iff.2
    ⟨le_fib_add_one _, fun _ ↦ le_rfl, fun _m hnm _ ↦ ((fib_lt_fib le_add_self).2 hnm).not_le⟩
@[simp] lemma greatestFib_eq_zero : greatestFib n = 0 ↔ n = 0 :=
  ⟨fun h ↦ by simpa using findGreatest_eq_zero_iff.1 h zero_lt_one le_add_self, by rintro rfl; rfl⟩
lemma greatestFib_ne_zero : greatestFib n ≠ 0 ↔ n ≠ 0 := greatestFib_eq_zero.not
@[simp] lemma greatestFib_pos : 0 < greatestFib n ↔ 0 < n := by simp [pos_iff_ne_zero]
lemma greatestFib_sub_fib_greatestFib_le_greatestFib (hn : n ≠ 0) :
    greatestFib (n - fib (greatestFib n)) ≤ greatestFib n - 2 := by
  rw [← Nat.lt_succ_iff, greatestFib_lt, tsub_lt_iff_right n.fib_greatestFib_le, Nat.sub_succ,
    succ_pred, ← fib_add_one]
  · exact n.lt_fib_greatestFib_add_one
  · simpa
  · simpa [← succ_le_iff, tsub_eq_zero_iff_le] using hn.bot_lt
private lemma zeckendorf_aux (hm : 0 < m) : m - fib (greatestFib m) < m :=
tsub_lt_self hm <| fib_pos.2 <| findGreatest_pos.2 ⟨1, zero_lt_one, le_add_self, hm⟩
def zeckendorf : ℕ → List ℕ
  | 0 => []
  | m@(_ + 1) =>
    let a := greatestFib m
    a :: zeckendorf (m - fib a)
decreasing_by simp_wf; subst_vars; apply zeckendorf_aux (zero_lt_succ _)
@[simp] lemma zeckendorf_zero : zeckendorf 0 = [] := zeckendorf.eq_1 ..
@[simp] lemma zeckendorf_succ (n : ℕ) :
    zeckendorf (n + 1) = greatestFib (n + 1) :: zeckendorf (n + 1 - fib (greatestFib (n + 1))) :=
  zeckendorf.eq_2 ..
@[simp] lemma zeckendorf_of_pos : ∀ {n}, 0 < n →
    zeckendorf n = greatestFib n :: zeckendorf (n - fib (greatestFib n))
  | _n + 1, _ => zeckendorf_succ _
lemma isZeckendorfRep_zeckendorf : ∀ n, (zeckendorf n).IsZeckendorfRep
  | 0 => by simp only [zeckendorf_zero, IsZeckendorfRep_nil]
  | n + 1 => by
    rw [zeckendorf_succ, IsZeckendorfRep, List.cons_append]
    refine (isZeckendorfRep_zeckendorf _).cons' (fun a ha ↦ ?_)
    obtain h | h := eq_zero_or_pos (n + 1 - fib (greatestFib (n + 1)))
    · simp only [h, zeckendorf_zero, nil_append, head?_cons, Option.mem_some_iff] at ha
      subst ha
      exact le_greatestFib.2 le_add_self
    rw [zeckendorf_of_pos h, cons_append, head?_cons, Option.mem_some_iff] at ha
    subst a
    exact add_le_of_le_tsub_right_of_le (le_greatestFib.2 le_add_self)
      (greatestFib_sub_fib_greatestFib_le_greatestFib n.succ_ne_zero)
lemma zeckendorf_sum_fib : ∀ {l}, IsZeckendorfRep l → zeckendorf (l.map fib).sum = l
  | [], _ => by simp only [map_nil, List.sum_nil, zeckendorf_zero]
  | a :: l, hl => by
    have hl' := hl
    simp only [IsZeckendorfRep, cons_append, chain'_iff_pairwise, pairwise_cons, mem_append,
      mem_singleton, or_imp, forall_and, forall_eq, zero_add] at hl
    rw [← chain'_iff_pairwise] at hl
    have ha : 0 < a := hl.1.2.trans_lt' zero_lt_two
    suffices h : greatestFib (fib a + sum (map fib l)) = a by
      simp only [map, List.sum_cons, add_pos_iff, fib_pos.2 ha, true_or, zeckendorf_of_pos, h,
      add_tsub_cancel_left, zeckendorf_sum_fib hl.2]
    simp only [add_comm, add_assoc, greatestFib, findGreatest_eq_iff, ne_eq, ha.ne',
      not_false_eq_true, le_add_iff_nonneg_left, _root_.zero_le, forall_true_left, not_le, true_and]
    refine ⟨le_add_of_le_right <| le_fib_add_one _, fun n hn _ ↦ ?_⟩
    rw [add_comm, ← List.sum_cons, ← map_cons]
    exact hl'.sum_fib_lt (by simpa)
@[simp] lemma sum_zeckendorf_fib (n : ℕ) : (n.zeckendorf.map fib).sum = n := by
  induction n using zeckendorf.induct <;> simp_all [fib_greatestFib_le]
def zeckendorfEquiv : ℕ ≃ {l // IsZeckendorfRep l} where
  toFun n := ⟨zeckendorf n, isZeckendorfRep_zeckendorf _⟩
  invFun l := (map fib l).sum
  left_inv := sum_zeckendorf_fib
  right_inv l := Subtype.ext <| zeckendorf_sum_fib l.2
end Nat