import Mathlib.Computability.Primrec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open Nat
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
@[simp]
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]
@[simp]
theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]
@[simp]
theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]
@[simp]
theorem ack_one (n : ℕ) : ack 1 n = n + 2 := by
  induction' n with n IH
  · simp
  · simp [IH]
@[simp]
theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 := by
  induction' n with n IH
  · simp
  · simpa [mul_succ]
@[simp]
theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 := by
  induction' n with n IH
  · simp
  · rw [ack_succ_succ, IH, ack_two, Nat.succ_add, Nat.pow_succ 2 (n + 3), mul_comm _ 2,
        Nat.mul_sub_left_distrib, ← Nat.sub_add_comm, two_mul 3, Nat.add_sub_add_right]
    have H : 2 * 3 ≤ 2 * 2 ^ 3 := by norm_num
    apply H.trans
    rw [_root_.mul_le_mul_left two_pos]
    exact pow_right_mono₀ one_le_two (Nat.le_add_left 3 n)
theorem ack_pos : ∀ m n, 0 < ack m n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply ack_pos
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply ack_pos
theorem one_lt_ack_succ_left : ∀ m n, 1 < ack (m + 1) n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply one_lt_ack_succ_left
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply one_lt_ack_succ_left
theorem one_lt_ack_succ_right : ∀ m n, 1 < ack m (n + 1)
  | 0, n => by simp
  | m + 1, n => by
    rw [ack_succ_succ]
    cases' exists_eq_succ_of_ne_zero (ack_pos (m + 1) n).ne' with h h
    rw [h]
    apply one_lt_ack_succ_right
theorem ack_strictMono_right : ∀ m, StrictMono (ack m)
  | 0, n₁, n₂, h => by simpa using h
  | m + 1, 0, n + 1, _h => by
    rw [ack_succ_zero, ack_succ_succ]
    exact ack_strictMono_right _ (one_lt_ack_succ_left m n)
  | m + 1, n₁ + 1, n₂ + 1, h => by
    rw [ack_succ_succ, ack_succ_succ]
    apply ack_strictMono_right _ (ack_strictMono_right _ _)
    rwa [add_lt_add_iff_right] at h
theorem ack_mono_right (m : ℕ) : Monotone (ack m) :=
  (ack_strictMono_right m).monotone
theorem ack_injective_right (m : ℕ) : Function.Injective (ack m) :=
  (ack_strictMono_right m).injective
@[simp]
theorem ack_lt_iff_right {m n₁ n₂ : ℕ} : ack m n₁ < ack m n₂ ↔ n₁ < n₂ :=
  (ack_strictMono_right m).lt_iff_lt
@[simp]
theorem ack_le_iff_right {m n₁ n₂ : ℕ} : ack m n₁ ≤ ack m n₂ ↔ n₁ ≤ n₂ :=
  (ack_strictMono_right m).le_iff_le
@[simp]
theorem ack_inj_right {m n₁ n₂ : ℕ} : ack m n₁ = ack m n₂ ↔ n₁ = n₂ :=
  (ack_injective_right m).eq_iff
theorem max_ack_right (m n₁ n₂ : ℕ) : ack m (max n₁ n₂) = max (ack m n₁) (ack m n₂) :=
  (ack_mono_right m).map_max
theorem add_lt_ack : ∀ m n, m + n < ack m n
  | 0, n => by simp
  | m + 1, 0 => by simpa using add_lt_ack m 1
  | m + 1, n + 1 =>
    calc
      m + 1 + n + 1 ≤ m + (m + n + 2) := by omega
      _ < ack m (m + n + 2) := add_lt_ack _ _
      _ ≤ ack m (ack (m + 1) n) :=
        ack_mono_right m <| le_of_eq_of_le (by rw [succ_eq_add_one]; ring_nf)
        <| succ_le_of_lt <| add_lt_ack (m + 1) n
      _ = ack (m + 1) (n + 1) := (ack_succ_succ m n).symm
theorem add_add_one_le_ack (m n : ℕ) : m + n + 1 ≤ ack m n :=
  succ_le_of_lt (add_lt_ack m n)
theorem lt_ack_left (m n : ℕ) : m < ack m n :=
  (self_le_add_right m n).trans_lt <| add_lt_ack m n
theorem lt_ack_right (m n : ℕ) : n < ack m n :=
  (self_le_add_left n m).trans_lt <| add_lt_ack m n
private theorem ack_strict_mono_left' : ∀ {m₁ m₂} (n), m₁ < m₂ → ack m₁ n < ack m₂ n
  | m, 0, _ => fun h => (not_lt_zero m h).elim
  | 0, m + 1, 0 => fun _h => by simpa using one_lt_ack_succ_right m 0
  | 0, m + 1, n + 1 => fun h => by
    rw [ack_zero, ack_succ_succ]
    apply lt_of_le_of_lt (le_trans _ <| add_le_add_left (add_add_one_le_ack _ _) m) (add_lt_ack _ _)
    omega
  | m₁ + 1, m₂ + 1, 0 => fun h => by
    simpa using ack_strict_mono_left' 1 ((add_lt_add_iff_right 1).1 h)
  | m₁ + 1, m₂ + 1, n + 1 => fun h => by
    rw [ack_succ_succ, ack_succ_succ]
    exact
      (ack_strict_mono_left' _ <| (add_lt_add_iff_right 1).1 h).trans
        (ack_strictMono_right _ <| ack_strict_mono_left' n h)
theorem ack_strictMono_left (n : ℕ) : StrictMono fun m => ack m n := fun _m₁ _m₂ =>
  ack_strict_mono_left' n
theorem ack_mono_left (n : ℕ) : Monotone fun m => ack m n :=
  (ack_strictMono_left n).monotone
theorem ack_injective_left (n : ℕ) : Function.Injective fun m => ack m n :=
  (ack_strictMono_left n).injective
@[simp]
theorem ack_lt_iff_left {m₁ m₂ n : ℕ} : ack m₁ n < ack m₂ n ↔ m₁ < m₂ :=
  (ack_strictMono_left n).lt_iff_lt
@[simp]
theorem ack_le_iff_left {m₁ m₂ n : ℕ} : ack m₁ n ≤ ack m₂ n ↔ m₁ ≤ m₂ :=
  (ack_strictMono_left n).le_iff_le
@[simp]
theorem ack_inj_left {m₁ m₂ n : ℕ} : ack m₁ n = ack m₂ n ↔ m₁ = m₂ :=
  (ack_injective_left n).eq_iff
theorem max_ack_left (m₁ m₂ n : ℕ) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ n) :=
  (ack_mono_left n).map_max
theorem ack_le_ack {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) : ack m₁ n₁ ≤ ack m₂ n₂ :=
  (ack_mono_left n₁ hm).trans <| ack_mono_right m₂ hn
theorem ack_succ_right_le_ack_succ_left (m n : ℕ) : ack m (n + 1) ≤ ack (m + 1) n := by
  cases' n with n n
  · simp
  · rw [ack_succ_succ]
    apply ack_mono_right m (le_trans _ <| add_add_one_le_ack _ n)
    omega
private theorem sq_le_two_pow_add_one_minus_three (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) - 3 := by
  induction' n with k hk
  · norm_num
  · cases' k with k k
    · norm_num
    · rw [add_sq, Nat.pow_succ 2, mul_comm _ 2, two_mul (2 ^ _),
          add_tsub_assoc_of_le, add_comm (2 ^ _), add_assoc]
      · apply Nat.add_le_add hk
        norm_num
        apply succ_le_of_lt
        rw [Nat.pow_succ, mul_comm _ 2, mul_lt_mul_left (zero_lt_two' ℕ)]
        exact Nat.lt_two_pow_self
      · rw [Nat.pow_succ, Nat.pow_succ]
        linarith [one_le_pow k 2 zero_lt_two]
theorem ack_add_one_sq_lt_ack_add_three : ∀ m n, (ack m n + 1) ^ 2 ≤ ack (m + 3) n
  | 0, n => by simpa using sq_le_two_pow_add_one_minus_three (n + 2)
  | m + 1, 0 => by
    rw [ack_succ_zero, ack_succ_zero]
    apply ack_add_one_sq_lt_ack_add_three
  | m + 1, n + 1 => by
    rw [ack_succ_succ, ack_succ_succ]
    apply (ack_add_one_sq_lt_ack_add_three _ _).trans (ack_mono_right _ <| ack_mono_left _ _)
    omega
theorem ack_ack_lt_ack_max_add_two (m n k : ℕ) : ack m (ack n k) < ack (max m n + 2) k :=
  calc
    ack m (ack n k) ≤ ack (max m n) (ack n k) := ack_mono_left _ (le_max_left _ _)
    _ < ack (max m n) (ack (max m n + 1) k) :=
      ack_strictMono_right _ <| ack_strictMono_left k <| lt_succ_of_le <| le_max_right m n
    _ = ack (max m n + 1) (k + 1) := (ack_succ_succ _ _).symm
    _ ≤ ack (max m n + 2) k := ack_succ_right_le_ack_succ_left _ _
theorem ack_add_one_sq_lt_ack_add_four (m n : ℕ) : ack m ((n + 1) ^ 2) < ack (m + 4) n :=
  calc
    ack m ((n + 1) ^ 2) < ack m ((ack m n + 1) ^ 2) :=
      ack_strictMono_right m <| Nat.pow_lt_pow_left (succ_lt_succ <| lt_ack_right m n) two_ne_zero
    _ ≤ ack m (ack (m + 3) n) := ack_mono_right m <| ack_add_one_sq_lt_ack_add_three m n
    _ ≤ ack (m + 2) (ack (m + 3) n) := ack_mono_left _ <| by omega
    _ = ack (m + 3) (n + 1) := (ack_succ_succ _ n).symm
    _ ≤ ack (m + 4) n := ack_succ_right_le_ack_succ_left _ n
theorem ack_pair_lt (m n k : ℕ) : ack m (pair n k) < ack (m + 4) (max n k) :=
  (ack_strictMono_right m <| pair_lt_max_add_one_sq n k).trans <|
    ack_add_one_sq_lt_ack_add_four _ _
theorem exists_lt_ack_of_nat_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ m, ∀ n, f n < ack m n := by
  induction' hf with f g hf hg IHf IHg f g hf hg IHf IHg f g hf hg IHf IHg
  · exact ⟨0, ack_pos 0⟩
  · refine ⟨1, fun n => ?_⟩
    rw [succ_eq_one_add]
    apply add_lt_ack
  · refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_left_le n
  · refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_right_le n
  all_goals cases' IHf with a ha; cases' IHg with b hb
  · refine
      ⟨max a b + 3, fun n =>
        (pair_lt_max_add_one_sq _ _).trans_le <|
          (Nat.pow_le_pow_left (add_le_add_right ?_ _) 2).trans <|
            ack_add_one_sq_lt_ack_add_three _ _⟩
    rw [max_ack_left]
    exact max_le_max (ha n).le (hb n).le
  · exact
      ⟨max a b + 2, fun n =>
        (ha _).trans <| (ack_strictMono_right a <| hb n).trans <| ack_ack_lt_ack_max_add_two a b n⟩
  · 
    have :
      ∀ {m n},
        rec (f m) (fun y IH => g <| pair m <| pair y IH) n < ack (max a b + 9) (m + n) := by
      intro m n
      induction' n with n IH
      · apply (ha m).trans (ack_strictMono_left m <| (le_max_left a b).trans_lt _)
        omega
      · 
        simp only
        apply (hb _).trans ((ack_pair_lt _ _ _).trans_le _)
        cases' lt_or_le _ m with h₁ h₁
        · rw [max_eq_left h₁.le]
          exact ack_le_ack (Nat.add_le_add (le_max_right a b) <| by norm_num)
                           (self_le_add_right m _)
        rw [max_eq_right h₁]
        apply (ack_pair_lt _ _ _).le.trans
        cases' lt_or_le _ n with h₂ h₂
        · rw [max_eq_left h₂.le, add_assoc]
          exact
            ack_le_ack (Nat.add_le_add (le_max_right a b) <| by norm_num)
              ((le_succ n).trans <| self_le_add_left _ _)
        rw [max_eq_right h₂]
        apply (ack_strictMono_right _ IH).le.trans
        rw [add_succ m, add_succ _ 8, succ_eq_add_one, succ_eq_add_one,
            ack_succ_succ (_ + 8), add_assoc]
        exact ack_mono_left _ (Nat.add_le_add (le_max_right a b) le_rfl)
    exact ⟨max a b + 9, fun n => this.trans_le <| ack_mono_right _ <| unpair_add_le n⟩
theorem not_nat_primrec_ack_self : ¬Nat.Primrec fun n => ack n n := fun h => by
  cases' exists_lt_ack_of_nat_primrec h with m hm
  exact (hm m).false
theorem not_primrec_ack_self : ¬Primrec fun n => ack n n := by
  rw [Primrec.nat_iff]
  exact not_nat_primrec_ack_self
theorem not_primrec₂_ack : ¬Primrec₂ ack := fun h =>
  not_primrec_ack_self <| h.comp Primrec.id Primrec.id