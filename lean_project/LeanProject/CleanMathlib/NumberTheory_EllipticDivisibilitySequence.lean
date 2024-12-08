import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
universe u v
variable {R : Type u} [CommRing R]
section IsEllDivSequence
variable (W : ℤ → R)
def IsEllSequence : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2
def IsDivSequence : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n
def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W
lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ => by simp only [id_eq]; ring1
lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ => Int.ofNat_dvd.mpr
theorem isEllDivSequence_id : IsEllDivSequence id :=
  ⟨isEllSequence_id, isDivSequence_id⟩
variable {W}
lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp only [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r
lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r
lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩
end IsEllDivSequence
@[elab_as_elim]
noncomputable def normEDSRec' {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])
@[elab_as_elim]
noncomputable def normEDSRec {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
    P n :=
  normEDSRec' zero one two three four
    (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n
variable (b c d : R)
section PreNormEDS
def preNormEDS' (b c d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => let m := n / 2
    have h4 : m + 4 < n + 5 := Nat.lt_succ.mpr <| add_le_add_right (n.div_le_self 2) 4
    have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
    have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
    have _ : m + 1 < n + 5 := (lt_add_one _).trans h2
    if hn : Even n then
      preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have _ : m + 5 < n + 5 := add_lt_add_right
        (Nat.div_lt_self (Nat.not_even_iff_odd.1 hn).pos <| Nat.lt_succ_self 1) 5
      preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
        preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2
@[simp]
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']
@[simp]
lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  rw [preNormEDS']
@[simp]
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']
@[simp]
lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by
  rw [preNormEDS']
@[simp]
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']
lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul _]
  simp only [m.mul_div_cancel_left two_pos]
lemma preNormEDS'_even (m : ℕ) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl, preNormEDS', dif_neg m.not_even_two_mul_add_one]
  simp only [Nat.mul_add_div two_pos]
  rfl
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs
@[simp]
lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · rw [hn, preNormEDS, Nat.cast_zero, Int.sign_zero, Int.cast_zero, zero_mul, preNormEDS'_zero]
  · rw [preNormEDS, Int.sign_natCast_of_ne_zero hn, Int.cast_one, one_mul, Int.natAbs_cast]
@[simp]
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  erw [preNormEDS_ofNat, preNormEDS'_zero]
@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  erw [preNormEDS_ofNat, preNormEDS'_one]
@[simp]
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  erw [preNormEDS_ofNat, preNormEDS'_two]
@[simp]
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  erw [preNormEDS_ofNat, preNormEDS'_three]
@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  erw [preNormEDS_ofNat, preNormEDS'_four]
lemma preNormEDS_even_ofNat (m : ℕ) : preNormEDS b c d (2 * (m + 3)) =
    preNormEDS b c d (m + 2) ^ 2 * preNormEDS b c d (m + 3) * preNormEDS b c d (m + 5) -
      preNormEDS b c d (m + 1) * preNormEDS b c d (m + 3) * preNormEDS b c d (m + 4) ^ 2 := by
  repeat erw [preNormEDS_ofNat]
  exact preNormEDS'_even ..
lemma preNormEDS_odd_ofNat (m : ℕ) : preNormEDS b c d (2 * (m + 2) + 1) =
    preNormEDS b c d (m + 4) * preNormEDS b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m + 1) * preNormEDS b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  repeat erw [preNormEDS_ofNat]
  exact preNormEDS'_odd ..
@[simp]
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  rw [preNormEDS, Int.sign_neg, Int.cast_neg, neg_mul, Int.natAbs_neg, preNormEDS]
lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =
    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -
      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    · simp
    · simp
    · simp
    · simp only [Int.natCast_add, Nat.cast_one]
      rw [Int.add_sub_cancel, show (m : ℤ) + 1 + 1 + 1 = m + 1 + 2 by rfl, Int.add_sub_cancel]
      exact preNormEDS_even_ofNat ..
  | neg h m =>
    simp_rw [show 2 * -(m : ℤ) = -(2 * m) by omega, show -(m : ℤ) - 1 = -(m + 1) by omega,
      show -(m : ℤ) + 2 = -(m - 2) by omega, show -(m : ℤ) - 2 = -(m + 2) by omega,
      show -(m : ℤ) + 1 = -(m - 1) by omega, preNormEDS_neg, h m]
    ring1
lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =
    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | m
    · simp
    · simp
    · simp only [Int.natCast_add, Nat.cast_one, Int.even_add_one, not_not, Int.even_coe_nat]
      rw [Int.add_sub_cancel]
      exact preNormEDS_odd_ofNat ..
  | neg h m =>
    rcases m with _ | m
    · simp
    · simp_rw [Int.natCast_add, Nat.cast_one, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
        show -(m + 1 : ℤ) + 2 = -(m - 1) by omega, show -(m + 1 : ℤ) - 1 = -(m + 2) by rfl,
        show -(m + 1 : ℤ) + 1 = -m by omega, preNormEDS_neg, even_neg, Int.even_add_one, ite_not,
        h m]
      ring1
end PreNormEDS
section NormEDS
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1
@[simp]
lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  simp only [normEDS, preNormEDS_ofNat, Int.even_coe_nat]
@[simp]
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  erw [normEDS_ofNat, preNormEDS'_zero, zero_mul]
@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  erw [normEDS_ofNat, preNormEDS'_one, one_mul, if_neg Nat.not_even_one]
@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  erw [normEDS_ofNat, preNormEDS'_two, one_mul, if_pos even_two]
@[simp]
lemma normEDS_three : normEDS b c d 3 = c := by
  erw [normEDS_ofNat, preNormEDS'_three, if_neg <| by decide, mul_one]
@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  erw [normEDS_ofNat, preNormEDS'_four, if_pos <| by decide]
lemma normEDS_even_ofNat (m : ℕ) : normEDS b c d (2 * (m + 3)) * b =
    normEDS b c d (m + 2) ^ 2 * normEDS b c d (m + 3) * normEDS b c d (m + 5) -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m + 4) ^ 2 := by
  repeat erw [normEDS_ofNat]
  simp only [preNormEDS'_even, if_pos <| even_two_mul _, Nat.even_add_one, ite_not]
  split_ifs <;> ring1
lemma normEDS_odd_ofNat (m : ℕ) : normEDS b c d (2 * (m + 2) + 1) =
    normEDS b c d (m + 4) * normEDS b c d (m + 2) ^ 3 -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) ^ 3 := by
  repeat erw [normEDS_ofNat]
  simp_rw [preNormEDS'_odd, if_neg (m + 2).not_even_two_mul_add_one, Nat.even_add_one, ite_not]
  split_ifs <;> ring1
@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp only [normEDS, preNormEDS_neg, neg_mul, even_neg]
lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  simp only [normEDS, preNormEDS_even, if_pos <| even_two_mul m, show m + 2 = m + 1 + 1 by ring1,
    Int.even_add_one, show m - 2 = m - 1 - 1 by ring1, Int.even_sub_one, ite_not]
  by_cases hm : Even m
  · simp only [if_pos hm]
    ring1
  · simp only [if_neg hm]
    ring1
lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =
    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 := by
  simp only [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one]
  conv_lhs => rw [← @one_pow R _ 4, ← ite_pow, ← ite_pow]
  simp only [show m + 2 = m + 1 + 1 by ring1, Int.even_add_one, Int.even_sub_one, ite_not]
  ring1
end NormEDS
section Map
variable {S : Type v} [CommRing S] (f : R →+* S)
lemma map_preNormEDS' (n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => rw [preNormEDS'_zero, map_zero, preNormEDS'_zero]
  | one => rw [preNormEDS'_one, map_one, preNormEDS'_one]
  | two => rw [preNormEDS'_two, map_one, preNormEDS'_two]
  | three => rw [preNormEDS'_three, preNormEDS'_three]
  | four => rw [preNormEDS'_four, preNormEDS'_four]
  | _ _ ih =>
    simp only [preNormEDS'_odd, preNormEDS'_even, map_one, map_sub, map_mul, map_pow, apply_ite f]
    repeat rw [ih _ <| by linarith only]
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  rw [preNormEDS, map_mul, map_intCast, map_preNormEDS', preNormEDS]
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  rw [normEDS, map_mul, map_preNormEDS, map_pow, apply_ite f, map_one, normEDS]
end Map