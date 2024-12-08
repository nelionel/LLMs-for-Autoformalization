import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Order.Filter.AtTopBot.Ring
namespace Filter
variable {α β : Type*}
section LinearOrderedSemifield
variable [LinearOrderedSemifield α] {l : Filter β} {f : β → α} {r c : α} {n : ℕ}
theorem tendsto_const_mul_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop :=
  ⟨fun h => h.atTop_of_const_mul hr, fun h =>
    Tendsto.atTop_of_const_mul (inv_pos.2 hr) <| by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩
theorem tendsto_mul_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr
lemma tendsto_div_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atTop := by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)
theorem tendsto_const_mul_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r := by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_lt hrx
theorem tendsto_mul_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]
lemma tendsto_div_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r := by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]
theorem Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_pos hr).2 hf
theorem Tendsto.atTop_mul_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_pos hr).2 hf
theorem Tendsto.atTop_div_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atTop := by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)
theorem tendsto_const_mul_pow_atTop (hn : n ≠ 0) (hc : 0 < c) :
    Tendsto (fun x => c * x ^ n) atTop atTop :=
  Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)
theorem tendsto_const_mul_pow_atTop_iff :
    Tendsto (fun x => c * x ^ n) atTop atTop ↔ n ≠ 0 ∧ 0 < c := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)
lemma tendsto_zpow_atTop_atTop {n : ℤ} (hn : 0 < n) : Tendsto (fun x : α ↦ x ^ n) atTop atTop := by
  lift n to ℕ+ using hn; simp
end LinearOrderedSemifield
section LinearOrderedField
variable [LinearOrderedField α] {l : Filter β} {f : β → α} {r : α}
theorem tendsto_const_mul_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot := by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr
theorem tendsto_mul_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr
lemma tendsto_div_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]
theorem tendsto_const_mul_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot := by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)
theorem tendsto_mul_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr
lemma tendsto_div_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]
theorem tendsto_const_mul_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop := by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)
theorem tendsto_mul_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr
lemma tendsto_div_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]
theorem tendsto_const_mul_atTop_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_lt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_lt, tendsto_const_mul_atTop_of_pos]
theorem tendsto_mul_const_atTop_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]
lemma tendsto_div_const_atTop_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]
theorem tendsto_const_mul_atBot_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]
theorem tendsto_mul_const_atBot_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]
lemma tendsto_div_const_atBot_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]
theorem tendsto_const_mul_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop ↔ r < 0 := by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]
theorem tendsto_mul_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]
lemma tendsto_div_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]
theorem tendsto_const_mul_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]
theorem tendsto_mul_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]
lemma tendsto_div_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]
theorem tendsto_const_mul_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot ↔ r < 0 := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]
theorem tendsto_mul_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]
lemma tendsto_div_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]
theorem Tendsto.const_mul_atTop_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_neg hr).2 hf
theorem Tendsto.atTop_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_neg hr).2 hf
lemma Tendsto.atTop_div_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot := (tendsto_div_const_atBot_of_neg hr).2 hf
theorem Tendsto.const_mul_atBot (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_pos hr).2 hf
theorem Tendsto.atBot_mul_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_pos hr).2 hf
theorem Tendsto.atBot_div_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atBot := (tendsto_div_const_atBot_of_pos hr).2 hf
theorem Tendsto.const_mul_atBot_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_neg hr).2 hf
theorem Tendsto.atBot_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_neg hr).2 hf
theorem tendsto_neg_const_mul_pow_atTop {c : α} {n : ℕ} (hn : n ≠ 0) (hc : c < 0) :
    Tendsto (fun x => c * x ^ n) atTop atBot :=
  (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc
theorem tendsto_const_mul_pow_atBot_iff {c : α} {n : ℕ} :
    Tendsto (fun x => c * x ^ n) atTop atBot ↔ n ≠ 0 ∧ c < 0 := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]
@[deprecated (since := "2024-05-06")]
alias Tendsto.neg_const_mul_atTop := Tendsto.const_mul_atTop_of_neg
@[deprecated (since := "2024-05-06")]
alias Tendsto.atTop_mul_neg_const := Tendsto.atTop_mul_const_of_neg
@[deprecated (since := "2024-05-06")]
alias Tendsto.neg_const_mul_atBot := Tendsto.const_mul_atBot_of_neg
@[deprecated (since := "2024-05-06")]
alias Tendsto.atBot_mul_neg_const := Tendsto.atBot_mul_const_of_neg
end LinearOrderedField
end Filter