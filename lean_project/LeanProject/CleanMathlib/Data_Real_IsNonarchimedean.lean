import Mathlib.Algebra.Order.Hom.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Choose.Sum
namespace IsNonarchimedean
open IsUltrametricDist
theorem add_le {α : Type*} [Add α] {f : α → ℝ} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩
theorem nsmul_le {F α : Type*} [AddGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  let _ := AddGroupSeminormClass.toSeminormedAddGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddGroup_norm_eq]
  exact norm_nsmul_le _ _
theorem nmul_le {F α : Type*} [Ring α] [FunLike F α ℝ] [AddGroupSeminormClass F α ℝ]
    {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  let _ := AddGroupSeminormClass.toSeminormedAddGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddGroup_norm_eq] at hne ⊢
  exact norm_add_eq_max_of_norm_ne_norm hne
theorem finset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  let _ := AddGroupSeminormClass.toSeminormedAddCommGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddCommGroup_norm_eq]
  apply exists_norm_finset_sum_le
theorem finset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b : β, (b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  obtain ⟨b, hbt, hbf⟩ := finset_image_add hna g t
  exact ⟨b, hbt ht, hbf⟩
theorem multiset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (s : Multiset β) :
    ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  let _ := AddGroupSeminormClass.toSeminormedAddCommGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddCommGroup_norm_eq]
  apply exists_norm_multiset_sum_le
theorem multiset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  obtain ⟨b, hbs, hbf⟩ := multiset_image_add hna g s
  exact ⟨b, hbs hs, hbf⟩
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a b : α) :
    ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    if_true, forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))
end IsNonarchimedean