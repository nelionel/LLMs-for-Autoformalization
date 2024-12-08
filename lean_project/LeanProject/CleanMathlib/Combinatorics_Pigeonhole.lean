import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.ModEq
universe u v w
variable {α : Type u} {β : Type v} {M : Type w} [DecidableEq β]
open Nat
namespace Finset
variable {s : Finset α} {t : Finset β} {f : α → β} {w : α → M} {b : M} {n : ℕ}
section
variable [LinearOrderedCancelAddCommMonoid M]
theorem exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (hf : ∀ a ∈ s, f a ∈ t)
    (hb : #t • b < ∑ x ∈ s, w x) : ∃ y ∈ t, b < ∑ x ∈ s with f x = y, w x :=
  exists_lt_of_sum_lt <| by simpa only [sum_fiberwise_of_maps_to hf, sum_const]
theorem exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul (hf : ∀ a ∈ s, f a ∈ t)
    (hb : ∑ x ∈ s, w x < #t • b) : ∃ y ∈ t, ∑ x ∈ s with f x = y, w x < b :=
  exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (M := Mᵒᵈ) hf hb
theorem exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
    (ht : ∀ y ∉ t, ∑ x ∈ s with f x = y, w x ≤ 0)
    (hb : #t • b < ∑ x ∈ s, w x) : ∃ y ∈ t, b < ∑ x ∈ s with f x = y, w x :=
  exists_lt_of_sum_lt <|
    calc
      ∑ _y ∈ t, b < ∑ x ∈ s, w x := by simpa
      _ ≤ ∑ y ∈ t, ∑ x ∈ s with f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos ht
theorem exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
    (ht : ∀ y ∉ t, (0 : M) ≤ ∑ x ∈ s with f x = y, w x) (hb : ∑ x ∈ s, w x < #t • b) :
    ∃ y ∈ t, ∑ x ∈ s with f x = y, w x < b :=
  exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum (M := Mᵒᵈ) ht hb
theorem exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty)
    (hb : #t • b ≤ ∑ x ∈ s, w x) : ∃ y ∈ t, b ≤ ∑ x ∈ s with f x = y, w x :=
  exists_le_of_sum_le ht <| by simpa only [sum_fiberwise_of_maps_to hf, sum_const]
theorem exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty)
    (hb : ∑ x ∈ s, w x ≤ #t • b) : ∃ y ∈ t, ∑ x ∈ s with f x = y, w x ≤ b :=
  exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb
theorem exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
    (hf : ∀ y ∉ t, ∑ x ∈ s with f x = y, w x ≤ 0) (ht : t.Nonempty)
    (hb : #t • b ≤ ∑ x ∈ s, w x) : ∃ y ∈ t, b ≤ ∑ x ∈ s with f x = y, w x :=
  exists_le_of_sum_le ht <|
    calc
      ∑ _y ∈ t, b ≤ ∑ x ∈ s, w x := by simpa
      _ ≤ ∑ y ∈ t, ∑ x ∈ s with f x = y, w x :=
        sum_le_sum_fiberwise_of_sum_fiber_nonpos hf
theorem exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
    (hf : ∀ y ∉ t, (0 : M) ≤ ∑ x ∈ s with f x = y, w x) (ht : t.Nonempty)
    (hb : ∑ x ∈ s, w x ≤ #t • b) : ∃ y ∈ t, ∑ x ∈ s with f x = y, w x ≤ b :=
  exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum (M := Mᵒᵈ) hf ht hb
end
variable [LinearOrderedCommSemiring M]
theorem exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t)
    (ht : #t • b < #s) : ∃ y ∈ t, b < #{x ∈ s | f x = y} := by
  simp_rw [cast_card] at ht ⊢
  exact exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf ht
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t)
    (hn : #t * n < #s) : ∃ y ∈ t, n < #{x ∈ s | f x = y} :=
  exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hf hn
theorem exists_card_fiber_lt_of_card_lt_nsmul (ht : #s < #t • b) :
    ∃ y ∈ t, #{x ∈ s | f x = y} < b := by
  simp_rw [cast_card] at ht ⊢
  exact
    exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht
theorem exists_card_fiber_lt_of_card_lt_mul (hn : #s < #t * n) : ∃ y ∈ t, #{x ∈ s | f x = y} < n :=
  exists_card_fiber_lt_of_card_lt_nsmul hn
theorem exists_le_card_fiber_of_nsmul_le_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty)
    (hb : #t • b ≤ #s) : ∃ y ∈ t, b ≤ #{x ∈ s | f x = y} := by
  simp_rw [cast_card] at hb ⊢
  exact exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb
theorem exists_le_card_fiber_of_mul_le_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty)
    (hn : #t * n ≤ #s) : ∃ y ∈ t, n ≤ #{x ∈ s | f x = y} :=
  exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hn
theorem exists_card_fiber_le_of_card_le_nsmul (ht : t.Nonempty) (hb : #s ≤ #t • b) :
    ∃ y ∈ t, #{x ∈ s | f x = y} ≤ b := by
  simp_rw [cast_card] at hb ⊢
  refine
    exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
      (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht hb
theorem exists_card_fiber_le_of_card_le_mul (ht : t.Nonempty) (hn : #s ≤ #t * n) :
    ∃ y ∈ t, #{x ∈ s | f x = y} ≤ n :=
  exists_card_fiber_le_of_card_le_nsmul ht hn
end Finset
namespace Fintype
open Finset
variable [Fintype α] [Fintype β] (f : α → β) {w : α → M} {b : M} {n : ℕ}
section
variable [LinearOrderedCancelAddCommMonoid M]
theorem exists_lt_sum_fiber_of_nsmul_lt_sum (hb : card β • b < ∑ x, w x) :
    ∃ y, b < ∑ x with f x = y, w x :=
  let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (fun _ _ => mem_univ _) hb
  ⟨y, hy⟩
theorem exists_le_sum_fiber_of_nsmul_le_sum [Nonempty β] (hb : card β • b ≤ ∑ x, w x) :
    ∃ y, b ≤ ∑ x with f x = y, w x :=
  let ⟨y, _, hy⟩ :=
    exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, hy⟩
theorem exists_sum_fiber_lt_of_sum_lt_nsmul (hb : ∑ x, w x < card β • b) :
    ∃ y, ∑ x with f x = y, w x < b :=
  exists_lt_sum_fiber_of_nsmul_lt_sum (M := Mᵒᵈ) _ hb
theorem exists_sum_fiber_le_of_sum_le_nsmul [Nonempty β] (hb : ∑ x, w x ≤ card β • b) :
    ∃ y, ∑ x with f x = y, w x ≤ b :=
  exists_le_sum_fiber_of_nsmul_le_sum (M := Mᵒᵈ) _ hb
end
variable [LinearOrderedCommSemiring M]
theorem exists_lt_card_fiber_of_nsmul_lt_card (hb : card β • b < card α) :
    ∃ y : β, b < #{x | f x = y} :=
  let ⟨y, _, h⟩ := exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (fun _ _ => mem_univ _) hb
  ⟨y, h⟩
theorem exists_lt_card_fiber_of_mul_lt_card (hn : card β * n < card α) :
    ∃ y : β, n < #{x | f x = y} :=
  exists_lt_card_fiber_of_nsmul_lt_card _ hn
theorem exists_card_fiber_lt_of_card_lt_nsmul (hb : ↑(card α) < card β • b) :
    ∃ y : β, #{x | f x = y} < b :=
  let ⟨y, _, h⟩ := Finset.exists_card_fiber_lt_of_card_lt_nsmul (f := f) hb
  ⟨y, h⟩
theorem exists_card_fiber_lt_of_card_lt_mul (hn : card α < card β * n) :
    ∃ y : β, #{x | f x = y} < n :=
  exists_card_fiber_lt_of_card_lt_nsmul _ hn
theorem exists_le_card_fiber_of_nsmul_le_card [Nonempty β] (hb : card β • b ≤ card α) :
    ∃ y : β, b ≤ #{x | f x = y} :=
  let ⟨y, _, h⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, h⟩
theorem exists_le_card_fiber_of_mul_le_card [Nonempty β] (hn : card β * n ≤ card α) :
    ∃ y : β, n ≤ #{x | f x = y} :=
  exists_le_card_fiber_of_nsmul_le_card _ hn
theorem exists_card_fiber_le_of_card_le_nsmul [Nonempty β] (hb : ↑(card α) ≤ card β • b) :
    ∃ y : β, #{x | f x = y} ≤ b :=
  let ⟨y, _, h⟩ := Finset.exists_card_fiber_le_of_card_le_nsmul univ_nonempty hb
  ⟨y, h⟩
theorem exists_card_fiber_le_of_card_le_mul [Nonempty β] (hn : card α ≤ card β * n) :
    ∃ y : β, #{x | f x = y} ≤ n :=
  exists_card_fiber_le_of_card_le_nsmul _ hn
end Fintype
namespace Nat
open Set
theorem exists_lt_modEq_of_infinite {s : Set ℕ} (hs : s.Infinite) {k : ℕ} (hk : 0 < k) :
    ∃ m ∈ s, ∃ n ∈ s, m < n ∧ m ≡ n [MOD k] :=
  (hs.exists_lt_map_eq_of_mapsTo fun n _ => show n % k ∈ Iio k from Nat.mod_lt n hk) <|
    finite_lt_nat k
end Nat