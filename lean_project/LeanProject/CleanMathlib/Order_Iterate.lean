import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic
open Function
open Function (Commute)
namespace Monotone
variable {α : Type*} [Preorder α] {f : α → α} {x y : ℕ → α}
theorem seq_le_seq (hf : Monotone f) (n : ℕ) (h₀ : x 0 ≤ y 0) (hx : ∀ k < n, x (k + 1) ≤ f (x k))
    (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n ≤ y n := by
  induction n with
  | zero => exact h₀
  | succ n ihn =>
    refine (hx _ n.lt_succ_self).trans ((hf <| ihn ?_ ?_).trans (hy _ n.lt_succ_self))
    · exact fun k hk => hx _ (hk.trans n.lt_succ_self)
    · exact fun k hk => hy _ (hk.trans n.lt_succ_self)
theorem seq_pos_lt_seq_of_lt_of_le (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  induction n with
  | zero => exact hn.false.elim
  | succ n ihn =>
  suffices x n ≤ y n from (hx n n.lt_succ_self).trans_le ((hf this).trans <| hy n n.lt_succ_self)
  cases n with
  | zero => exact h₀
  | succ n =>
    refine (ihn n.zero_lt_succ (fun k hk => hx _ ?_) fun k hk => hy _ ?_).le <;>
    exact hk.trans n.succ.lt_succ_self
theorem seq_pos_lt_seq_of_le_of_lt (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_pos_lt_seq_of_lt_of_le hn h₀ hy hx
theorem seq_lt_seq_of_lt_of_le (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  cases n
  exacts [h₀, hf.seq_pos_lt_seq_of_lt_of_le (Nat.zero_lt_succ _) h₀.le hx hy]
theorem seq_lt_seq_of_le_of_lt (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_lt_seq_of_lt_of_le n h₀ hy hx
variable {β : Type*} {g : β → β} {h : β → α}
open Function
theorem le_iterate_comp_of_le (hf : Monotone f) (H : h ∘ g ≤ f ∘ h) (n : ℕ) :
    h ∘ g^[n] ≤ f^[n] ∘ h := fun x => by
  apply hf.seq_le_seq n <;> intros <;>
    simp [iterate_succ', -iterate_succ, comp_apply, id_eq, le_refl]
  case hx => exact H _
theorem iterate_comp_le_of_le (hf : Monotone f) (H : f ∘ h ≤ h ∘ g) (n : ℕ) :
    f^[n] ∘ h ≤ h ∘ g^[n] :=
  hf.dual.le_iterate_comp_of_le H n
theorem iterate_le_of_le {g : α → α} (hf : Monotone f) (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  hf.iterate_comp_le_of_le h n
theorem le_iterate_of_le {g : α → α} (hg : Monotone g) (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  hg.dual.iterate_le_of_le h n
end Monotone
namespace Function
section Preorder
variable {α : Type*} [Preorder α] {f : α → α}
theorem id_le_iterate_of_id_le (h : id ≤ f) (n : ℕ) : id ≤ f^[n] := by
  simpa only [iterate_id] using monotone_id.iterate_le_of_le h n
theorem iterate_le_id_of_le_id (h : f ≤ id) (n : ℕ) : f^[n] ≤ id :=
  @id_le_iterate_of_id_le αᵒᵈ _ f h n
theorem monotone_iterate_of_id_le (h : id ≤ f) : Monotone fun m => f^[m] :=
  monotone_nat_of_le_succ fun n x => by
    rw [iterate_succ_apply']
    exact h _
theorem antitone_iterate_of_le_id (h : f ≤ id) : Antitone fun m => f^[m] := fun m n hmn =>
  @monotone_iterate_of_id_le αᵒᵈ _ f h m n hmn
end Preorder
namespace Commute
section Preorder
variable {α : Type*} [Preorder α] {f g : α → α}
theorem iterate_le_of_map_le (h : Commute f g) (hf : Monotone f) (hg : Monotone g) {x}
    (hx : f x ≤ g x) (n : ℕ) : f^[n] x ≤ g^[n] x := by
  apply hf.seq_le_seq n
  · rfl
  · intros; rw [iterate_succ_apply']
  · intros; simp [h.iterate_right _ _, hg.iterate _ hx]
theorem iterate_pos_lt_of_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x := by
  apply hf.seq_pos_lt_seq_of_le_of_lt hn
  · rfl
  · intros; rw [iterate_succ_apply']
  · intros; simp [h.iterate_right _ _, hg.iterate _ hx]
theorem iterate_pos_lt_of_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x :=
  @iterate_pos_lt_of_map_lt αᵒᵈ _ g f h.symm hg.dual hf.dual x hx n hn
end Preorder
variable {α : Type*} [LinearOrder α] {f g : α → α}
theorem iterate_pos_lt_iff_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x := by
  rcases lt_trichotomy (f x) (g x) with (H | H | H)
  · simp only [*, iterate_pos_lt_of_map_lt]
  · simp only [*, h.iterate_eq_of_map_eq, lt_irrefl]
  · simp only [lt_asymm H, lt_asymm (h.symm.iterate_pos_lt_of_map_lt' hg hf H hn)]
theorem iterate_pos_lt_iff_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x :=
  @iterate_pos_lt_iff_map_lt αᵒᵈ _ _ _ h.symm hg.dual hf.dual x n hn
theorem iterate_pos_le_iff_map_le (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt' hg hf hn)
theorem iterate_pos_le_iff_map_le' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt hg hf hn)
theorem iterate_pos_eq_iff_map_eq (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x = g^[n] x ↔ f x = g x := by
  simp only [le_antisymm_iff, h.iterate_pos_le_iff_map_le hf hg hn,
    h.symm.iterate_pos_le_iff_map_le' hg hf hn]
end Commute
end Function
namespace Monotone
variable {α : Type*} [Preorder α] {f : α → α} {x : α}
theorem monotone_iterate_of_le_map (hf : Monotone f) (hx : x ≤ f x) : Monotone fun n => f^[n] x :=
  monotone_nat_of_le_succ fun n => by
    rw [iterate_succ_apply]
    exact hf.iterate n hx
theorem antitone_iterate_of_map_le (hf : Monotone f) (hx : f x ≤ x) : Antitone fun n => f^[n] x :=
  hf.dual.monotone_iterate_of_le_map hx
end Monotone
namespace StrictMono
variable {α : Type*} [Preorder α] {f : α → α} {x : α}
theorem strictMono_iterate_of_lt_map (hf : StrictMono f) (hx : x < f x) :
    StrictMono fun n => f^[n] x :=
  strictMono_nat_of_lt_succ fun n => by
    rw [iterate_succ_apply]
    exact hf.iterate n hx
theorem strictAnti_iterate_of_map_lt (hf : StrictMono f) (hx : f x < x) :
    StrictAnti fun n => f^[n] x :=
  hf.dual.strictMono_iterate_of_lt_map hx
end StrictMono