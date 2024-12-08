import Mathlib.SetTheory.Game.State
namespace SetTheory
namespace PGame
namespace Domineering
open Function
@[simps!]
def shiftUp : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.refl ℤ).prodCongr (Equiv.addRight (1 : ℤ))
@[simps!]
def shiftRight : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl ℤ)
abbrev Board :=
  Finset (ℤ × ℤ)
def left (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftUp
def right (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftRight
theorem mem_left {b : Board} (x : ℤ × ℤ) : x ∈ left b ↔ x ∈ b ∧ (x.1, x.2 - 1) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
theorem mem_right {b : Board} (x : ℤ × ℤ) : x ∈ right b ↔ x ∈ b ∧ (x.1 - 1, x.2) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
def moveLeft (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1, m.2 - 1)
def moveRight (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1 - 1, m.2)
theorem fst_pred_mem_erase_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    (m.1 - 1, m.2) ∈ b.erase m := by
  rw [mem_right] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.fst (pred_ne_self m.1)
theorem snd_pred_mem_erase_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    (m.1, m.2 - 1) ∈ b.erase m := by
  rw [mem_left] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.snd (pred_ne_self m.2)
theorem card_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m := snd_pred_mem_erase_of_mem_left h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
theorem card_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ := fst_pred_mem_erase_of_mem_right h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
theorem moveLeft_card {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    Finset.card (moveLeft b m) + 2 = Finset.card b := by
  dsimp only [moveLeft]
  rw [Finset.card_erase_of_mem (snd_pred_mem_erase_of_mem_left h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_left h)
theorem moveRight_card {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    Finset.card (moveRight b m) + 2 = Finset.card b := by
  dsimp only [moveRight]
  rw [Finset.card_erase_of_mem (fst_pred_mem_erase_of_mem_right h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_right h)
theorem moveLeft_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    Finset.card (moveLeft b m) / 2 < Finset.card b / 2 := by simp [← moveLeft_card h, lt_add_one]
theorem moveRight_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    Finset.card (moveRight b m) / 2 < Finset.card b / 2 := by simp [← moveRight_card h, lt_add_one]
instance state : State Board where
  turnBound s := s.card / 2
  l s := (left s).image (moveLeft s)
  r s := (right s).image (moveRight s)
  left_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact moveLeft_smaller h
  right_bound m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact moveRight_smaller h
end Domineering
def domineering (b : Domineering.Board) : PGame :=
  PGame.ofState b
instance shortDomineering (b : Domineering.Board) : Short (domineering b) := by
  dsimp only [domineering]
  infer_instance
def domineering.one :=
  domineering [(0, 0), (0, 1)].toFinset
def domineering.L :=
  domineering [(0, 2), (0, 1), (0, 0), (1, 0)].toFinset
instance shortOne : Short domineering.one := by dsimp [domineering.one]; infer_instance
instance shortL : Short domineering.L := by dsimp [domineering.L]; infer_instance
end PGame
end SetTheory