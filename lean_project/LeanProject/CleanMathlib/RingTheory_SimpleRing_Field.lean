import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Field.Equiv
namespace IsSimpleRing
open TwoSidedIdeal in
lemma isField_center (A : Type*) [Ring A] [IsSimpleRing A] : IsField (Subring.center A) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    rintro ⟨x, hx1⟩ hx2
    rw [Subring.mem_center_iff] at hx1
    replace hx2 : x ≠ 0 := by simpa [Subtype.ext_iff] using hx2
    let I := TwoSidedIdeal.mk' (Set.range (x * ·)) ⟨0, by simp⟩
      (by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, mul_add _ _ _⟩)
      (by rintro _ ⟨x, rfl⟩; exact ⟨-x, by simp⟩)
      (by rintro a _ ⟨c, rfl⟩; exact ⟨a * c, by dsimp; rw [← mul_assoc, ← hx1, mul_assoc]⟩)
      (by rintro _ b ⟨a, rfl⟩; exact ⟨a * b, by dsimp; rw [← mul_assoc, ← hx1, mul_assoc]⟩)
    have mem : 1 ∈ I := one_mem_of_ne_zero_mem I hx2 (by simpa [I, mem_mk'] using ⟨1, by simp⟩)
    simp only [TwoSidedIdeal.mem_mk', Set.mem_range, I] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨⟨y, Subring.mem_center_iff.2 fun a ↦ ?_⟩, by ext; exact hy⟩
    calc a * y
      _ = (x * y) * a * y := by rw [hy, one_mul]
      _ = (y * x) * a * y := by rw [hx1]
      _ = y * (x * a) * y := by rw [mul_assoc y x a]
      _ = y * (a * x) * y := by rw [hx1]
      _ = y * ((a * x) * y) := by rw [mul_assoc]
      _ = y * (a * (x * y)) := by rw [mul_assoc a x y]
      _ = y * a := by rw [hy, mul_one]
end IsSimpleRing
lemma isSimpleRing_iff_isField (A : Type*) [CommRing A] : IsSimpleRing A ↔ IsField A :=
  ⟨fun _ ↦ Subring.topEquiv.symm.toMulEquiv.isField _ <| by
    rw [← Subring.center_eq_top A]; exact IsSimpleRing.isField_center A,
    fun h ↦ letI := h.toField; inferInstance⟩