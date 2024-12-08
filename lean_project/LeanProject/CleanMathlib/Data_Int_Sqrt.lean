import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Common
namespace Int
@[pp_nodot]
def sqrt (z : ℤ) : ℤ :=
  Nat.sqrt <| Int.toNat z
theorem sqrt_eq (n : ℤ) : sqrt (n * n) = n.natAbs := by
  rw [sqrt, ← natAbs_mul_self, toNat_natCast, Nat.sqrt_eq]
theorem exists_mul_self (x : ℤ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.ofNat_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩
theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
  natCast_nonneg _
@[simp, norm_cast]
theorem sqrt_natCast (n : ℕ) : Int.sqrt (n : ℤ) = Nat.sqrt n := by rw [sqrt, toNat_ofNat]
@[simp]
theorem sqrt_ofNat (n : ℕ) : Int.sqrt (no_index (OfNat.ofNat n) : ℤ) = Nat.sqrt (OfNat.ofNat n) :=
  sqrt_natCast _
end Int