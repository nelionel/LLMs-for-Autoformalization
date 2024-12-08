import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.PNat.Basic
namespace Mathlib.Tactic.Ring
instance : CSLift ℕ+ Nat where
  lift := PNat.val
  inj := PNat.coe_injective
instance {n} : CSLiftVal (no_index (OfNat.ofNat (n+1)) : ℕ+) (n + 1) := ⟨rfl⟩
instance {n h} : CSLiftVal (Nat.toPNat n h) n := ⟨rfl⟩
instance {n} : CSLiftVal (Nat.succPNat n) (n + 1) := ⟨rfl⟩
instance {n} : CSLiftVal (Nat.toPNat' n) (n.pred + 1) := ⟨rfl⟩
instance {n k} : CSLiftVal (PNat.divExact n k) (n.div k + 1) := ⟨rfl⟩
instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n + k) (n' + k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩
instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n * k) (n' * k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩
instance {n n' k} [h1 : CSLiftVal (n : ℕ+) n'] :
    CSLiftVal (n ^ k) (n' ^ k) := ⟨by simp [h1.1, CSLift.lift]⟩
end Ring
end Mathlib.Tactic