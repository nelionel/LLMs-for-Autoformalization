import Mathlib.Data.Nat.Notation
def PNat := { n : ℕ // 0 < n } deriving DecidableEq
@[inherit_doc]
notation "ℕ+" => PNat
@[coe]
def PNat.val : ℕ+ → ℕ := Subtype.val
instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩
instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩