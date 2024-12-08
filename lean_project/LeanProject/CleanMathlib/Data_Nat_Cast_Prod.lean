import Mathlib.Algebra.Group.Prod
assert_not_exists MonoidWithZero
variable {α β : Type*}
namespace Prod
variable [AddMonoidWithOne α] [AddMonoidWithOne β]
instance instAddMonoidWithOne : AddMonoidWithOne (α × β) :=
  { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }
@[simp]
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]
@[simp]
theorem fst_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : α × β)).1 = (OfNat.ofNat n : α) :=
  rfl
@[simp]
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]
@[simp]
theorem snd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : α × β)).2 = (OfNat.ofNat n : β) :=
  rfl
end Prod