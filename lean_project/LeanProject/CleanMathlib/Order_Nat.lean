import Mathlib.Order.BoundedOrder.Basic
namespace Nat
instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le
instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩
@[simp, nolint simpNF] protected lemma bot_eq_zero : ⊥ = 0 := rfl
end Nat