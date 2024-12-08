import Mathlib.Init
universe u v
variable {α : Sort u} {β : Sort v}
class IsSymmOp (op : α → α → β) : Prop where
  symm_op : ∀ a b, op a b = op b a
class LeftCommutative (op : α → β → β) : Prop where
  left_comm : (a₁ a₂ : α) → (b : β) → op a₁ (op a₂ b) = op a₂ (op a₁ b)
class RightCommutative (op : β → α → β) : Prop where
  right_comm : (b : β) → (a₁ a₂ : α) → op (op b a₁) a₂ = op (op b a₂) a₁
instance (priority := 100) isSymmOp_of_isCommutative (α : Sort u) (op : α → α → α)
    [Std.Commutative op] : IsSymmOp op where symm_op := Std.Commutative.comm
theorem IsSymmOp.flip_eq (op : α → α → β) [IsSymmOp op] : flip op = op :=
  funext fun a ↦ funext fun b ↦ (IsSymmOp.symm_op a b).symm
instance {f : α → β → β} [h : LeftCommutative f] : RightCommutative (fun x y ↦ f y x) :=
  ⟨fun _ _ _ ↦ (h.left_comm _ _ _).symm⟩
instance {f : β → α → β} [h : RightCommutative f] : LeftCommutative (fun x y ↦ f y x) :=
  ⟨fun _ _ _ ↦ (h.right_comm _ _ _).symm⟩
instance {f : α → α → α} [hc : Std.Commutative f] [ha : Std.Associative f] : LeftCommutative f :=
  ⟨fun a b c ↦ by rw [← ha.assoc, hc.comm a, ha.assoc]⟩
instance {f : α → α → α} [hc : Std.Commutative f] [ha : Std.Associative f] : RightCommutative f :=
  ⟨fun a b c ↦ by rw [ha.assoc, hc.comm b, ha.assoc]⟩