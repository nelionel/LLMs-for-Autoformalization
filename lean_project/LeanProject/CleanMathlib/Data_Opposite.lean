import Mathlib.Logic.Equiv.Defs
universe v u
variable (α : Sort u)
structure Opposite where
  op ::
  unop : α
attribute [pp_nodot] Opposite.unop
@[app_unexpander Opposite.op]
protected def Opposite.unexpander_op : Lean.PrettyPrinter.Unexpander
  | s => pure s
@[inherit_doc]
notation:max 
α "ᵒᵖ" => Opposite α
namespace Opposite
variable {α}
theorem op_injective : Function.Injective (op : α → αᵒᵖ) := fun _ _ => congr_arg Opposite.unop
theorem unop_injective : Function.Injective (unop : αᵒᵖ → α) := fun ⟨_⟩⟨_⟩ => by simp
@[simp]
theorem op_unop (x : αᵒᵖ) : op (unop x) = x :=
  rfl
theorem unop_op (x : α) : unop (op x) = x :=
  rfl
theorem op_inj_iff (x y : α) : op x = op y ↔ x = y :=
  op_injective.eq_iff
@[simp]
theorem unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff
def equivToOpposite : α ≃ αᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
theorem op_surjective : Function.Surjective (op : α → αᵒᵖ) := equivToOpposite.surjective
theorem unop_surjective : Function.Surjective (unop : αᵒᵖ → α) := equivToOpposite.symm.surjective
@[simp]
theorem equivToOpposite_coe : (equivToOpposite : α → αᵒᵖ) = op :=
  rfl
@[simp]
theorem equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ → α) = unop :=
  rfl
theorem op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y :=
  equivToOpposite.apply_eq_iff_eq_symm_apply
theorem unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y :=
  equivToOpposite.symm.apply_eq_iff_eq_symm_apply
instance [Inhabited α] : Inhabited αᵒᵖ :=
  ⟨op default⟩
instance [Nonempty α] : Nonempty αᵒᵖ := Nonempty.map op ‹_›
instance [Subsingleton α] : Subsingleton αᵒᵖ := unop_injective.subsingleton
@[simp, induction_eliminator]
protected def rec' {F : αᵒᵖ → Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)
end Opposite