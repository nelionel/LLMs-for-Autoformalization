import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ToAdditive
import Mathlib.Util.AssertExists
assert_not_exists One
assert_not_exists Function.Injective
universe u v w
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hVAdd : α → β → γ
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ
attribute [notation_class  smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs]  HSMul
attribute [notation_class zsmul Simps.zsmulArgs]  HSMul
class VAdd (G : Type u) (P : Type v) where
  vadd : G → P → P
class VSub (G : outParam Type*) (P : Type*) where
  vsub : P → P → G
@[to_additive (attr := ext)]
class SMul (M : Type u) (α : Type v) where
  smul : M → α → α
@[inherit_doc] infixr:65 " +ᵥ " => HVAdd.hVAdd
@[inherit_doc] infixl:65 " -ᵥ " => VSub.vsub
@[inherit_doc] infixr:73 " • " => HSMul.hSMul
@[inherit_doc HSMul.hSMul]
macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)
attribute [to_additive existing] Mul Div HMul instHMul HDiv instHDiv HSMul
attribute [to_additive (reorder := 1 2) SMul] Pow
attribute [to_additive (reorder := 1 2)] HPow
attribute [to_additive existing (reorder := 1 2, 5 6) hSMul] HPow.hPow
attribute [to_additive existing (reorder := 1 2, 4 5) smul] Pow.pow
@[to_additive (attr := default_instance)]
instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul
@[to_additive]
theorem SMul.smul_eq_hSMul {α β} [SMul α β] : (SMul.smul : α → β → β) = HSMul.hSMul := rfl
attribute [to_additive existing (reorder := 1 2)] instHPow
variable {G : Type*}
@[to_additive, notation_class]
class Inv (α : Type u) where
  inv : α → α
@[inherit_doc]
postfix:max "⁻¹" => Inv.inv
section ite
variable {α : Type*} (P : Prop) [Decidable P]
section Mul
variable [Mul α]
@[to_additive]
lemma mul_dite (a : α) (b : P → α) (c : ¬ P → α) :
    (a * if h : P then b h else c h) = if h : P then a * b h else a * c h := by split <;> rfl
@[to_additive]
lemma mul_ite (a b c : α) : (a * if P then b else c) = if P then a * b else a * c := mul_dite ..
@[to_additive]
lemma dite_mul (a : P → α) (b : ¬ P → α) (c : α) :
    (if h : P then a h else b h) * c = if h : P then a h * c else b h * c := by split <;> rfl
@[to_additive]
lemma ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * c := dite_mul ..
attribute [simp] mul_dite dite_mul mul_ite ite_mul
@[to_additive]
lemma dite_mul_dite (a : P → α) (b : ¬ P → α) (c : P → α) (d : ¬ P → α) :
    ((if h : P then a h else b h) * if h : P then c h else d h) =
      if h : P then a h * c h else b h * d h := by split <;> rfl
@[to_additive]
lemma ite_mul_ite (a b c d : α) :
    ((if P then a else b) * if P then c else d) = if P then a * c else b * d := by split <;> rfl
end Mul
section Div
variable [Div α]
@[to_additive]
lemma div_dite (a : α) (b : P → α) (c : ¬ P → α) :
    (a / if h : P then b h else c h) = if h : P then a / b h else a / c h := by split <;> rfl
@[to_additive]
lemma div_ite (a b c : α) : (a / if P then b else c) = if P then a / b else a / c := div_dite ..
@[to_additive]
lemma dite_div (a : P → α) (b : ¬ P → α) (c : α) :
    (if h : P then a h else b h) / c = if h : P then a h / c else b h / c := by split <;> rfl
@[to_additive]
lemma ite_div (a b c : α) : (if P then a else b) / c = if P then a / c else b / c := dite_div ..
@[to_additive]
lemma dite_div_dite (a : P → α) (b : ¬ P → α) (c : P → α) (d : ¬ P → α) :
    ((if h : P then a h else b h) / if h : P then c h else d h) =
      if h : P then a h / c h else b h / d h := by split <;> rfl
@[to_additive]
lemma ite_div_ite (a b c d : α) :
    ((if P then a else b) / if P then c else d) = if P then a / c else b / d := dite_div_dite ..
end Div
end ite