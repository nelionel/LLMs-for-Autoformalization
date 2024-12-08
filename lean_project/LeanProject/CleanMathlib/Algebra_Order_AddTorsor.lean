import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Defs
open Function
variable {G P : Type*}
class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a
@[deprecated (since := "2024-07-15")] alias OrderedVAdd := IsOrderedVAdd
@[to_additive]
class IsOrderedSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop where
  protected smul_le_smul_left : ∀ a b : P, a ≤ b → ∀ c : G, c • a ≤ c • b
  protected smul_le_smul_right : ∀ c d : G, c ≤ d → ∀ a : P, c • a ≤ d • a
@[to_additive]
instance [LE G] [LE P] [SMul G P] [IsOrderedSMul G P] : CovariantClass G P (· • ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ IsOrderedSMul.smul_le_smul_left _ _ bc a
@[to_additive]
instance [OrderedCommMonoid G] : IsOrderedSMul G G where
  smul_le_smul_left _ _ := mul_le_mul_left'
  smul_le_smul_right _ _ := mul_le_mul_right'
@[to_additive]
theorem IsOrderedSMul.smul_le_smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d :=
  (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)
@[to_additive]
theorem Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [IsOrderedSMul G P] {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)
class IsCancelVAdd (G P : Type*) [VAdd G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b
@[deprecated (since := "2024-07-15")] alias CancelVAdd := IsCancelVAdd
@[to_additive]
class IsCancelSMul (G P : Type*) [SMul G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a • b = a • c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a • c = b • c → a = b
class IsOrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] extends
    IsOrderedVAdd G P : Prop where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b
@[deprecated (since := "2024-07-15")] alias OrderedCancelVAdd := IsOrderedCancelVAdd
@[to_additive]
class IsOrderedCancelSMul (G P : Type*) [LE G] [LE P] [SMul G P] extends
    IsOrderedSMul G P : Prop where
  protected le_of_smul_le_smul_left : ∀ (a : G) (b c : P), a • b ≤ a • c → b ≤ c
  protected le_of_smul_le_smul_right : ∀ (a b : G) (c : P), a • c ≤ b • c → a ≤ b
@[to_additive]
instance [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] :
    IsCancelSMul G P where
  left_cancel a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)
@[to_additive]
instance [OrderedCancelCommMonoid G] : IsOrderedCancelSMul G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'
@[to_additive]
instance (priority := 200) [LE G] [LE P] [SMul G P] [IsOrderedCancelSMul G P] :
    ContravariantClass G P (· • ·) (· ≤ ·) :=
  ⟨IsOrderedCancelSMul.le_of_smul_le_smul_left⟩
namespace SMul
@[to_additive]
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
  a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]
@[to_additive]
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]
end SMul