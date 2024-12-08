import Mathlib.Data.Set.Defs
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
@[nolint unusedArguments] def EmptyRelation {α : Sort*} := fun _ _ : α ↦ False
class IsIrrefl (α : Sort*) (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a
class IsRefl (α : Sort*) (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a
class IsSymm (α : Sort*) (r : α → α → Prop) : Prop where
  symm : ∀ a b, r a b → r b a
class IsAsymm (α : Sort*) (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬r b a
class IsAntisymm (α : Sort*) (r : α → α → Prop) : Prop where
  antisymm : ∀ a b, r a b → r b a → a = b
instance (priority := 100) IsAsymm.toIsAntisymm {α : Sort*} (r : α → α → Prop) [IsAsymm α r] :
    IsAntisymm α r where
  antisymm _ _ hx hy := (IsAsymm.asymm _ _ hx hy).elim
class IsTrans (α : Sort*) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c
instance {α : Sort*} {r : α → α → Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩
instance (priority := 100) {α : Sort*} {r : α → α → Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩
class IsTotal (α : Sort*) (r : α → α → Prop) : Prop where
  total : ∀ a b, r a b ∨ r b a
class IsPreorder (α : Sort*) (r : α → α → Prop) extends IsRefl α r, IsTrans α r : Prop
class IsPartialOrder (α : Sort*) (r : α → α → Prop) extends IsPreorder α r, IsAntisymm α r : Prop
class IsLinearOrder (α : Sort*) (r : α → α → Prop) extends IsPartialOrder α r, IsTotal α r : Prop
class IsEquiv (α : Sort*) (r : α → α → Prop) extends IsPreorder α r, IsSymm α r : Prop
class IsStrictOrder (α : Sort*) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r : Prop
class IsStrictWeakOrder (α : Sort*) (lt : α → α → Prop) extends IsStrictOrder α lt : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a
class IsTrichotomous (α : Sort*) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a
class IsStrictTotalOrder (α : Sort*) (lt : α → α → Prop) extends IsTrichotomous α lt,
    IsStrictOrder α lt : Prop
instance eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl
instance iff_isEquiv : IsEquiv Prop Iff where
  symm := @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl
section
variable {α : Sort*} {r : α → α → Prop} {a b c : α}
local infixl:50 " ≺ " => r
lemma irrefl [IsIrrefl α r] (a : α) : ¬a ≺ a := IsIrrefl.irrefl a
lemma refl [IsRefl α r] (a : α) : a ≺ a := IsRefl.refl a
lemma trans [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
lemma symm [IsSymm α r] : a ≺ b → b ≺ a := IsSymm.symm _ _
lemma antisymm [IsAntisymm α r] : a ≺ b → b ≺ a → a = b := IsAntisymm.antisymm _ _
lemma asymm [IsAsymm α r] : a ≺ b → ¬b ≺ a := IsAsymm.asymm _ _
lemma trichotomous [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  IsTrichotomous.trichotomous
instance (priority := 90) isAsymm_of_isTrans_of_isIrrefl [IsTrans α r] [IsIrrefl α r] :
    IsAsymm α r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩
instance IsIrrefl.decide [DecidableRel r] [IsIrrefl α r] :
    IsIrrefl α (fun a b => decide (r a b) = true) where
  irrefl := fun a => by simpa using irrefl a
instance IsRefl.decide [DecidableRel r] [IsRefl α r] :
    IsRefl α (fun a b => decide (r a b) = true) where
  refl := fun a => by simpa using refl a
instance IsTrans.decide [DecidableRel r] [IsTrans α r] :
    IsTrans α (fun a b => decide (r a b) = true) where
  trans := fun a b c => by simpa using trans a b c
instance IsSymm.decide [DecidableRel r] [IsSymm α r] :
    IsSymm α (fun a b => decide (r a b) = true) where
  symm := fun a b => by simpa using symm a b
instance IsAntisymm.decide [DecidableRel r] [IsAntisymm α r] :
    IsAntisymm α (fun a b => decide (r a b) = true) where
  antisymm := fun a b h₁ h₂ => antisymm _ _ (by simpa using h₁) (by simpa using h₂)
instance IsAsymm.decide [DecidableRel r] [IsAsymm α r] :
    IsAsymm α (fun a b => decide (r a b) = true) where
  asymm := fun a b => by simpa using asymm a b
instance IsTotal.decide [DecidableRel r] [IsTotal α r] :
    IsTotal α (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b
instance IsTrichotomous.decide [DecidableRel r] [IsTrichotomous α r] :
    IsTrichotomous α (fun a b => decide (r a b) = true) where
  trichotomous := fun a b => by simpa using trichotomous a b
variable (r)
@[elab_without_expected_type] lemma irrefl_of [IsIrrefl α r] (a : α) : ¬a ≺ a := irrefl a
@[elab_without_expected_type] lemma refl_of [IsRefl α r] (a : α) : a ≺ a := refl a
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := _root_.trans
@[elab_without_expected_type] lemma symm_of [IsSymm α r] : a ≺ b → b ≺ a := symm
@[elab_without_expected_type] lemma asymm_of [IsAsymm α r] : a ≺ b → ¬b ≺ a := asymm
@[elab_without_expected_type]
lemma total_of [IsTotal α r] (a b : α) : a ≺ b ∨ b ≺ a := IsTotal.total _ _
@[elab_without_expected_type]
lemma trichotomous_of [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous
section
def Reflexive := ∀ x, x ≺ x
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z
def Irreflexive := ∀ x, ¬x ≺ x
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y
def Total := ∀ x y, x ≺ y ∨ y ≺ x
@[deprecated Equivalence.refl (since := "2024-09-13")]
theorem Equivalence.reflexive (h : Equivalence r) : Reflexive r := h.refl
@[deprecated Equivalence.symm (since := "2024-09-13")]
theorem Equivalence.symmetric (h : Equivalence r) : Symmetric r :=
  fun _ _ ↦ h.symm
@[deprecated Equivalence.trans (since := "2024-09-13")]
theorem Equivalence.transitive (h : Equivalence r) : Transitive r :=
  fun _ _ _ ↦ h.trans
variable {β : Sort*} (r : β → β → Prop) (f : α → β)
@[deprecated "No deprecation message was provided." (since := "2024-09-13")]
theorem InvImage.trans (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) ↦ h h₁ h₂
@[deprecated "No deprecation message was provided." (since := "2024-09-13")]
theorem InvImage.irreflexive (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) ↦ h (f a) h₁
end
end
section LE
variable {α : Type*} [LE α] {P : α → Prop} {x y : α}
def Minimal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y
def Maximal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → x ≤ y → y ≤ x
lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1
lemma Maximal.prop (h : Maximal P x) : P x :=
  h.1
lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y ≤ x) : x ≤ y :=
  h.2 hy hle
lemma Maximal.le_of_ge (h : Maximal P x) (hy : P y) (hge : x ≤ y) : y ≤ x :=
  h.2 hy hge
end LE
def IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
def IsLowerSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s
@[inherit_doc IsUpperSet]
structure UpperSet (α : Type*) [LE α] where
  carrier : Set α
  upper' : IsUpperSet carrier
extend_docs UpperSet before "The type of upper sets of an order."
@[inherit_doc IsLowerSet]
structure LowerSet (α : Type*) [LE α] where
  carrier : Set α
  lower' : IsLowerSet carrier
extend_docs LowerSet before "The type of lower sets of an order."