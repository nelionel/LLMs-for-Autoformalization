import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Tactic.Spread
assert_not_exists MonoidWithZero
open Function (Injective Surjective)
variable {M N G H α β γ δ : Type*}
@[to_additive "See also `AddMonoid.toAddAction`"]
instance (priority := 910) Mul.toSMul (α : Type*) [Mul α] : SMul α α := ⟨(· * ·)⟩
@[to_additive (attr := simp)]
lemma smul_eq_mul (α : Type*) [Mul α] {a a' : α} : a • a' = a * a' := rfl
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
@[to_additive (attr := ext)]
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  protected one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b
class VAddCommClass (M N α : Type*) [VAdd M α] [VAdd N α] : Prop where
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)
@[to_additive]
class SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a
export MulAction (mul_smul)
export AddAction (add_vadd)
export SMulCommClass (smul_comm)
export VAddCommClass (vadd_comm)
library_note "bundled maps over different rings"
@[to_additive]
lemma SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α where smul_comm a' a b := (smul_comm a a' b).symm
add_decl_doc VAddCommClass.symm
@[to_additive]
lemma Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Injective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]
@[to_additive]
lemma Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Surjective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]
@[to_additive]
instance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α where
  smul_comm a a' b := by rw [← mul_smul, mul_comm, mul_smul]
class VAddAssocClass (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  vadd_assoc : ∀ (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z
@[to_additive VAddAssocClass] 
class IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z
@[to_additive (attr := simp)]
lemma smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z
@[to_additive]
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α := ⟨mul_assoc⟩
class IsCentralVAdd (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  op_vadd_eq_vadd : ∀ (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a
@[to_additive]
class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α] : Prop where
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a
@[to_additive]
lemma IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm
export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)
attribute [simp] IsCentralScalar.op_smul_eq_smul
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩
@[to_additive]
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩
@[to_additive]
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α where
  smul_assoc m n a := by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]
@[to_additive]
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α where
  smul_assoc m n a := by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]
namespace SMul
variable [SMul M α]
@[to_additive (attr := simp) " Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. "]
def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a
variable (α)
@[to_additive
"An additive action of `M` on `α` and a function `N → M` induces an additive action of `N` on `α`."]
abbrev comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
variable {α}
@[to_additive
"Given a tower of additive actions `M → α → β`, if we use `SMul.comp` to pull back both of
`M`'s actions by a map `g : N → M`, then we obtain a new tower of scalar actions `N → α → β`.
This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables."]
lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)
@[to_additive
"This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables."]
lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)
@[to_additive
"This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables."]
lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)
end SMul
section
@[to_additive] 
lemma mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm
@[to_additive] 
lemma smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y
@[to_additive]
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]
@[to_additive]
lemma smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]
@[to_additive]
lemma smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * (c • d) = (a * c) • (b * d) := by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d
@[to_additive]
alias smul_mul_smul := smul_mul_smul_comm
attribute [deprecated smul_mul_smul_comm (since := "2024-08-29")] smul_mul_smul
attribute [deprecated vadd_add_vadd_comm (since := "2024-08-29")] vadd_add_vadd
@[to_additive]
lemma mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) :
    (a * b) • (c * d) = (a • c) * (b • d) := smul_smul_smul_comm a b c d
variable [SMul M α]
@[to_additive]
lemma Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)
@[to_additive]
lemma Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b := (h.symm.smul_right r).symm
end
section
variable [Monoid M] [MulAction M α]
@[to_additive]
lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm
variable (M)
@[to_additive (attr := simp)]
lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _
@[to_additive "`VAdd` version of `zero_add_eq_id`"]
lemma one_smul_eq_id : (((1 : M) • ·) : α → α) = id := funext <| one_smul _
@[to_additive "`VAdd` version of `comp_add_left`"]
lemma comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) :=
  funext fun _ ↦ (mul_smul _ _ _).symm
variable {M}
@[to_additive
    "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected abbrev Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]
@[to_additive
    "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected abbrev Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul := by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]
section
variable (M)
@[to_additive
"The regular action of a monoid on itself by left addition.
This is promoted to an `AddTorsor` by `addGroup_is_addTorsor`."]
instance (priority := 910) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
@[to_additive]
instance IsScalarTower.left : IsScalarTower M M α where
  smul_assoc x y z := mul_smul x y z
variable {M}
section Monoid
variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
lemma smul_pow (r : M) (x : N) : ∀ n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul_comm, ← pow_succ', ← pow_succ']
end Monoid
section Group
variable [Group G] [MulAction G α] {g : G} {a b : α}
@[to_additive (attr := simp)]
lemma inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]
@[to_additive (attr := simp)]
lemma smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]
@[to_additive] lemma inv_smul_eq_iff : g⁻¹ • a = b ↔ a = g • b :=
  ⟨fun h ↦ by rw [← h, smul_inv_smul], fun h ↦ by rw [h, inv_smul_smul]⟩
@[to_additive] lemma eq_inv_smul_iff : a = g⁻¹ • b ↔ g • a = b :=
  ⟨fun h ↦ by rw [h, smul_inv_smul], fun h ↦ by rw [← h, inv_smul_smul]⟩
section Mul
variable [Mul H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H] {a b : H}
@[simp] lemma Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b :=
  ⟨fun h ↦ inv_smul_smul g b ▸ h.smul_right g⁻¹, fun h ↦ h.smul_right g⟩
@[simp] lemma Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b := by
  rw [Commute.symm_iff, Commute.smul_right_iff, Commute.symm_iff]
end Mul
variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]
lemma smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ :=
  inv_eq_of_mul_eq_one_right <| by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]
lemma smul_zpow (g : G) (a : H) (n : ℤ) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]
end Group
end
lemma SMulCommClass.of_commMonoid
    (A B G : Type*) [CommMonoid G] [SMul A G] [SMul B G]
    [IsScalarTower A G G] [IsScalarTower B G G] :
    SMulCommClass A B G where
  smul_comm r s x := by
    rw [← one_smul G (s • x), ← smul_assoc, ← one_smul G x, ← smul_assoc s 1 x,
      smul_comm, smul_assoc, one_smul, smul_assoc, one_smul]
namespace MulAction
variable (M α) in
@[to_additive
"Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`."]
def toFun : α ↪ M → α :=
  ⟨fun y x ↦ x • y, fun y₁ y₂ H ↦ one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩
@[to_additive (attr := simp)]
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl
end MulAction
end
section CompatibleScalar
@[to_additive]
lemma smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]
@[to_additive (attr := simp)]
lemma smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]
@[to_additive (attr := simp)]
lemma mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]
@[to_additive]
lemma IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩
@[to_additive]
lemma SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩
end CompatibleScalar