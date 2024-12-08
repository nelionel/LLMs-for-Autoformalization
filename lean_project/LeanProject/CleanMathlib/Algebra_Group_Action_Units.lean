import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Defs
assert_not_exists MonoidWithZero
variable {G H M N α : Type*}
namespace Units
@[to_additive] instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a
@[to_additive] lemma smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a := rfl
@[to_additive, simp]
lemma smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α) :
    (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a := rfl
@[simp]
lemma smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.unit • a = m • a := rfl
@[to_additive]
lemma _root_.IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.unit⁻¹ • a = 1 := h.val_inv_mul
@[to_additive]
instance [Monoid M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α where
  eq_of_smul_eq_smul h := Units.ext <| eq_of_smul_eq_smul h
@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction Mˣ α where
  one_smul := (one_smul M : _)
  mul_smul m n := mul_smul (m : M) n
@[to_additive]
instance smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mˣ N α where smul_comm m n := (smul_comm (m : M) n : _)
@[to_additive]
instance smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nˣ α where smul_comm m n := (smul_comm m (n : N) : _)
@[to_additive]
instance [Monoid M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mˣ N α where smul_assoc m n := (smul_assoc (m : M) n : _)
@[to_additive]
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulAction G Mˣ where
  smul g m :=
    ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel, one_smul],
      by rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel, one_smul]⟩
  one_smul _ := Units.ext <| one_smul _ _
  mul_smul _ _ _ := Units.ext <| mul_smul _ _ _
@[to_additive (attr := simp)]
lemma val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) := rfl
@[to_additive (attr := simp)]
lemma smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ := ext rfl
@[to_additive "Transfer `VAddCommClass G H M` to `VAddCommClass G H (AddUnits M)`."]
instance smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SMulCommClass G H M] :
    SMulCommClass G H Mˣ where smul_comm g h m := Units.ext <| smul_comm g h (m : M)
@[to_additive "Transfer `VAddAssocClass G H M` to `VAddAssocClass G H (AddUnits M)`."]
instance isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] :
    IsScalarTower G H Mˣ where smul_assoc g h m := Units.ext <| smul_assoc g h (m : M)
@[to_additive "Transfer `VAddAssocClass G M α` to `VAddAssocClass G (AddUnits M) α`."]
instance isScalarTower'_left [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
    [SMulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] :
    IsScalarTower G Mˣ α where smul_assoc g m := (smul_assoc g (m : M) : _)
example [Monoid M] [Monoid N] [MulAction M N] [SMulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ := Units.mulAction'
end Units
@[to_additive]
lemma IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩