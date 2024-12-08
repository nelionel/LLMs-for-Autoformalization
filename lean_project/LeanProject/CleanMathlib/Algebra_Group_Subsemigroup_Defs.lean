import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.SetLike.Basic
assert_not_exists CompleteLattice
assert_not_exists MonoidWithZero
variable {M : Type*} {N : Type*}
section NonAssoc
variable [Mul M] {s : Set M}
class MulMemClass (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M] : Prop where
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
export MulMemClass (mul_mem)
class AddMemClass (S : Type*) (M : outParam Type*) [Add M] [SetLike S M] : Prop where
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s
export AddMemClass (add_mem)
attribute [to_additive] MulMemClass
attribute [aesop safe apply (rule_sets := [SetLike])] mul_mem add_mem
structure Subsemigroup (M : Type*) [Mul M] where
  carrier : Set M
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
structure AddSubsemigroup (M : Type*) [Add M] where
  carrier : Set M
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
attribute [to_additive AddSubsemigroup] Subsemigroup
namespace Subsemigroup
@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩
@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _
initialize_simps_projections Subsemigroup (carrier → coe)
initialize_simps_projections AddSubsemigroup (carrier → coe)
@[to_additive (attr := simp)]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
@[to_additive (attr := simp)]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl
@[to_additive (attr := simp, norm_cast)]
theorem coe_set_mk (s : Set M) (h_mul) : (mk s h_mul : Set M) = s :=
  rfl
@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl
@[to_additive (attr := ext) "Two `AddSubsemigroup`s are equal if they have the same elements."]
theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to it."]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'
variable {S : Subsemigroup M}
@[to_additive (attr := simp)]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
variable (S)
@[to_additive "An `AddSubsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩
@[to_additive "The trivial `AddSubsemigroup` `∅` of an additive magma `M`."]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := False.elim }⟩
@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩
@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x
@[to_additive (attr := simp)]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x
@[to_additive (attr := simp)]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl
@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl
@[to_additive "The inf of two `AddSubsemigroup`s is their intersection."]
instance : Min (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
@[to_additive (attr := simp)]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) ∩ p' :=
  rfl
@[to_additive (attr := simp)]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
@[to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot
@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩
end Subsemigroup
namespace MulHom
variable [Mul N]
open Subsemigroup
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eqLocus (f g : M →ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]
@[to_additive]
theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun _ => h trivial
end MulHom
end NonAssoc
namespace MulMemClass
variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩
@[to_additive (attr := simp low, norm_cast)]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl
@[to_additive (attr := simp low)]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl
@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl
@[to_additive "An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure."]
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S :=
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl
@[to_additive "An `AddSubsemigroup` of an `AddCommSemigroup` is an `AddCommSemigroup`."]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S :=
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl
@[to_additive "The natural semigroup hom from an `AddSubsemigroup` of
`AddSubsemigroup` `M` to `M`."]
def subtype : S' →ₙ* M where
  toFun := Subtype.val; map_mul' := fun _ _ => rfl
@[to_additive (attr := simp)]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl
end MulMemClass