import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Data.Set.Basic
protected def copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) : MySubobject X :=
  { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }
@[simp] lemma coe_copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) :
  (p.copy s hs : Set X) = s := rfl
lemma copy_eq (p : MySubobject X) (s : Set X) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs
end MySubobject
```
An alternative to `SetLike` could have been an extensional `Membership` typeclass:
```
class ExtMembership (α : out_param <| Type u) (β : Type v) extends Membership α β where
  (ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `SetLike` conveniently uses a carrier set projection directly.
## Tags
subobjects
-/
@[notation_class * carrier Simps.findCoercionArgs]
class SetLike (A : Type*) (B : outParam Type*) where
  protected coe : A → Set B
  protected coe_injective' : Function.Injective coe
attribute [coe] SetLike.coe
namespace SetLike
variable {A : Type*} {B : Type*} [i : SetLike A B]
instance : CoeTC A (Set B) where coe := SetLike.coe
instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩
instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩
section Delab
open Lean PrettyPrinter.Delaborator SubExpr
@[delab app.Subtype]
def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, _, .bvar 0] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``instMembership 3
  let S ← withAppArg <| withBindingBody n <| withNaryArg 3 delab
  `(↥$S)
end Delab
variable (p q : A)
@[simp, norm_cast]
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl
variable {p q}
protected theorem «exists» {q : p → Prop} : (∃ x, q x) ↔ ∃ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.exists
protected theorem «forall» {q : p → Prop} : (∀ x, q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.forall
theorem coe_injective : Function.Injective (SetLike.coe : A → Set B) := fun _ _ h =>
  SetLike.coe_injective' h
@[simp, norm_cast]
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff
@[norm_cast] lemma coe_ne_coe : (p : Set B) ≠ q ↔ p ≠ q := coe_injective.ne_iff
theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h
theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h
theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff
@[simp]
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff_val.symm
@[simp]
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2
@[aesop 5% apply (rule_sets := [SetLike])]
lemma mem_of_subset {s : Set B} (hp : s ⊆ p) {x : B} (hx : x ∈ s) : x ∈ p := hp hx
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := rfl
@[simp] lemma setOf_mem_eq (a : A) : {b | b ∈ a} = a := rfl
instance (priority := 100) instPartialOrder : PartialOrder A :=
  { PartialOrder.lift (SetLike.coe : A → Set B) coe_injective with
    le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }
theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T :=
  Iff.rfl
@[simp, norm_cast] lemma coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T := .rfl
@[simp, norm_cast] lemma coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T := .rfl
@[gcongr] protected alias ⟨_, GCongr.coe_subset_coe⟩ := coe_subset_coe
@[gcongr] protected alias ⟨_, GCongr.coe_ssubset_coe⟩ := coe_ssubset_coe
@[mono]
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr
@[mono]
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr
theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q :=
  Set.not_subset
theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p :=
  Set.exists_of_ssubset
theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_le, not_le_iff_exists]
end SetLike