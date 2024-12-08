import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Hom
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
variable {F α M N G : Type*}
@[to_additive (attr := simps apply_val symm_apply)
"An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
@[to_additive (attr := simp)]
lemma toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_apply]
namespace Units
variable [Monoid M] [Monoid N]
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }
@[simp]
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl
@[simp]
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl
@[to_additive (attr := simps (config := .asFn) apply)
  "Left addition of an additive unit is a permutation of the underlying type."]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left
@[to_additive (attr := simp)]
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun _ => rfl
@[to_additive]
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M → M) :=
  (mulLeft a).bijective
@[to_additive (attr := simps (config := .asFn) apply)
"Right addition of an additive unit is a permutation of the underlying type."]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u
@[to_additive (attr := simp)]
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun _ => rfl
@[to_additive]
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).bijective
end Units
namespace Equiv
section Group
variable [Group G]
@[to_additive "Left addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft
@[to_additive (attr := simp)]
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) :=
  rfl
@[to_additive (attr := simp) "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) :=
  rfl
@[to_additive (attr := simp)]
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun _ => rfl
@[to_additive]
theorem _root_.Group.mulLeft_bijective (a : G) : Function.Bijective (a * ·) :=
  (Equiv.mulLeft a).bijective
@[to_additive "Right addition in an `AddGroup` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight
@[to_additive (attr := simp)]
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl
@[to_additive (attr := simp)]
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun _ => rfl
@[to_additive (attr := simp) "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl
@[to_additive]
theorem _root_.Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).bijective
@[to_additive (attr := simps) " A version of `Equiv.addLeft a (-b)` that is defeq to `a - b`. "]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
@[to_additive]
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _
@[to_additive (attr := simps) " A version of `Equiv.addRight (-a) b` that is defeq to `b - a`. "]
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
@[to_additive]
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _
end Group
end Equiv
variable (α) in
@[simps]
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext <| Prod.ext rfl rfl
@[to_additive (attr := simps apply)
  "When the `AddGroup` is commutative, `Equiv.neg` is an `AddEquiv`."]
def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }
@[to_additive (attr := simp)]
theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl
@[instance]
theorem isLocalHom_equiv [Monoid M] [Monoid N] [EquivLike F M N]
    [MulEquivClass F M N] (f : F) : IsLocalHom f where
  map_nonunit a ha := by
    convert ha.map (f : M ≃* N).symm
    rw [MulEquiv.eq_symm_apply]
    rfl 
@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_equiv := isLocalHom_equiv