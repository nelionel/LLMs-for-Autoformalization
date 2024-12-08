import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Units
import Mathlib.Order.Hom.Basic
open Function
variable {F α β γ δ : Type*}
section AddMonoid
structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α →+ β where
  monotone' : Monotone toFun
infixr:25 " →+o " => OrderAddMonoidHom
structure OrderAddMonoidIso (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α ≃+ β where
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b
infixr:25 " ≃+o " => OrderAddMonoidIso
end AddMonoid
section Monoid
@[to_additive]
structure OrderMonoidHom (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α →* β where
  monotone' : Monotone toFun
infixr:25 " →*o " => OrderMonoidHom
variable [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β] [FunLike F α β]
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `OrderHomClass F α β` and `AddMonoidHomClass F α β`
  into an actual `OrderAddMonoidHom`.
  This is declared as the default coercion from `F` to `α →+o β`."]
def OrderMonoidHomClass.toOrderMonoidHom [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) :
    α →*o β :=
  { (f : α →* β) with monotone' := OrderHomClass.monotone f }
@[to_additive "Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom` via
  `OrderAddMonoidHomClass.toOrderAddMonoidHom`"]
instance [OrderHomClass F α β] [MonoidHomClass F α β] : CoeTC F (α →*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩
@[to_additive]
structure OrderMonoidIso (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α ≃* β where
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b
infixr:25 " ≃*o " => OrderMonoidIso
variable [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β] [FunLike F α β]
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `AddEquivClass F α β`
  into an actual `OrderAddMonoidIso`.
  This is declared as the default coercion from `F` to `α ≃+o β`."]
def OrderMonoidIsoClass.toOrderMonoidIso [EquivLike F α β] [OrderIsoClass F α β]
    [MulEquivClass F α β] (f : F) :
    α ≃*o β :=
  { (f : α ≃* β) with map_le_map_iff' := OrderIsoClass.map_le_map_iff f }
@[to_additive "Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom` via
  `OrderAddMonoidHomClass.toOrderAddMonoidHom`"]
instance [OrderHomClass F α β] [MonoidHomClass F α β] : CoeTC F (α →*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩
@[to_additive "Any type satisfying `OrderAddMonoidIsoClass` can be cast into `OrderAddMonoidIso` via
  `OrderAddMonoidIsoClass.toOrderAddMonoidIso`"]
instance [EquivLike F α β] [OrderIsoClass F α β] [MulEquivClass F α β] : CoeTC F (α ≃*o β) :=
  ⟨OrderMonoidIsoClass.toOrderMonoidIso⟩
end Monoid
section MonoidWithZero
variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]
structure OrderMonoidWithZeroHom (α β : Type*) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  monotone' : Monotone toFun
infixr:25 " →*₀o " => OrderMonoidWithZeroHom
section
variable [FunLike F α β]
@[coe]
def OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom [OrderHomClass F α β]
    [MonoidWithZeroHomClass F α β] (f : F) : α →*₀o β :=
{ (f : α →*₀ β) with monotone' := OrderHomClass.monotone f }
end
variable [FunLike F α β]
instance [OrderHomClass F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀o β) :=
  ⟨OrderMonoidWithZeroHomClass.toOrderMonoidWithZeroHom⟩
end MonoidWithZero
section OrderedZero
variable [FunLike F α β]
variable [Preorder α] [Zero α] [Preorder β] [Zero β] [OrderHomClass F α β]
  [ZeroHomClass F α β] (f : F) {a : α}
theorem map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha
theorem map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha
end OrderedZero
section OrderedAddCommGroup
variable [OrderedAddCommGroup α] [OrderedAddCommMonoid β] [i : FunLike F α β]
variable (f : F)
theorem monotone_iff_map_nonneg [iamhc : AddMonoidHomClass F α β] :
    Monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a, map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩
variable [iamhc : AddMonoidHomClass F α β]
theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
  monotone_toDual_comp_iff.symm.trans <| monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _
theorem monotone_iff_map_nonpos : Monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 :=
  antitone_comp_ofDual_iff.symm.trans <| antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _
theorem antitone_iff_map_nonneg : Antitone (f : α → β) ↔ ∀ a ≤ 0, 0 ≤ f a :=
  monotone_comp_ofDual_iff.symm.trans <| monotone_iff_map_nonneg (α := αᵒᵈ) (iamhc := iamhc) _
variable [AddLeftStrictMono β]
theorem strictMono_iff_map_pos :
    StrictMono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a := by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)
theorem strictAnti_iff_map_neg : StrictAnti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 :=
  strictMono_toDual_comp_iff.symm.trans <| strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _
theorem strictMono_iff_map_neg : StrictMono (f : α → β) ↔ ∀ a < 0, f a < 0 :=
  strictAnti_comp_ofDual_iff.symm.trans <| strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _
theorem strictAnti_iff_map_pos : StrictAnti (f : α → β) ↔ ∀ a < 0, 0 < f a :=
  strictMono_comp_ofDual_iff.symm.trans <| strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _
end OrderedAddCommGroup
namespace OrderMonoidHom
section Preorder
variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}
@[to_additive]
instance : FunLike (α →*o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr
@[to_additive]
instance : OrderHomClass (α →*o β) α β where
  map_rel f _ _ h := f.monotone' h
@[to_additive]
instance : MonoidHomClass (α →*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
@[to_additive]
theorem toFun_eq_coe (f : α →*o β) : f.toFun = (f : α → β) :=
  rfl
@[to_additive (attr := simp)]
theorem coe_mk (f : α →* β) (h) : (OrderMonoidHom.mk f h : α → β) = f :=
  rfl
@[to_additive (attr := simp)]
theorem mk_coe (f : α →*o β) (h) : OrderMonoidHom.mk (f : α →* β) h = f := by
  ext
  rfl
@[to_additive "Reinterpret an ordered additive monoid homomorphism as an order homomorphism."]
def toOrderHom (f : α →*o β) : α →o β :=
  { f with }
@[to_additive (attr := simp)]
theorem coe_monoidHom (f : α →*o β) : ((f : α →* β) : α → β) = f :=
  rfl
@[to_additive (attr := simp)]
theorem coe_orderHom (f : α →*o β) : ((f : α →o β) : α → β) = f :=
  rfl
@[to_additive]
theorem toMonoidHom_injective : Injective (toMonoidHom : _ → α →* β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0
@[to_additive]
theorem toOrderHom_injective : Injective (toOrderHom : _ → α →o β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0
@[to_additive "Copy of an `OrderAddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities."]
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }
@[to_additive (attr := simp)]
theorem coe_copy (f : α →*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
@[to_additive]
theorem copy_eq (f : α →*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
@[to_additive "The identity map as an ordered additive monoid homomorphism."]
protected def id : α →*o α :=
  { MonoidHom.id α, OrderHom.id with }
@[to_additive (attr := simp)]
theorem coe_id : ⇑(OrderMonoidHom.id α) = id :=
  rfl
@[to_additive]
instance : Inhabited (α →*o α) :=
  ⟨OrderMonoidHom.id α⟩
variable {α}
@[to_additive "Composition of `OrderAddMonoidHom`s as an `OrderAddMonoidHom`"]
def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
  { f.toMonoidHom.comp (g : α →* β), f.toOrderHom.comp (g : α →o β) with }
@[to_additive (attr := simp)]
theorem coe_comp (f : β →*o γ) (g : α →*o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
@[to_additive (attr := simp)]
theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[to_additive]
theorem coe_comp_monoidHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →* γ) = (f : β →* γ).comp g :=
  rfl
@[to_additive]
theorem coe_comp_orderHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →o γ) = (f : β →o γ).comp g :=
  rfl
@[to_additive (attr := simp)]
theorem comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[to_additive (attr := simp)]
theorem comp_id (f : α →*o β) : f.comp (OrderMonoidHom.id α) = f :=
  rfl
@[to_additive (attr := simp)]
theorem id_comp (f : α →*o β) : (OrderMonoidHom.id β).comp f = f :=
  rfl
@[to_additive (attr := simp)]
theorem cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩
@[to_additive (attr := simp)]
theorem cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
@[to_additive "`0` is the homomorphism sending all elements to `0`."]
instance : One (α →*o β) :=
  ⟨{ (1 : α →* β) with monotone' := monotone_const }⟩
@[to_additive (attr := simp)]
theorem coe_one : ⇑(1 : α →*o β) = 1 :=
  rfl
@[to_additive (attr := simp)]
theorem one_apply (a : α) : (1 : α →*o β) a = 1 :=
  rfl
@[to_additive (attr := simp)]
theorem one_comp (f : α →*o β) : (1 : β →*o γ).comp f = 1 :=
  rfl
@[to_additive (attr := simp)]
theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 :=
  ext fun _ => map_one f
end Preorder
section Mul
variable [OrderedCommMonoid α] [OrderedCommMonoid β] [OrderedCommMonoid γ]
@[to_additive "For two ordered additive monoid morphisms `f` and `g`, their product is the ordered
additive monoid morphism sending `a` to `f a + g a`."]
instance : Mul (α →*o β) :=
  ⟨fun f g => { (f * g : α →* β) with monotone' := f.monotone'.mul' g.monotone' }⟩
@[to_additive (attr := simp)]
theorem coe_mul (f g : α →*o β) : ⇑(f * g) = f * g :=
  rfl
@[to_additive (attr := simp)]
theorem mul_apply (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
  rfl
@[to_additive]
theorem mul_comp (g₁ g₂ : β →*o γ) (f : α →*o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
@[to_additive]
theorem comp_mul (g : β →*o γ) (f₁ f₂ : α →*o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _
end Mul
section OrderedCommMonoid
variable {hα : OrderedCommMonoid α} {hβ : OrderedCommMonoid β}
@[to_additive (attr := simp)]
theorem toMonoidHom_eq_coe (f : α →*o β) : f.toMonoidHom = f :=
  rfl
@[to_additive (attr := simp)]
theorem toOrderHom_eq_coe (f : α →*o β) : f.toOrderHom = f :=
  rfl
end OrderedCommMonoid
section OrderedCommGroup
variable {hα : OrderedCommGroup α} {hβ : OrderedCommGroup β}
@[to_additive
      "Makes an ordered additive group homomorphism from a proof that the map preserves
      addition."]
def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }
end OrderedCommGroup
end OrderMonoidHom
namespace OrderMonoidIso
section Preorder
variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α ≃*o β}
@[to_additive]
instance : EquivLike (α ≃*o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr
@[to_additive]
instance : OrderIsoClass (α ≃*o β) α β where
  map_le_map_iff f := f.map_le_map_iff'
@[to_additive]
instance : MulEquivClass (α ≃*o β) α β where
  map_mul f := map_mul f.toMulEquiv
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
@[to_additive]
theorem toFun_eq_coe (f : α ≃*o β) : f.toFun = (f : α → β) :=
  rfl
@[to_additive (attr := simp)]
theorem coe_mk (f : α ≃* β) (h) : (OrderMonoidIso.mk f h : α → β) = f :=
  rfl
@[to_additive (attr := simp)]
theorem mk_coe (f : α ≃*o β) (h) : OrderMonoidIso.mk (f : α ≃* β) h = f := rfl
@[to_additive "Reinterpret an ordered additive monoid isomomorphism as an order isomomorphism."]
def toOrderIso (f : α ≃*o β) : α ≃o β :=
  { f with
    map_rel_iff' := map_le_map_iff f }
@[to_additive (attr := simp)]
theorem coe_mulEquiv (f : α ≃*o β) : ((f : α ≃* β) : α → β) = f :=
  rfl
@[to_additive (attr := simp)]
theorem coe_orderIso (f : α ≃*o β) : ((f : α →o β) : α → β) = f :=
  rfl
@[to_additive]
theorem toMulEquiv_injective : Injective (toMulEquiv : _ → α ≃* β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0
@[to_additive]
theorem toOrderIso_injective : Injective (toOrderIso : _ → α ≃o β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0
variable (α)
@[to_additive "The identity map as an ordered additive monoid isomorphism."]
protected def refl : α ≃*o α :=
  { MulEquiv.refl α with map_le_map_iff' := by simp }
@[to_additive (attr := simp)]
theorem coe_refl : ⇑(OrderMonoidIso.refl α) = id :=
  rfl
@[to_additive]
instance : Inhabited (α ≃*o α) :=
  ⟨OrderMonoidIso.refl α⟩
variable {α}
@[to_additive (attr := trans) "Transitivity of addition-preserving order isomorphisms"]
def trans (f : α ≃*o β) (g : β ≃*o γ) : α ≃*o γ :=
  { (f : α ≃* β).trans g with map_le_map_iff' := by simp }
@[to_additive (attr := simp)]
theorem coe_trans (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α → γ) = g ∘ f :=
  rfl
@[to_additive (attr := simp)]
theorem trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl
@[to_additive]
theorem coe_trans_mulEquiv (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃* γ) = (f : α ≃* β).trans g :=
  rfl
@[to_additive]
theorem coe_trans_orderIso (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃o γ) = (f : α ≃o β).trans g :=
  rfl
@[to_additive (attr := simp)]
theorem trans_assoc (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl
@[to_additive (attr := simp)]
theorem trans_refl (f : α ≃*o β) : f.trans (OrderMonoidIso.refl β) = f :=
  rfl
@[to_additive (attr := simp)]
theorem refl_trans (f : α ≃*o β) : (OrderMonoidIso.refl α).trans f = f :=
  rfl
@[to_additive (attr := simp)]
theorem cancel_right {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f) :
    g₁.trans f = g₂.trans f ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← trans_apply, h, trans_apply], by rintro rfl; rfl⟩
@[to_additive (attr := simp)]
theorem cancel_left {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g) :
    g.trans f₁ = g.trans f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩
@[to_additive (attr := simp)]
theorem toMulEquiv_eq_coe (f : α ≃*o β) : f.toMulEquiv = f :=
  rfl
@[to_additive (attr := simp)]
theorem toOrderIso_eq_coe (f : α ≃*o β) : f.toOrderIso = f :=
  rfl
variable (f)
@[to_additive]
protected lemma strictMono : StrictMono f :=
  strictMono_of_le_iff_le fun _ _ ↦ (map_le_map_iff _).symm
@[to_additive]
protected lemma strictMono_symm : StrictMono f.symm :=
  strictMono_of_le_iff_le <| fun a b ↦ by
    rw [← map_le_map_iff f]
    convert Iff.rfl <;>
    exact f.toEquiv.apply_symm_apply _
end Preorder
section OrderedCommGroup
variable {hα : OrderedCommGroup α} {hβ : OrderedCommGroup β}
@[to_additive
      "Makes an ordered additive group isomorphism from a proof that the map preserves
      addition."]
def mk' (f : α ≃ β) (hf : ∀ {a b}, f a ≤ f b ↔ a ≤ b) (map_mul : ∀ a b : α, f (a * b) = f a * f b) :
    α ≃*o β :=
  { MulEquiv.mk' f map_mul with map_le_map_iff' := hf }
end OrderedCommGroup
end OrderMonoidIso
namespace OrderMonoidWithZeroHom
section Preorder
variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}
instance : FunLike (α →*₀o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr
instance : MonoidWithZeroHomClass (α →*₀o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
instance : OrderHomClass (α →*₀o β) α β where
  map_rel f _ _ h := f.monotone' h
@[ext]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
theorem toFun_eq_coe (f : α →*₀o β) : f.toFun = (f : α → β) :=
  rfl
@[simp]
theorem coe_mk (f : α →*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α → β) = f :=
  rfl
@[simp]
theorem mk_coe (f : α →*₀o β) (h) : OrderMonoidWithZeroHom.mk (f : α →*₀ β) h = f := rfl
def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }
@[simp]
theorem coe_monoidWithZeroHom (f : α →*₀o β) : ⇑(f : α →*₀ β) = f :=
  rfl
@[simp]
theorem coe_orderMonoidHom (f : α →*₀o β) : ⇑(f : α →*o β) = f :=
  rfl
theorem toOrderMonoidHom_injective : Injective (toOrderMonoidHom : _ → α →*o β) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h using 0
theorem toMonoidWithZeroHom_injective : Injective (toMonoidWithZeroHom : _ → α →*₀ β) :=
  fun f g h => ext <| by convert DFunLike.ext_iff.1 h using 0
protected def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toOrderMonoidHom.copy f' h, f.toMonoidWithZeroHom.copy f' h with toFun := f' }
@[simp]
theorem coe_copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }
@[simp]
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl
instance : Inhabited (α →*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩
variable {α}
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { f.toMonoidWithZeroHom.comp (g : α →*₀ β), f.toOrderMonoidHom.comp (g : α →*o β) with }
@[simp]
theorem coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
theorem coe_comp_monoidWithZeroHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g :=
  rfl
theorem coe_comp_orderMonoidHom (f : β →*₀o γ) (g : α →*₀o β) :
    (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl
@[simp]
theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : α →*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f := rfl
@[simp]
theorem id_comp (f : α →*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f := rfl
@[simp]
theorem cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩
@[simp]
theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end Preorder
section Mul
variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]
instance : Mul (α →*₀o β) :=
  ⟨fun f g => { (f * g : α →*₀ β) with monotone' := f.monotone'.mul' g.monotone' }⟩
@[simp]
theorem coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g :=
  rfl
@[simp]
theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl
theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _
end Mul
section LinearOrderedCommMonoidWithZero
variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}
@[simp]
theorem toMonoidWithZeroHom_eq_coe (f : α →*₀o β) : f.toMonoidWithZeroHom = f := by
  rfl
@[simp]
theorem toOrderMonoidHom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f :=
  rfl
end LinearOrderedCommMonoidWithZero
end OrderMonoidWithZeroHom
@[simps! toFun]
def OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZero α)ˣ ≃*o α where
  toMulEquiv := WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]