import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Defs
open Function
variable {F α β γ δ : Type*}
structure ContinuousOrderHom (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous toFun
infixr:25 " →Co " => ContinuousOrderHom
section
class ContinuousOrderHomClass (F : Type*) (α β : outParam Type*) [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] extends
    ContinuousMapClass F α β : Prop where
  map_monotone (f : F) : Monotone f
namespace ContinuousOrderHomClass
variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [FunLike F α β] [ContinuousOrderHomClass F α β]
instance (priority := 100) toOrderHomClass  :
    OrderHomClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }
@[coe]
def toContinuousOrderHom (f : F) : α →Co β :=
    { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }
instance : CoeTC F (α →Co β) :=
  ⟨toContinuousOrderHom⟩
end ContinuousOrderHomClass
namespace ContinuousOrderHom
variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
section Preorder
variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]
def toContinuousMap (f : α →Co β) : C(α, β) :=
  { f with }
instance instFunLike : FunLike (α →Co β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
instance : ContinuousOrderHomClass (α →Co β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun
@[simp] theorem coe_toOrderHom (f : α →Co β) : ⇑f.toOrderHom = f := rfl
theorem toFun_eq_coe {f : α →Co β} : f.toFun = (f : α → β) := rfl
@[ext]
theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
  ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩
@[simp]
theorem coe_copy (f : α →Co β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : α →Co β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : α →Co α :=
  ⟨OrderHom.id, continuous_id⟩
instance : Inhabited (α →Co α) :=
  ⟨ContinuousOrderHom.id _⟩
@[simp]
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl
def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩
@[simp]
theorem coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : α →Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : α →Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
@[simp]
theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
instance : Preorder (α →Co β) :=
  Preorder.lift ((↑) : (α →Co β) → α → β)
end Preorder
instance [PartialOrder β] : PartialOrder (α →Co β) :=
  PartialOrder.lift ((↑) : (α →Co β) → α → β) DFunLike.coe_injective
end ContinuousOrderHom
end