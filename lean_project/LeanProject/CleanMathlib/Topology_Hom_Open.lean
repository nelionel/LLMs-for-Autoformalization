import Mathlib.Topology.ContinuousMap.Basic
open Function
variable {F α β γ δ : Type*}
structure ContinuousOpenMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap toFun
infixr:25 " →CO " => ContinuousOpenMap
section
class ContinuousOpenMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  [TopologicalSpace β] [FunLike F α β] extends ContinuousMapClass F α β : Prop where
  map_open (f : F) : IsOpenMap f
end
export ContinuousOpenMapClass (map_open)
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
    [ContinuousOpenMapClass F α β] :
    CoeTC F (α →CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩
namespace ContinuousOpenMap
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
instance instFunLike : FunLike (α →CO β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
instance : ContinuousOpenMapClass (α →CO β) α β where
  map_continuous f := f.continuous_toFun
  map_open f := f.map_open'
theorem toFun_eq_coe {f : α →CO β} : f.toFun = (f : α → β) :=
  rfl
@[simp] 
theorem coe_toContinuousMap (f : α →CO β) : (f.toContinuousMap : α → β) = f := rfl
@[ext]
theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
  ⟨f.toContinuousMap.copy f' <| h, h.symm.subst f.map_open'⟩
@[simp]
theorem coe_copy (f : α →CO β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : α →CO β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : α →CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩
instance : Inhabited (α →CO α) :=
  ⟨ContinuousOpenMap.id _⟩
@[simp]
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl
def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩
@[simp]
theorem coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : α →CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : α →CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩
@[simp]
theorem cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end ContinuousOpenMap