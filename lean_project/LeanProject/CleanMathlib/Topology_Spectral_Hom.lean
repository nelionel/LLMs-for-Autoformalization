import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.ContinuousMap.Basic
open Function OrderDual
variable {F α β γ δ : Type*}
section Unbundled
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {s : Set β}
@[stacks 005A, stacks 08YG]
structure IsSpectralMap (f : α → β) extends Continuous f : Prop where
  isCompact_preimage_of_isOpen ⦃s : Set β⦄ : IsOpen s → IsCompact s → IsCompact (f ⁻¹' s)
theorem IsCompact.preimage_of_isOpen (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) :
    IsCompact (f ⁻¹' s) :=
  hf.isCompact_preimage_of_isOpen h₁ h₀
theorem IsSpectralMap.continuous {f : α → β} (hf : IsSpectralMap f) : Continuous f :=
  hf.toContinuous
theorem isSpectralMap_id : IsSpectralMap (@id α) :=
  ⟨continuous_id, fun _s _ => id⟩
@[stacks 005B]
theorem IsSpectralMap.comp {f : β → γ} {g : α → β} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (f ∘ g) :=
  ⟨hf.continuous.comp hg.continuous, fun _s hs₀ hs₁ =>
    ((hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg) (hs₀.preimage hf.continuous)⟩
end Unbundled
structure SpectralMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  spectral' : IsSpectralMap toFun
section
class SpectralMapClass (F α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [FunLike F α β] : Prop where
  map_spectral (f : F) : IsSpectralMap f
end
export SpectralMapClass (map_spectral)
attribute [simp] map_spectral
instance (priority := 100) SpectralMapClass.toContinuousMapClass [TopologicalSpace α]
    [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] : ContinuousMapClass F α β :=
  { ‹SpectralMapClass F α β› with map_continuous := fun f => (map_spectral f).continuous }
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] :
    CoeTC F (SpectralMap α β) :=
  ⟨fun f => ⟨_, map_spectral f⟩⟩
namespace SpectralMap
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
def toContinuousMap (f : SpectralMap α β) : ContinuousMap α β :=
  ⟨_, f.spectral'.continuous⟩
instance instFunLike : FunLike (SpectralMap α β) α β where
  coe := SpectralMap.toFun
  coe_injective' f g h := by cases f; cases g; congr
instance : SpectralMapClass (SpectralMap α β) α β where
  map_spectral f := f.spectral'
@[simp]
theorem toFun_eq_coe {f : SpectralMap α β} : f.toFun = (f : α → β) :=
  rfl
@[ext]
theorem ext {f g : SpectralMap α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : SpectralMap α β :=
  ⟨f', h.symm.subst f.spectral'⟩
@[simp]
theorem coe_copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : SpectralMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : SpectralMap α α :=
  ⟨id, isSpectralMap_id⟩
instance : Inhabited (SpectralMap α α) :=
  ⟨SpectralMap.id α⟩
@[simp]
theorem coe_id : ⇑(SpectralMap.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : SpectralMap.id α a = a :=
  rfl
def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩
@[simp]
theorem coe_comp (f : SpectralMap β γ) (g : SpectralMap α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
theorem coe_comp_continuousMap (f : SpectralMap β γ) (g : SpectralMap α β) :
    f ∘ g = (f : ContinuousMap β γ) ∘ (g : ContinuousMap α β) :=
   rfl
@[simp]
theorem coe_comp_continuousMap' (f : SpectralMap β γ) (g : SpectralMap α β) :
    (f.comp g : ContinuousMap α γ) = (f : ContinuousMap β γ).comp g :=
  rfl
@[simp]
theorem comp_assoc (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : SpectralMap α β) : f.comp (SpectralMap.id α) = f :=
  ext fun _a => rfl
@[simp]
theorem id_comp (f : SpectralMap α β) : (SpectralMap.id β).comp f = f :=
  ext fun _a => rfl
@[simp]
theorem cancel_right {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
   fun a => of_eq (congrFun (congrArg comp a) f)⟩
@[simp]
theorem cancel_left {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end SpectralMap