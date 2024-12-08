import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Lattice
open Function OrderDual Set
variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}
structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  toFun : α → β
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  toFun : α → β
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)
structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β where
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)
section
class sSupHomClass (F α β : Type*) [SupSet α] [SupSet β] [FunLike F α β] : Prop where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
class sInfHomClass (F α β : Type*) [InfSet α] [InfSet β] [FunLike F α β] : Prop where
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)
class FrameHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  extends InfTopHomClass F α β : Prop where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
class CompleteLatticeHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β]
  [FunLike F α β] extends sInfHomClass F α β : Prop where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
end
export sSupHomClass (map_sSup)
export sInfHomClass (map_sInf)
attribute [simp] map_sSup map_sInf
section Hom
variable [FunLike F α β]
@[simp] theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [iSup, ← Set.range_comp, Function.comp_def]
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]
@[simp] theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by simp [iInf, ← Set.range_comp, Function.comp_def]
theorem map_iInf₂ [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_iInf]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [sSupHomClass F α β] : SupBotHomClass F α β :=
  {  ‹sSupHomClass F α β› with
    map_sup := fun f a b => by
      rw [← sSup_pair, map_sSup]
      simp only [Set.image_pair, sSup_insert, sSup_singleton]
    map_bot := fun f => by
      rw [← sSup_empty, map_sSup, Set.image_empty, sSup_empty] }
instance (priority := 100) sInfHomClass.toInfTopHomClass [CompleteLattice α]
    [CompleteLattice β] [sInfHomClass F α β] : InfTopHomClass F α β :=
  { ‹sInfHomClass F α β› with
    map_inf := fun f a b => by
      rw [← sInf_pair, map_sInf, Set.image_pair]
      simp only [Set.image_pair, sInf_insert, sInf_singleton]
    map_top := fun f => by
      rw [← sInf_empty, map_sInf, Set.image_empty, sInf_empty] }
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }
end Hom
section Equiv
variable [EquivLike F α β]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sSupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sSup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sSup_le_iff, Set.forall_mem_image] }
instance (priority := 100) OrderIsoClass.tosInfHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sInfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sInf := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_sInf_iff, Set.forall_mem_image] }
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.tosInfHomClass with }
end Equiv
variable [FunLike F α β]
@[simps] def OrderIso.toCompleteLatticeHom [CompleteLattice α] [CompleteLattice β]
    (f : OrderIso α β) : CompleteLatticeHom α β where
  toFun := f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f
instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩
instance [InfSet α] [InfSet β] [sInfHomClass F α β] : CoeTC F (sInfHom α β) :=
  ⟨fun f => ⟨f, map_sInf f⟩⟩
instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩
instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩
namespace sSupHom
variable [SupSet α]
section SupSet
variable [SupSet β] [SupSet γ] [SupSet δ]
instance : FunLike (sSupHom α β) α β where
  coe := sSupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
instance : sSupHomClass (sSupHom α β) α β where
  map_sSup := sSupHom.map_sSup'
@[simp] lemma toFun_eq_coe (f : sSupHom α β) : f.toFun = f := rfl
@[simp, norm_cast] lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl
@[ext]
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'
@[simp]
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩
@[simp]
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]
@[simp]
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end SupSet
variable {_ : CompleteLattice β}
instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩
instance : OrderBot (sSupHom α β) where
  bot := ⊥
  bot_le := fun _ _ ↦ CompleteLattice.bot_le _
@[simp]
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl
@[simp]
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl
end sSupHom
namespace sInfHom
variable [InfSet α]
section InfSet
variable [InfSet β] [InfSet γ] [InfSet δ]
instance : FunLike (sInfHom α β) α β where
  coe := sInfHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
instance : sInfHomClass (sInfHom α β) α β where
  map_sInf := sInfHom.map_sInf'
@[simp] lemma toFun_eq_coe (f : sInfHom α β) : f.toFun = f := rfl
@[simp] lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl
@[ext]
theorem ext {f g : sInfHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : sInfHom α β where
  toFun := f'
  map_sInf' := h.symm ▸ f.map_sInf'
@[simp]
theorem coe_copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : sInfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : sInfHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
instance : Inhabited (sInfHom α α) :=
  ⟨sInfHom.id α⟩
@[simp]
theorem coe_id : ⇑(sInfHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : sInfHom.id α a = a :=
  rfl
def comp (f : sInfHom β γ) (g : sInfHom α β) : sInfHom α γ where
  toFun := f ∘ g
  map_sInf' s := by rw [comp_apply, map_sInf, map_sInf, Set.image_image]; simp only [Function.comp]
@[simp]
theorem coe_comp (f : sInfHom β γ) (g : sInfHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : sInfHom β γ) (g : sInfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : sInfHom γ δ) (g : sInfHom β γ) (h : sInfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : sInfHom α β) : f.comp (sInfHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : sInfHom α β) : (sInfHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : sInfHom β γ} {f : sInfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left {g : sInfHom β γ} {f₁ f₂ : sInfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end InfSet
variable [CompleteLattice β]
instance : PartialOrder (sInfHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
instance : Top (sInfHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sInf_empty]
      · rw [hs.image_const, sInf_singleton]⟩⟩
instance : OrderTop (sInfHom α β) where
  top := ⊤
  le_top := fun _ _ => CompleteLattice.le_top _
@[simp]
theorem coe_top : ⇑(⊤ : sInfHom α β) = ⊤ :=
  rfl
@[simp]
theorem top_apply (a : α) : (⊤ : sInfHom α β) a = ⊤ :=
  rfl
end sInfHom
namespace FrameHom
variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]
instance : FunLike (FrameHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
instance : FrameHomClass (FrameHom α β) α β where
  map_sSup f := f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
lemma toFun_eq_coe (f : FrameHom α β) : f.toFun = f := rfl
@[simp] lemma coe_toInfTopHom (f : FrameHom α β) : ⇑f.toInfTopHom = f := rfl
@[simp] lemma coe_toLatticeHom (f : FrameHom α β) : ⇑f.toLatticeHom = f := rfl
@[simp] lemma coe_mk (f : InfTopHom α β) (hf) : ⇑(mk f hf) = f := rfl
@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩
@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
end FrameHom
namespace CompleteLatticeHom
variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]
instance : FunLike (CompleteLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  map_sSup f := f.map_sSup'
  map_sInf f := f.map_sInf'
def tosSupHom (f : CompleteLatticeHom α β) : sSupHom α β :=
  f
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
lemma toFun_eq_coe (f : CompleteLatticeHom α β) : f.toFun = f := rfl
@[simp] lemma coe_tosInfHom (f : CompleteLatticeHom α β) : ⇑f.tosInfHom = f := rfl
@[simp] lemma coe_tosSupHom (f : CompleteLatticeHom α β) : ⇑f.tosSupHom = f := rfl
@[simp] lemma coe_toBoundedLatticeHom (f : CompleteLatticeHom α β) : ⇑f.toBoundedLatticeHom = f :=
rfl
@[simp] lemma coe_mk (f : sInfHom α β) (hf) : ⇑(mk f hf) = f := rfl
@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }
@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }
instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩
@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }
@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end CompleteLatticeHom
namespace sSupHom
variable [SupSet α] [SupSet β] [SupSet γ]
@[simps]
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩
  left_inv _ := sSupHom.ext fun _ => rfl
  right_inv _ := sInfHom.ext fun _ => rfl
@[simp]
theorem dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _ :=
  rfl
@[simp]
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) :
    sSupHom.dual (g.comp f) = (sSupHom.dual g).comp (sSupHom.dual f) :=
  rfl
@[simp]
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl
@[simp]
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl
end sSupHom
namespace sInfHom
variable [InfSet α] [InfSet β] [InfSet γ]
@[simps]
protected def dual : sInfHom α β ≃ sSupHom αᵒᵈ βᵒᵈ where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_sSup' := fun _ => congr_arg toDual (map_sInf f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_sInf' := fun _ => congr_arg ofDual (map_sSup f _) }
  left_inv _ := sInfHom.ext fun _ => rfl
  right_inv _ := sSupHom.ext fun _ => rfl
@[simp]
theorem dual_id : sInfHom.dual (sInfHom.id α) = sSupHom.id _ :=
  rfl
@[simp]
theorem dual_comp (g : sInfHom β γ) (f : sInfHom α β) :
    sInfHom.dual (g.comp f) = (sInfHom.dual g).comp (sInfHom.dual f) :=
  rfl
@[simp]
theorem symm_dual_id : sInfHom.dual.symm (sSupHom.id _) = sInfHom.id α :=
  rfl
@[simp]
theorem symm_dual_comp (g : sSupHom βᵒᵈ γᵒᵈ) (f : sSupHom αᵒᵈ βᵒᵈ) :
    sInfHom.dual.symm (g.comp f) = (sInfHom.dual.symm g).comp (sInfHom.dual.symm f) :=
  rfl
end sInfHom
namespace CompleteLatticeHom
variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]
@[simps!]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := ext fun _ => rfl
@[simp]
theorem dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _ :=
  rfl
@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    CompleteLatticeHom.dual (g.comp f) =
      (CompleteLatticeHom.dual g).comp (CompleteLatticeHom.dual f) :=
  rfl
@[simp]
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl
@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl
end CompleteLatticeHom
namespace CompleteLatticeHom
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := preimage f
  map_sSup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_sInf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]
@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.preimage f :=
  rfl
@[simp]
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl
end CompleteLatticeHom
theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  Set.image_sUnion
@[simps]
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β) where
  toFun := image f
  map_sSup' := Set.image_sSup
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
variable [CompleteLattice α] (x : α × α)
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]
@[simp, norm_cast]
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl
@[simp, norm_cast]
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl