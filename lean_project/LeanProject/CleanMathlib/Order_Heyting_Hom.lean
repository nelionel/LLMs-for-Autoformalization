import Mathlib.Order.Hom.Lattice
open Function
variable {F α β γ δ : Type*}
structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHom α β where
  protected map_bot' : toFun ⊥ = ⊥
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
structure CoheytingHom (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHom α β where
  protected map_top' : toFun ⊤ = ⊤
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b
structure BiheytingHom (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHom α β where
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b
class HeytingHomClass (F α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β]
  extends LatticeHomClass F α β : Prop where
  map_bot (f : F) : f ⊥ = ⊥
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
class CoheytingHomClass (F α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β]
  extends LatticeHomClass F α β : Prop where
  map_top (f : F) : f ⊤ = ⊤
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b
class BiheytingHomClass (F α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β]
  extends LatticeHomClass F α β : Prop where
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b
export HeytingHomClass (map_himp)
export CoheytingHomClass (map_sdiff)
attribute [simp] map_himp map_sdiff
section Hom
variable [FunLike F α β]
instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [HeytingAlgebra α]
    { _ : HeytingAlgebra β} [HeytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }
instance (priority := 100) CoheytingHomClass.toBoundedLatticeHomClass [CoheytingAlgebra α]
    { _ : CoheytingAlgebra β} [CoheytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹CoheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, map_sdiff] }
instance (priority := 100) BiheytingHomClass.toHeytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [BiheytingHomClass F α β] : HeytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, BiheytingHomClass.map_sdiff] }
instance (priority := 100) BiheytingHomClass.toCoheytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [BiheytingHomClass F α β] : CoheytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }
end Hom
section Equiv
variable [EquivLike F α β]
instance (priority := 100) OrderIsoClass.toHeytingHomClass [HeytingAlgebra α]
    { _ : HeytingAlgebra β} [OrderIsoClass F α β] : HeytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }
instance (priority := 100) OrderIsoClass.toCoheytingHomClass [CoheytingAlgebra α]
    { _ : CoheytingAlgebra β} [OrderIsoClass F α β] : CoheytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }
instance (priority := 100) OrderIsoClass.toBiheytingHomClass [BiheytingAlgebra α]
    { _ : BiheytingAlgebra β} [OrderIsoClass F α β] : BiheytingHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }
end Equiv
variable [FunLike F α β]
lemma BoundedLatticeHomClass.toBiheytingHomClass [BooleanAlgebra α] [BooleanAlgebra β]
    [BoundedLatticeHomClass F α β] : BiheytingHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (isCompl_compl.map _).compl_eq]
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (isCompl_compl.map _).compl_eq] }
section HeytingAlgebra
open scoped symmDiff
variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] (f : F)
@[simp]
theorem map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [← himp_bot, ← himp_bot, map_himp, map_bot]
@[simp]
theorem map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b := by simp_rw [bihimp, map_inf, map_himp]
end HeytingAlgebra
section CoheytingAlgebra
open scoped symmDiff
variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] (f : F)
@[simp]
theorem map_hnot (a : α) : f (￢a) = ￢f a := by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]
@[simp]
theorem map_symmDiff (a b : α) : f (a ∆ b) = f a ∆ f b := by simp_rw [symmDiff, map_sup, map_sdiff]
end CoheytingAlgebra
instance [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩
instance [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
    CoeTC F (CoheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩
instance [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingHomClass F α β] :
    CoeTC F (BiheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_himp' := map_himp f
      map_sdiff' := map_sdiff f }⟩
namespace HeytingHom
variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]
instance instFunLike : FunLike (HeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
instance instHeytingHomClass : HeytingHomClass (HeytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'
theorem toFun_eq_coe {f : HeytingHom α β} : f.toFun = ⇑f :=
  rfl
@[simp]
theorem toFun_eq_coe_aux {f : HeytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl
@[ext]
theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : HeytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f
@[simp]
theorem coe_copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : HeytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : HeytingHom α α :=
  { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }
@[simp]
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl
instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩
instance : PartialOrder (HeytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }
variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}
@[simp]
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end HeytingHom
namespace CoheytingHom
variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingAlgebra γ] [CoheytingAlgebra δ]
instance : FunLike (CoheytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
instance : CoheytingHomClass (CoheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'
theorem toFun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α → β) :=
  rfl
@[simp]
theorem toFun_eq_coe_aux {f : CoheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl
@[ext]
theorem ext {f g : CoheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : CoheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f
@[simp]
theorem coe_copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : CoheytingHom α α :=
  { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }
@[simp]
theorem coe_id : ⇑(CoheytingHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : CoheytingHom.id α a = a :=
  rfl
instance : Inhabited (CoheytingHom α α) :=
  ⟨CoheytingHom.id _⟩
instance : PartialOrder (CoheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
    map_sdiff' := fun a b => by simp }
variable {f f₁ f₂ : CoheytingHom α β} {g g₁ g₂ : CoheytingHom β γ}
@[simp]
theorem coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => CoheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end CoheytingHom
namespace BiheytingHom
variable [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingAlgebra γ] [BiheytingAlgebra δ]
instance : FunLike (BiheytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
instance : BiheytingHomClass (BiheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'
theorem toFun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α → β) :=
  rfl
@[simp]
theorem toFun_eq_coe_aux {f : BiheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl
@[ext]
theorem ext {f g : BiheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
protected def copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : BiheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f
@[simp]
theorem coe_copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable (α)
protected def id : BiheytingHom α α :=
  { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }
@[simp]
theorem coe_id : ⇑(BiheytingHom.id α) = id :=
  rfl
variable {α}
@[simp]
theorem id_apply (a : α) : BiheytingHom.id α a = a :=
  rfl
instance : Inhabited (BiheytingHom α α) :=
  ⟨BiheytingHom.id _⟩
instance : PartialOrder (BiheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective
def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
    map_sdiff' := fun a b => by simp }
variable {f f₁ f₂ : BiheytingHom α β} {g g₁ g₂ : BiheytingHom β γ}
@[simp]
theorem coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩
@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => BiheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
end BiheytingHom