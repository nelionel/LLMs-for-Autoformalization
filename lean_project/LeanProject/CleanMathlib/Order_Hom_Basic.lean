import Mathlib.Logic.Equiv.Option
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.WithBot
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Util.AssertExists
assert_not_exists Set.range
open OrderDual
variable {F α β γ δ : Type*}
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  toFun : α → β
  monotone' : Monotone toFun
infixr:25 " →o " => OrderHom
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)
infixl:25 " ↪o " => OrderEmbedding
abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)
infixl:25 " ≃o " => OrderIso
section
abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)
class OrderIsoClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β] :
    Prop where
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b
end
export OrderIsoClass (map_le_map_iff)
attribute [simp] map_le_map_iff
@[coe]
def OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F) :
    α ≃o β :=
  { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }
instance [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨OrderIsoClass.toOrderIso⟩
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β]
    [EquivLike F α β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike (E := F) with
    map_rel := fun f _ _ => (map_le_map_iff f).2 }
namespace OrderHomClass
variable [Preorder α] [Preorder β] [FunLike F α β] [OrderHomClass F α β]
protected theorem monotone (f : F) : Monotone f := fun _ _ => map_rel f
protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f
@[gcongr] protected lemma GCongr.mono (f : F) {a b : α} (hab : a ≤ b) : f a ≤ f b :=
  OrderHomClass.mono f hab
@[coe]
def toOrderHom (f : F) : α →o β where
  toFun := f
  monotone' := OrderHomClass.monotone f
instance : CoeTC F (α →o β) :=
  ⟨toOrderHom⟩
end OrderHomClass
section OrderIsoClass
section LE
variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]
@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff f (a := EquivLike.inv f b) (b := a)).symm
  exact (EquivLike.right_inv f _).symm
theorem map_inv_le_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b ≤ EquivLike.inv f a ↔ b ≤ a := by
  simp
@[simp]
theorem le_map_inv_iff (f : F) {a : α} {b : β} : a ≤ EquivLike.inv f b ↔ f a ≤ b := by
  convert (map_le_map_iff f (a := a) (b := EquivLike.inv f b)).symm
  exact (EquivLike.right_inv _ _).symm
end LE
variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]
theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)
@[simp]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
theorem map_inv_lt_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b < EquivLike.inv f a ↔ b < a := by
  simp
@[simp]
theorem lt_map_inv_iff (f : F) {a : α} {b : β} : a < EquivLike.inv f b ↔ f a < b := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]
end OrderIsoClass
namespace OrderHom
variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
instance : FunLike (α →o β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
instance : OrderHomClass (α →o β) α β where
  map_rel f _ _ h := f.monotone' h
@[simp] theorem coe_mk (f : α → β) (hf : Monotone f) : ⇑(mk f hf) = f := rfl
protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'
protected theorem mono (f : α →o β) : Monotone f :=
  f.monotone
def Simps.coe (f : α →o β) : α → β := f
initialize_simps_projections OrderHom (toFun → coe)
@[simp] theorem toFun_eq_coe (f : α →o β) : f.toFun = f := rfl
@[ext]
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h
@[simp] theorem coe_eq (f : α →o β) : OrderHomClass.toOrderHom f = f := rfl
@[simp] theorem _root_.OrderHomClass.coe_coe {F} [FunLike F α β] [OrderHomClass F α β] (f : F) :
    ⇑(f : α →o β) = f :=
  rfl
protected instance canLift : CanLift (α → β) (α →o β) (↑) Monotone where
  prf f h := ⟨⟨f, h⟩, rfl⟩
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩
@[simp]
theorem coe_copy (f : α →o β) (f' : α → β) (h : f' = f) : (f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : α →o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
@[simps (config := .asFn)]
def id : α →o α :=
  ⟨_root_.id, monotone_id⟩
instance : Inhabited (α →o α) :=
  ⟨id⟩
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ toFun
instance {β : Type*} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ toFun ext
theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl
@[simp]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl
@[mono]
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂
def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun f := ⟨fun x ↦ ⟨Function.curry f x, fun _ _ h ↦ f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x ↦ f x, fun x y h ↦ (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp [le_def]
@[simp]
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl
@[simp]
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl
@[simps (config := .asFn)]
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩
@[mono]
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
    g₁.comp f₁ ≤ g₂.comp f₂ := fun _ => (hg _).trans (g₂.mono <| hf _)
@[simp] lemma mk_comp_mk (g : β → γ) (f : α → β) (hg hf) :
    comp ⟨g, hg⟩ ⟨f, hf⟩ = ⟨g ∘ f, hg.comp hf⟩ := rfl
@[simps! (config := .asFn)]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩
@[simp]
theorem comp_id (f : α →o β) : comp f id = f := by
  ext
  rfl
@[simp]
theorem id_comp (f : α →o β) : comp id f = f := by
  ext
  rfl
@[simps (config := .asFn)]
def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β →o α →o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h
@[simp]
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl
@[simp]
theorem comp_const (γ : Type*) [Preorder γ] (f : α →o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl
@[simps]
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩
@[mono]
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
    f₁.prod g₁ ≤ f₂.prod g₂ := fun _ => Prod.le_def.2 ⟨hf _, hg _⟩
theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
    (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl
@[simps!]
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩
@[simps!]
def diag : α →o α × α :=
  id.prod id
@[simps! (config := { simpRhs := true })]
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag
@[simps]
def fst : α × β →o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩
@[simps]
def snd : α × β →o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩
@[simp]
theorem fst_prod_snd : (fst : α × β →o α).prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl
@[simp]
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl
@[simp]
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl
@[simps]
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_and.symm
@[simps]
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩
variable {ι : Type*} {π : ι → Type*} [∀ i, Preorder (π i)]
@[simps (config := .asFn)]
def _root_.Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩
@[simps (config := .asFn)]
def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' _ _ h := h
@[simps! (config := .asFn)]
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩
@[simps]
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := forall_swap
@[simps (config := .asFn)]
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩
@[simps!]
def _root_.Subtype.orderEmbedding {p q : α → Prop} (h : ∀ a, p a → q a) :
    {x // p x} ↪o {x // q x} :=
  { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }
instance unique [Subsingleton α] : Unique (α →o α) where
  default := OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)
theorem orderHom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elim _ _
@[simps]
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β → βᵒᵈ) ∘ (f : α → β) ∘
    (OrderDual.ofDual : αᵒᵈ → α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp]
theorem dual_id : (OrderHom.id : α →o α).dual = OrderHom.id :=
  rfl
@[simp]
theorem dual_comp (g : β →o γ) (f : α →o β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl
@[simp]
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl
@[simp]
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl
def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl
@[simps (config := .asFn)]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩
@[simps (config := .asFn)]
protected def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.withTop_map⟩
end OrderHom
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      intros
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }
@[simp]
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl
namespace OrderEmbedding
variable [Preorder α] [Preorder β] (f : α ↪o β)
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by intros; simp [lt_iff_le_not_le, f.map_rel_iff] }
@[simp]
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl
@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff
@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff
theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff
protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f
protected theorem strictMono : StrictMono f := fun _ _ => f.lt_iff_lt.2
protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.acc a
protected theorem wellFounded (f : α ↪o β) :
    WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.wellFounded
protected theorem isWellOrder [IsWellOrder β (· < ·)] (f : α ↪o β) : IsWellOrder α (· < ·) :=
  f.ltEmbedding.isWellOrder
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩
protected theorem wellFoundedLT [WellFoundedLT β] (f : α ↪o β) : WellFoundedLT α where
  wf := f.wellFounded IsWellFounded.wf
protected theorem wellFoundedGT [WellFoundedGT β] (f : α ↪o β) : WellFoundedGT α :=
  @OrderEmbedding.wellFoundedLT αᵒᵈ _ _ _ _ f.dual
@[simps (config := .asFn)]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β :=
  { f.toEmbedding.optionMap with
    toFun := WithBot.map f,
    map_rel_iff' := @fun a b => WithBot.map_le_iff f f.map_rel_iff a b }
@[simps (config := .asFn)]
protected def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.withBotMap.dual with toFun := WithTop.map f }
@[simps (config := .asFn)]
protected def withBotCoe : α ↪o WithBot α where
  toFun := .some
  inj' := Option.some_injective _
  map_rel_iff' := WithBot.coe_le_coe
@[simps (config := .asFn)]
protected def withTopCoe : α ↪o WithTop α :=
  { (OrderEmbedding.withBotCoe (α := αᵒᵈ)).dual with toFun := .some }
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf
@[simp]
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α → β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le
@[simp]
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl
@[simps! (config := .asFn)]
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩
@[simps (config := .asFn)]
def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.monotone
@[simps] def ofIsEmpty [IsEmpty α] : α ↪o β where
  toFun := isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a
@[simp, norm_cast]
lemma coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α → β) := rfl
end OrderEmbedding
section Disjoint
variable [PartialOrder α] [PartialOrder β] (f : OrderEmbedding α β)
lemma Disjoint.of_orderEmbedding [OrderBot α] [OrderBot β] {a₁ a₂ : α} :
    Disjoint (f a₁) (f a₂) → Disjoint a₁ a₂ := by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x ≤ ⊥ := h h₁ h₂
    _ ≤ f ⊥ := bot_le
lemma Codisjoint.of_orderEmbedding [OrderTop α] [OrderTop β] {a₁ a₂ : α} :
    Codisjoint (f a₁) (f a₂) → Codisjoint a₁ a₂ :=
  Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual
lemma IsCompl.of_orderEmbedding [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α} :
    IsCompl (f a₁) (f a₂) → IsCompl a₁ a₂ := fun ⟨hd, hcd⟩ ↦
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩
end Disjoint
section RelHom
variable [PartialOrder α] [Preorder β]
namespace RelHom
variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))
@[simps (config := .asFn)]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel
end RelHom
theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom :=
  fun _ _ h => f.injective h
end RelHom
namespace OrderIso
section LE
variable [LE α] [LE β] [LE γ]
instance : EquivLike (α ≃o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
instance : OrderIsoClass (α ≃o β) α β where
  map_le_map_iff f _ _ := f.map_rel_iff'
@[simp]
theorem toFun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl
@[ext]
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding
@[simp]
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl
protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.bijective
protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.injective
protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.surjective
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)
@[simp]
theorem coe_refl : ⇑(refl α) = id :=
  rfl
@[simp]
theorem refl_apply (x : α) : refl α x = x :=
  rfl
@[simp]
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl
def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
@[simp]
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x
@[simp]
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
@[simp]
theorem symm_refl (α : Type*) [LE α] : (refl α).symm = refl α :=
  rfl
theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq
@[simp]
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := rfl
theorem symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) → β ≃o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) :=
  symm_bijective.injective
@[simp]
theorem toEquiv_symm (e : α ≃o β) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl
@[trans]
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'
@[simp]
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl
@[simp]
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl
@[simp]
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl
@[simp]
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl
@[simp]
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl
theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
@[simp]
theorem self_trans_symm (e : α ≃o β) : e.trans e.symm = OrderIso.refl α :=
  RelIso.self_trans_symm e
@[simp]
theorem symm_trans_self (e : α ≃o β) : e.symm.trans e = OrderIso.refl β :=
  RelIso.symm_trans_self e
@[simps apply symm_apply]
def arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α →o β) ≃o (γ →o δ) where
  toFun  p := .comp g <| .comp p f.symm
  invFun p := .comp g.symm <| .comp p f
  left_inv p := DFunLike.coe_injective <| by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
  right_inv p := DFunLike.coe_injective <| by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← DFunLike.coe_eq_coe_fn, ← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left
@[simps! apply symm_apply]
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α →o α) ≃ (β →o β) :=
  arrowCongr f f
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap
@[simp]
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl
@[simp]
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl
variable (α)
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α
@[simp]
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl
@[simp]
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl
variable {α}
@[simp]
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl
@[simp]
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl
end LE
open Set
section LE
variable [LE α] [LE β]
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff
@[gcongr] protected alias ⟨_, GCongr.orderIso_apply_le_apply⟩ := le_iff_le
theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply
theorem symm_apply_le (e : α ≃o β) {x : α} {y : β} : e.symm y ≤ x ↔ y ≤ e x :=
  e.symm_apply_rel
end LE
variable [Preorder α] [Preorder β]
protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.monotone
protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.strictMono
@[simp]
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt
@[gcongr] protected alias ⟨_, GCongr.orderIso_apply_lt_apply⟩ := lt_iff_lt
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩
@[simp]
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl
@[simp]
theorem toRelIsoLT_symm (e : α ≃o β) : e.toRelIsoLT.symm = e.symm.toRelIsoLT :=
  rfl
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩
@[simp]
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl
@[simp]
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl
@[simp]
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by
  ext
  simp
@[simp]
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext
  simp
def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq],
    map_rel_iff' := by
      intros a b
      apply le_iff_le_of_cmp_eq_cmp
      convert (h a (f b)).symm
      apply gf }
def ofHomInv {F G : Type*} [FunLike F α β] [OrderHomClass F α β] [FunLike G β α]
    [OrderHomClass G β α] (f : F) (g : G)
    (h₁ : (f : α →o β).comp (g : β →o α) = OrderHom.id)
    (h₂ : (g : β →o α).comp (f : α →o β) = OrderHom.id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' := @fun a b =>
    ⟨fun h => by
      replace h := map_rel g h
      rwa [Equiv.coe_fn_mk, show g (f a) = (g : β →o α).comp (f : α →o β) a from rfl,
        show g (f b) = (g : β →o α).comp (f : α →o β) b from rfl, h₂] at h,
      fun h => (f : α →o β).monotone h⟩
@[simps! toEquiv apply]
def funUnique (α β : Type*) [Unique α] [Preorder β] : (α → β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]
@[simp]
theorem funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl
end OrderIso
namespace Equiv
variable [Preorder α] [Preorder β]
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩
@[simp]
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl
@[simp]
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl
end Equiv
namespace StrictMono
variable [LinearOrder α] [Preorder β]
variable (f : α → β) (h_mono : StrictMono f)
@[simps (config := .asFn)]
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
    left_inv := fun _ => h_mono.injective <| hg _,
    right_inv := hg }
end StrictMono
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.map_rel_iff⟩
section LatticeIsos
theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y, f.map_rel_iff]
  apply hx
theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le
theorem OrderIso.map_top' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x' ≤ x)
    (hy : ∀ y', y' ≤ y) : f x = y :=
  f.dual.map_bot' hx hy
theorem OrderIso.map_top [LE α] [PartialOrder β] [OrderTop α] [OrderTop β] (f : α ≃o β) : f ⊤ = ⊤ :=
  f.dual.map_bot
theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  f.monotone.map_inf_le x y
theorem OrderEmbedding.le_map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ↪o β) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  f.monotone.le_map_sup x y
theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y := by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)
theorem OrderIso.map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ≃o β) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  f.dual.map_inf x y
theorem OrderIso.isMax_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α} :
    IsMax (f x) ↔ IsMax x := by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply
theorem OrderIso.isMin_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α} :
    IsMin (f x) ↔ IsMin x := by
  refine ⟨f.strictMono.isMin_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMin_of_apply
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le, ← f.map_inf, ← f.map_bot]
  exact f.monotone ha.le_bot
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup, ← f.map_sup, ← f.map_top]
  exact f.monotone ha.top_le
@[simp]
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩
@[simp]
theorem codisjoint_map_orderIso_iff [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) : Codisjoint (f a) (f b) ↔ Codisjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩
namespace WithBot
protected def toDualTopEquiv [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _
@[simp]
theorem toDualTopEquiv_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv ↑(toDual a) = toDual (a : WithTop α) :=
  rfl
@[simp]
theorem toDualTopEquiv_symm_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv.symm (toDual (a : WithTop α)) = ↑(toDual a) :=
  rfl
@[simp]
theorem toDualTopEquiv_bot [LE α] : WithBot.toDualTopEquiv (⊥ : WithBot αᵒᵈ) = ⊥ :=
  rfl
@[simp]
theorem toDualTopEquiv_symm_bot [LE α] : WithBot.toDualTopEquiv.symm (⊥ : (WithTop α)ᵒᵈ) = ⊥ :=
  rfl
theorem coe_toDualTopEquiv_eq [LE α] :
    (WithBot.toDualTopEquiv : WithBot αᵒᵈ → (WithTop α)ᵒᵈ) = toDual ∘ WithBot.ofDual :=
  funext fun _ => rfl
@[simps]
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithBot α where
  toFun := (↑)
  inj' := WithBot.coe_injective
  map_rel_iff' := WithBot.coe_le_coe
end WithBot
namespace WithTop
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _
@[simp]
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl
@[simp]
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl
@[simp]
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl
@[simp]
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl
theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl
@[simps]
def coeOrderHom {α : Type*} [Preorder α] : α ↪o WithTop α where
  toFun := (↑)
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe
end WithTop
namespace OrderIso
variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]
@[simps! apply]
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β :=
  { e.toOrderEmbedding.withTopMap with
    toEquiv := e.toEquiv.optionCongr }
@[simp]
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
@[simp]
theorem withTopCongr_symm (e : α ≃o β) : e.withTopCongr.symm = e.symm.withTopCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
@[simp]
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withTopCongr.trans e₂.withTopCongr = (e₁.trans e₂).withTopCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
@[simps! apply]
def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β :=
  { e.toOrderEmbedding.withBotMap with toEquiv := e.toEquiv.optionCongr }
@[simp]
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
@[simp]
theorem withBotCongr_symm (e : α ≃o β) : e.withBotCongr.symm = e.symm.withBotCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
@[simp]
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withBotCongr.trans e₂.withBotCongr = (e₁.trans e₂).withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
end OrderIso
section BoundedOrder
variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)
theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩
theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩
theorem OrderIso.complementedLattice [ComplementedLattice α] (f : α ≃o β) : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩
theorem OrderIso.complementedLattice_iff (f : α ≃o β) :
    ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩
end BoundedOrder
end LatticeIsos
section DenselyOrdered
lemma denselyOrdered_iff_of_orderIsoClass {X Y F : Type*} [Preorder X] [Preorder Y]
    [EquivLike F X Y] [OrderIsoClass F X Y] (f : F) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  constructor
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, by simpa using hc⟩
end DenselyOrdered