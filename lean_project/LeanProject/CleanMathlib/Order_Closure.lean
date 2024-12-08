import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.GaloisConnection
import Mathlib.Order.Hom.Basic
open Set
variable (α : Type*) {ι : Sort*} {κ : ι → Sort*}
structure ClosureOperator [Preorder α] extends α →o α where
  le_closure' : ∀ x, x ≤ toFun x
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop
namespace ClosureOperator
instance [Preorder α] : FunLike (ClosureOperator α) α α where
  coe c := c.1
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all
instance [Preorder α] : OrderHomClass (ClosureOperator α) α α where
  map_rel f _ _ h := f.mono h
initialize_simps_projections ClosureOperator (toFun → apply, IsClosed → isClosed)
@[simps apply]
def conjBy {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
    (e : α ≃o β) : ClosureOperator β where
  toFun := e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
    (map_le_map_iff e).mpr <| c.monotone <| (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
    congrArg e <| Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := Iff.trans c.isClosed_iff e.eq_symm_apply
lemma conjBy_refl {α} [Preorder α] (c : ClosureOperator α) :
    c.conjBy (OrderIso.refl α) = c := rfl
lemma conjBy_trans {α β γ} [Preorder α] [Preorder β] [Preorder γ]
    (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : ClosureOperator α) :
    c.conjBy (e₁.trans e₂) = (c.conjBy e₁).conjBy e₂ := rfl
section PartialOrder
variable [PartialOrder α]
@[simps!]
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True
instance : Inhabited (ClosureOperator α) :=
  ⟨id α⟩
variable {α}
variable (c : ClosureOperator α)
@[ext]
theorem ext : ∀ c₁ c₂ : ClosureOperator α, (∀ x, c₁ x = c₂ x) → c₁ = c₂ :=
  DFunLike.ext
@[simps]
def mk' (f : α → α) (hf₁ : Monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
    ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) :
    ClosureOperator α where
  toFun := f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)
@[simps!]
def ofPred (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
    (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) : ClosureOperator α where
  __ := mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
  isClosed_iff := ⟨fun hx ↦ (hmin le_rfl hx).antisymm <| hf _, fun hx ↦ hx ▸ hfp _⟩
@[mono]
theorem monotone : Monotone c :=
  c.monotone'
theorem le_closure (x : α) : x ≤ c x :=
  c.le_closure' x
@[simp]
theorem idempotent (x : α) : c (c x) = c x :=
  c.idempotent' x
@[simp] lemma isClosed_closure (x : α) : c.IsClosed (c x) := c.isClosed_iff.2 <| c.idempotent x
abbrev Closeds := {x // c.IsClosed x}
def toCloseds (x : α) : c.Closeds := ⟨c x, c.isClosed_closure x⟩
variable {c} {x y : α}
theorem IsClosed.closure_eq : c.IsClosed x → c x = x := c.isClosed_iff.1
theorem isClosed_iff_closure_le : c.IsClosed x ↔ c x ≤ x :=
  ⟨fun h ↦ h.closure_eq.le, fun h ↦ c.isClosed_iff.2 <| h.antisymm <| c.le_closure x⟩
theorem setOf_isClosed_eq_range_closure : {x | c.IsClosed x} = Set.range c := by
  ext x; exact ⟨fun hx ↦ ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩
theorem le_closure_iff : x ≤ c y ↔ c x ≤ c y :=
  ⟨fun h ↦ c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩
@[simp]
theorem IsClosed.closure_le_iff (hy : c.IsClosed y) : c x ≤ y ↔ x ≤ y := by
  rw [← hy.closure_eq, ← le_closure_iff]
lemma closure_min (hxy : x ≤ y) (hy : c.IsClosed y) : c x ≤ y := hy.closure_le_iff.2 hxy
lemma closure_isGLB (x : α) : IsGLB { y | x ≤ y ∧ c.IsClosed y } (c x) where
  left _ := and_imp.mpr closure_min
  right _ h := h ⟨c.le_closure x, c.isClosed_closure x⟩
theorem ext_isClosed (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁.IsClosed x ↔ c₂.IsClosed x) : c₁ = c₂ :=
  ext c₁ c₂ <| fun x => IsGLB.unique (c₁.closure_isGLB x) <|
    (Set.ext (and_congr_right' <| h ·)).substr (c₂.closure_isGLB x)
theorem eq_ofPred_closed (c : ClosureOperator α) :
    c = ofPred c c.IsClosed c.le_closure c.isClosed_closure fun _ _ ↦ closure_min := by
  ext
  rfl
end PartialOrder
variable {α}
section OrderTop
variable [PartialOrder α] [OrderTop α] (c : ClosureOperator α)
@[simp]
theorem closure_top : c ⊤ = ⊤ :=
  le_top.antisymm (c.le_closure _)
@[simp] lemma isClosed_top : c.IsClosed ⊤ := c.isClosed_iff.2 c.closure_top
end OrderTop
theorem closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) :
    c (x ⊓ y) ≤ c x ⊓ c y :=
  c.monotone.map_inf_le _ _
section SemilatticeSup
variable [SemilatticeSup α] (c : ClosureOperator α)
theorem closure_sup_closure_le (x y : α) : c x ⊔ c y ≤ c (x ⊔ y) :=
  c.monotone.le_map_sup _ _
theorem closure_sup_closure_left (x y : α) : c (c x ⊔ y) = c (x ⊔ y) :=
  (le_closure_iff.1
        (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _)))).antisymm
    (c.monotone (sup_le_sup_right (c.le_closure _) _))
theorem closure_sup_closure_right (x y : α) : c (x ⊔ c y) = c (x ⊔ y) := by
  rw [sup_comm, closure_sup_closure_left, sup_comm (a := x)]
theorem closure_sup_closure (x y : α) : c (c x ⊔ c y) = c (x ⊔ y) := by
  rw [closure_sup_closure_left, closure_sup_closure_right]
end SemilatticeSup
section CompleteLattice
variable [CompleteLattice α] (c : ClosureOperator α)
@[simps!]
def ofCompletePred (p : α → Prop) (hsinf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : ClosureOperator α :=
  ofPred (fun a ↦ ⨅ b : {b // a ≤ b ∧ p b}, b) p
    (fun a ↦ by simp (config := {contextual := true}))
    (fun _ ↦ hsinf _ <| forall_mem_range.2 fun b ↦ b.2.2)
    (fun _ b hab hb ↦ iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)
theorem sInf_isClosed {c : ClosureOperator α} {S : Set α}
    (H : ∀ x ∈ S, c.IsClosed x) : c.IsClosed (sInf S) :=
  isClosed_iff_closure_le.mpr <| le_of_le_of_eq c.monotone.map_sInf_le <|
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm
@[simp]
theorem closure_iSup_closure (f : ι → α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
  le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i) <|
    c.monotone <| iSup_mono fun _ => c.le_closure _
@[simp]
theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    c (⨆ (i) (j), c (f i j)) = c (⨆ (i) (j), f i j) :=
  le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j) <|
    c.monotone <| iSup₂_mono fun _ _ => c.le_closure _
end CompleteLattice
end ClosureOperator
@[simps apply symm_apply]
def OrderIso.equivClosureOperator {α β} [Preorder α] [Preorder β] (e : α ≃o β) :
    ClosureOperator α ≃ ClosureOperator β where
  toFun     c := c.conjBy e
  invFun    c := c.conjBy e.symm
  left_inv  c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl
variable {α} {β : Type*}
structure LowerAdjoint [Preorder α] [Preorder β] (u : β → α) where
  toFun : α → β
  gc' : GaloisConnection toFun u
namespace LowerAdjoint
variable (α)
@[simps]
protected def id [Preorder α] : LowerAdjoint (id : α → α) where
  toFun x := x
  gc' := GaloisConnection.id
variable {α}
instance [Preorder α] : Inhabited (LowerAdjoint (id : α → α)) :=
  ⟨LowerAdjoint.id α⟩
section Preorder
variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)
instance : CoeFun (LowerAdjoint u) fun _ => α → β where coe := toFun
theorem gc : GaloisConnection l u :=
  l.gc'
@[ext]
theorem ext : ∀ l₁ l₂ : LowerAdjoint u, (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
  | ⟨l₁, _⟩, ⟨l₂, _⟩, h => by
    congr
@[mono]
theorem monotone : Monotone (u ∘ l) :=
  l.gc.monotone_u.comp l.gc.monotone_l
theorem le_closure (x : α) : x ≤ u (l x) :=
  l.gc.le_u_l _
end Preorder
section PartialOrder
variable [PartialOrder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)
@[simps]
def closureOperator : ClosureOperator α where
  toFun x := u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)
theorem idempotent (x : α) : u (l (u (l x))) = u (l x) :=
  l.closureOperator.idempotent _
theorem le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
  l.closureOperator.le_closure_iff
end PartialOrder
section Preorder
variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)
def closed : Set α := {x | u (l x) = x}
theorem mem_closed_iff (x : α) : x ∈ l.closed ↔ u (l x) = x :=
  Iff.rfl
theorem closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.closed) : u (l x) = x :=
  h
end Preorder
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {u : β → α} (l : LowerAdjoint u)
theorem mem_closed_iff_closure_le (x : α) : x ∈ l.closed ↔ u (l x) ≤ x :=
  l.closureOperator.isClosed_iff_closure_le
@[simp]
theorem closure_is_closed (x : α) : u (l x) ∈ l.closed :=
  l.idempotent x
theorem closed_eq_range_close : l.closed = Set.range (u ∘ l) :=
  l.closureOperator.setOf_isClosed_eq_range_closure
def toClosed (x : α) : l.closed :=
  ⟨u (l x), l.closure_is_closed x⟩
@[simp]
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : l.closed y) : u (l x) ≤ y ↔ x ≤ y :=
  (show l.closureOperator.IsClosed y from hy).closure_le_iff
end PartialOrder
theorem closure_top [PartialOrder α] [OrderTop α] [Preorder β] {u : β → α} (l : LowerAdjoint u) :
    u (l ⊤) = ⊤ :=
  l.closureOperator.closure_top
theorem closure_inf_le [SemilatticeInf α] [Preorder β] {u : β → α} (l : LowerAdjoint u) (x y : α) :
    u (l (x ⊓ y)) ≤ u (l x) ⊓ u (l y) :=
  l.closureOperator.closure_inf_le x y
section SemilatticeSup
variable [SemilatticeSup α] [Preorder β] {u : β → α} (l : LowerAdjoint u)
theorem closure_sup_closure_le (x y : α) : u (l x) ⊔ u (l y) ≤ u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_le x y
theorem closure_sup_closure_left (x y : α) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_left x y
theorem closure_sup_closure_right (x y : α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_right x y
theorem closure_sup_closure (x y : α) : u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure x y
end SemilatticeSup
section CompleteLattice
variable [CompleteLattice α] [Preorder β] {u : β → α} (l : LowerAdjoint u)
theorem closure_iSup_closure (f : ι → α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i)) :=
  l.closureOperator.closure_iSup_closure _
theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    u (l <| ⨆ (i) (j), u (l <| f i j)) = u (l <| ⨆ (i) (j), f i j) :=
  l.closureOperator.closure_iSup₂_closure _
end CompleteLattice
section CoeToSet
variable [SetLike α β] (l : LowerAdjoint ((↑) : α → Set β))
theorem subset_closure (s : Set β) : s ⊆ l s :=
  l.le_closure s
theorem not_mem_of_not_mem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s := fun h =>
  hP (subset_closure _ s h)
theorem le_iff_subset (s : Set β) (S : α) : l s ≤ S ↔ s ⊆ S :=
  l.gc s S
theorem mem_iff (s : Set β) (x : β) : x ∈ l s ↔ ∀ S : α, s ⊆ S → x ∈ S := by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩
theorem eq_of_le {s : Set β} {S : α} (h₁ : s ⊆ S) (h₂ : S ≤ l s) : l s = S :=
  ((l.le_iff_subset _ _).2 h₁).antisymm h₂
theorem closure_union_closure_subset (x y : α) : (l x : Set β) ∪ l y ⊆ l (x ∪ y) :=
  l.closure_sup_closure_le x y
@[simp]
theorem closure_union_closure_left (x y : α) : l (l x ∪ y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_left x y)
@[simp]
theorem closure_union_closure_right (x y : α) : l (x ∪ l y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_right x y)
theorem closure_union_closure (x y : α) : l (l x ∪ l y) = l (x ∪ y) := by
  rw [closure_union_closure_right, closure_union_closure_left]
@[simp]
theorem closure_iUnion_closure (f : ι → α) : l (⋃ i, l (f i)) = l (⋃ i, f i) :=
  SetLike.coe_injective <| l.closure_iSup_closure _
@[simp]
theorem closure_iUnion₂_closure (f : ∀ i, κ i → α) :
    l (⋃ (i) (j), l (f i j)) = l (⋃ (i) (j), f i j) :=
  SetLike.coe_injective <| l.closure_iSup₂_closure _
end CoeToSet
end LowerAdjoint
@[simps]
def GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : LowerAdjoint u where
  toFun := l
  gc' := gc
@[simps!]
def GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.lowerAdjoint.closureOperator
def ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) :
    GaloisInsertion c.toCloseds (↑) where
  choice x hx := ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx
@[simp]
theorem closureOperator_gi_self [PartialOrder α] (c : ClosureOperator α) :
    c.gi.gc.closureOperator = c := by
  ext x
  rfl