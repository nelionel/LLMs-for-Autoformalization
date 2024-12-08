import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Says
open Function Set
universe u v w z
variable {α : Sort u} {β : Sort v} {γ : Sort w}
namespace Equiv
@[simp]
theorem range_eq_univ {α : Type*} {β : Type*} (e : α ≃ β) : range e = univ :=
  eq_univ_of_forall e.surjective
protected theorem image_eq_preimage {α β} (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  Set.ext fun _ => mem_image_iff_of_inverse e.left_inv e.right_inv
@[simp 1001]
theorem _root_.Set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} :
    x ∈ f '' S ↔ f.symm x ∈ S :=
  Set.ext_iff.mp (f.image_eq_preimage S) x
theorem _root_.Set.image_equiv_eq_preimage_symm {α β} (S : Set α) (f : α ≃ β) :
    f '' S = f.symm ⁻¹' S :=
  f.image_eq_preimage S
theorem _root_.Set.preimage_equiv_eq_image_symm {α β} (S : Set α) (f : β ≃ α) :
    f ⁻¹' S = f.symm '' S :=
  (f.symm.image_eq_preimage S).symm
@[simp high]
protected theorem symm_image_subset {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    e.symm '' t ⊆ s ↔ t ⊆ e '' s := by rw [image_subset_iff, e.image_eq_preimage]
@[simp high]
protected theorem subset_symm_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
  calc
    s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t := by rw [e.symm.symm_image_subset]
    _ ↔ e '' s ⊆ t := by rw [e.symm_symm]
@[simp]
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.leftInverse_symm.image_image s
theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) :
    t = e '' s ↔ e.symm '' t = s :=
  (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm
@[simp]
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s
@[simp]
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.surjective.image_preimage s
@[simp]
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.injective.preimage_image s
protected theorem image_compl {α β} (f : Equiv α β) (s : Set α) : f '' sᶜ = (f '' s)ᶜ :=
  image_compl_eq f.bijective
@[simp]
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.rightInverse_symm.preimage_preimage s
@[simp]
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.leftInverse_symm.preimage_preimage s
theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
  e.surjective.preimage_subset_preimage_iff
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
  image_subset_image_iff e.injective
@[simp]
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  image_eq_image e.injective
theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
  Set.preimage_eq_iff_eq_image e.bijective
theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
  Set.eq_preimage_iff_image_eq e.bijective
lemma setOf_apply_symm_eq_image_setOf {α β} (e : α ≃ β) (p : α → Prop) :
    {b | p (e.symm b)} = e '' {a | p a} := by
  rw [Equiv.image_eq_preimage, preimage_setOf_eq]
@[simp]
theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ ⁻¹' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  ext
  simp [and_assoc]
@[simp]
theorem prod_assoc_symm_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm ⁻¹' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  ext
  simp [and_assoc]
theorem prod_assoc_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    Equiv.prodAssoc α β γ '' (s ×ˢ t) ×ˢ u = s ×ˢ t ×ˢ u := by
  simpa only [Equiv.image_eq_preimage] using prod_assoc_symm_preimage
theorem prod_assoc_symm_image {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
    (Equiv.prodAssoc α β γ).symm '' s ×ˢ t ×ˢ u = (s ×ˢ t) ×ˢ u := by
  simpa only [Equiv.image_eq_preimage] using prod_assoc_preimage
def setProdEquivSigma {α β : Type*} (s : Set (α × β)) :
    s ≃ Σx : α, { y : β | (x, y) ∈ s } where
  toFun x := ⟨x.1.1, x.1.2, by simp⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl
@[simps! apply]
def setCongr {α : Type*} {s t : Set α} (h : s = t) : s ≃ t :=
  subtypeEquivProp h
@[simps]
def image {α β : Type*} (e : α ≃ β) (s : Set α) :
    s ≃ e '' s where
  toFun x := ⟨e x.1, by simp⟩
  invFun y :=
    ⟨e.symm y.1, by
      rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
      simpa using m⟩
  left_inv x := by simp
  right_inv y := by simp
namespace Set
@[simps apply symm_apply]
protected def univ (α) : @univ α ≃ α :=
  ⟨Subtype.val, fun a => ⟨a, trivial⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
protected def empty (α) : (∅ : Set α) ≃ Empty :=
  equivEmpty _
protected def pempty (α) : (∅ : Set α) ≃ PEmpty :=
  equivPEmpty _
protected def union' {α} {s t : Set α} (p : α → Prop) [DecidablePred p] (hs : ∀ x ∈ s, p x)
    (ht : ∀ x ∈ t, ¬p x) : (s ∪ t : Set α) ≃ s ⊕ t where
  toFun x :=
    if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩
    else Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩
  invFun o :=
    match o with
    | Sum.inl x => ⟨x, Or.inl x.2⟩
    | Sum.inr x => ⟨x, Or.inr x.2⟩
  left_inv := fun ⟨x, h'⟩ => by by_cases h : p x <;> simp [h]
  right_inv o := by
    rcases o with (⟨x, h⟩ | ⟨x, h⟩) <;> [simp [hs _ h]; simp [ht _ h]]
protected def union {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t) :
    (s ∪ t : Set α) ≃ s ⊕ t :=
  Set.union' (fun x => x ∈ s) (fun _ => id) fun _ xt xs => Set.disjoint_left.mp H xs xt
theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ s) : Equiv.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha
theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    {a : (s ∪ t : Set α)} (ha : ↑a ∈ t) : Equiv.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg fun h => Set.disjoint_left.mp H h ha
@[simp]
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    (a : s) : (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, by simp⟩ :=
  rfl
@[simp]
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : Disjoint s t)
    (a : t) : (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, by simp⟩ :=
  rfl
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩, fun ⟨x, h⟩ => by
    simp? at h says simp only [mem_singleton_iff] at h
    subst x
    rfl, fun ⟨⟩ => rfl⟩
@[simps! apply symm_apply]
protected def ofEq {α : Type u} {s t : Set α} (h : s = t) : s ≃ t :=
  Equiv.setCongr h
lemma Equiv.strictMono_setCongr {α : Type*} [PartialOrder α] {S T : Set α} (h : S = T) :
    StrictMono (setCongr h) := fun _ _ ↦ id
protected def insert {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    (insert a s : Set α) ≃ s ⊕ PUnit.{u + 1} :=
  calc
    (insert a s : Set α) ≃ ↥(s ∪ {a}) := Equiv.Set.ofEq (by simp)
    _ ≃ s ⊕ ({a} : Set α) := Equiv.Set.union <| by simpa
    _ ≃ s ⊕ PUnit.{u + 1} := sumCongr (Equiv.refl _) (Equiv.Set.singleton _)
@[simp]
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : s) : (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl
@[simp]
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s)
    (b : PUnit.{u + 1}) : (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl
@[simp]
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
    Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl
@[simp]
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
    Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl
protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : s ⊕ (sᶜ : Set α) ≃ α :=
  calc
    s ⊕ (sᶜ : Set α) ≃ ↥(s ∪ sᶜ) := (Equiv.Set.union disjoint_compl_right).symm
    _ ≃ @univ α := Equiv.Set.ofEq (by simp)
    _ ≃ α := Equiv.Set.univ _
@[simp]
theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl
@[simp]
theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
    Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl
theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ := by
  simp [Equiv.Set.sumCompl, Equiv.Set.univ, union_apply_left, hx]
theorem sumCompl_symm_apply_of_not_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ := by
  simp [Equiv.Set.sumCompl, Equiv.Set.univ, union_apply_right, hx]
@[simp]
theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] {x : s} :
    (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
  Set.sumCompl_symm_apply_of_mem x.2
@[simp]
theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
    {x : (sᶜ : Set α)} : (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
  Set.sumCompl_symm_apply_of_not_mem x.2
protected def sumDiffSubset {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] :
    s ⊕ (t \ s : Set α) ≃ t :=
  calc
    s ⊕ (t \ s : Set α) ≃ (s ∪ t \ s : Set α) :=
      (Equiv.Set.union disjoint_sdiff_self_right).symm
    _ ≃ t := Equiv.Set.ofEq (by simp [union_diff_self, union_eq_self_of_subset_left h])
@[simp]
theorem sumDiffSubset_apply_inl {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl
@[simp]
theorem sumDiffSubset_apply_inr {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    (x : (t \ s : Set α)) : Equiv.Set.sumDiffSubset h (Sum.inr x) = inclusion diff_subset x :=
  rfl
theorem sumDiffSubset_symm_apply_of_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∈ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inl, Set.inclusion_mk]
theorem sumDiffSubset_symm_apply_of_not_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)]
    {x : t} (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ := by
  apply (Equiv.Set.sumDiffSubset h).injective
  simp only [apply_symm_apply, sumDiffSubset_apply_inr, Set.inclusion_mk]
protected def unionSumInter {α : Type u} (s t : Set α) [DecidablePred (· ∈ s)] :
    (s ∪ t : Set α) ⊕ (s ∩ t : Set α) ≃ s ⊕ t :=
  calc
    (s ∪ t : Set α) ⊕ (s ∩ t : Set α)
      ≃ (s ∪ t \ s : Set α) ⊕ (s ∩ t : Set α) := by rw [union_diff_self]
    _ ≃ (s ⊕ (t \ s : Set α)) ⊕ (s ∩ t : Set α) :=
      sumCongr (Set.union disjoint_sdiff_self_right) (Equiv.refl _)
    _ ≃ s ⊕ ((t \ s : Set α) ⊕ (s ∩ t : Set α)) := sumAssoc _ _ _
    _ ≃ s ⊕ (t \ s ∪ s ∩ t : Set α) :=
      sumCongr (Equiv.refl _)
        (by
          refine (Set.union' (· ∉ s) ?_ ?_).symm
          exacts [fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ s ⊕ t := by
      { rw [(_ : t \ s ∪ s ∩ t = t)]
        rw [union_comm, inter_comm, inter_union_diff] }
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] (e₀ : s ≃ t) :
    { e : α ≃ β // ∀ x : s, e x = e₀ x } ≃ ((sᶜ : Set α) ≃ (tᶜ : Set β)) where
  toFun e :=
    subtypeEquiv e fun _ =>
      not_congr <|
        Iff.symm <|
          MapsTo.mem_iff (mapsTo_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
            (SurjOn.mapsTo_compl
              (surjOn_iff_exists_map_subtype.2 ⟨t, e₀, Subset.refl t, e₀.surjective, e.2⟩)
              e.1.injective)
  invFun e₁ :=
    Subtype.mk
      (calc
        α ≃ s ⊕ (sᶜ : Set α) := (Set.sumCompl s).symm
        _ ≃ t ⊕ (tᶜ : Set β) := e₀.sumCongr e₁
        _ ≃ β := Set.sumCompl t
        )
      fun x => by
      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
        Set.sumCompl_symm_apply, Trans.trans]
  left_inv e := by
    ext x
    by_cases hx : x ∈ s
    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
        trans_apply, Subtype.coe_mk, Set.sumCompl_apply_inl, Trans.trans]
    · simp only [Set.sumCompl_symm_apply_of_not_mem hx, Sum.map_inr, subtypeEquiv_apply,
        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Subtype.coe_mk, Trans.trans]
  right_inv e :=
    Equiv.ext fun x => by
      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
        sumCongr_apply, Equiv.coe_trans, Subtype.coe_eta, Subtype.coe_mk, Trans.trans,
        Set.sumCompl_symm_apply_compl]
protected def prod {α β} (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ s × t :=
  @subtypeProdEquivProd α β s t
@[simps]
protected def univPi {α : Type*} {β : α → Type*} (s : ∀ a, Set (β a)) :
    pi univ s ≃ ∀ a, s a where
  toFun f a := ⟨(f : ∀ a, β a) a, f.2 a (mem_univ a)⟩
  invFun f := ⟨fun a => f a, fun a _ => (f a).2⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext a
    rfl
  right_inv f := by
    ext a
    rfl
protected noncomputable def imageOfInjOn {α β} (f : α → β) (s : Set α) (H : InjOn f s) :
    s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p =>
    ⟨Classical.choose p.2, (Classical.choose_spec p.2).1⟩, fun ⟨_, h⟩ =>
    Subtype.eq
      (H (Classical.choose_spec (mem_image_of_mem f h)).1 h
        (Classical.choose_spec (mem_image_of_mem f h)).2),
    fun ⟨_, h⟩ => Subtype.eq (Classical.choose_spec h).2⟩
@[simps! apply]
protected noncomputable def image {α β} (f : α → β) (s : Set α) (H : Injective f) : s ≃ f '' s :=
  Equiv.Set.imageOfInjOn f s H.injOn
@[simp]
protected theorem image_symm_apply {α β} (f : α → β) (s : Set α) (H : Injective f) (x : α)
    (h : f x ∈ f '' s) : (Set.image f s H).symm ⟨f x, h⟩ = ⟨x, H.mem_set_image.1 h⟩ :=
  (Equiv.symm_apply_eq _).2 rfl
theorem image_symm_preimage {α β} {f : α → β} (hf : Injective f) (u s : Set α) :
    (fun x => (Set.image f s hf).symm x : f '' s → α) ⁻¹' u = Subtype.val ⁻¹' (f '' u) := by
  ext ⟨b, a, has, rfl⟩
  simp [hf.eq_iff]
@[simps]
protected def congr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩
protected def sep {α : Type u} (s : Set α) (t : α → Prop) :
    ({ x ∈ s | t x } : Set α) ≃ { x : s | t x } :=
  (Equiv.subtypeSubtypeEquivSubtypeInter s t).symm
protected def powerset {α} (S : Set α) :
    𝒫 S ≃ Set S where
  toFun := fun x : 𝒫 S => Subtype.val ⁻¹' (x : Set α)
  invFun := fun x : Set S => ⟨Subtype.val '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩
  left_inv x := by ext y;exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩
  right_inv x := by ext; simp
@[simps]
noncomputable def rangeSplittingImageEquiv {α β : Type*} (f : α → β) (s : Set (range f)) :
    rangeSplitting f '' s ≃ s where
  toFun x :=
    ⟨⟨f x, by simp⟩, by
      rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
      simpa [apply_rangeSplitting f] using m⟩
  invFun x := ⟨rangeSplitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩
  left_inv x := by
    rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
    simp [apply_rangeSplitting f]
  right_inv x := by simp [apply_rangeSplitting f]
@[simps symm_apply_coe]
def rangeInl (α β : Type*) : Set.range (Sum.inl : α → α ⊕ β) ≃ α where
  toFun
  | ⟨.inl x, _⟩ => x
  | ⟨.inr _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  invFun x := ⟨.inl x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv _ := rfl
@[simp] lemma rangeInl_apply_inl {α : Type*} (β : Type*) (x : α) :
    (rangeInl α β) ⟨.inl x, mem_range_self _⟩ = x :=
  rfl
@[simps symm_apply_coe]
def rangeInr (α β : Type*) : Set.range (Sum.inr : β → α ⊕ β) ≃ β where
  toFun
  | ⟨.inl _, h⟩ => False.elim <| by rcases h with ⟨x, h'⟩; cases h'
  | ⟨.inr x, _⟩ => x
  invFun x := ⟨.inr x, mem_range_self _⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv _ := rfl
@[simp] lemma rangeInr_apply_inr (α : Type*) {β : Type*} (x : β) :
    (rangeInr α β) ⟨.inr x, mem_range_self _⟩ = x :=
  rfl
end Set
@[simps]
def ofLeftInverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    α ≃ range f where
  toFun a := ⟨f a, a, rfl⟩
  invFun b := f_inv (nonempty_of_exists b.2) b
  left_inv a := hf ⟨a⟩ a
  right_inv := fun ⟨b, a, ha⟩ =>
    Subtype.eq <| show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha
abbrev ofLeftInverse' {α β : Sort _} (f : α → β) (f_inv : β → α) (hf : LeftInverse f_inv f) :
    α ≃ range f :=
  ofLeftInverse f (fun _ => f_inv) fun _ => hf
@[simps! apply]
noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
  Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf
theorem apply_ofInjective_symm {α β} {f : α → β} (hf : Injective f) (b : range f) :
    f ((ofInjective f hf).symm b) = b :=
  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b
@[simp]
theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
  apply (ofInjective f hf).injective
  simp [apply_ofInjective_symm hf]
theorem coe_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    ((ofInjective f hf).symm : range f → α) = rangeSplitting f := by
  ext ⟨y, x, rfl⟩
  apply hf
  simp [apply_rangeSplitting f]
@[simp]
theorem self_comp_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
    f ∘ (ofInjective f hf).symm = Subtype.val :=
  funext fun x => apply_ofInjective_symm hf x
theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : Nonempty α → β → α)
    (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
    ofLeftInverse f f_inv hf =
      ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subsingleton.elim _ _)
        (fun h => (hf h).injective)) := by
  ext
  simp
theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : β → α)
    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
  ext
  simp
protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (e ⁻¹' a) :=
  e.injective.preimage_surjective.forall
theorem preimage_piEquivPiSubtypeProd_symm_pi {α : Type*} {β : α → Type*} (p : α → Prop)
    [DecidablePred p] (s : ∀ i, Set (β i)) :
    (piEquivPiSubtypeProd p β).symm ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i := by
  ext ⟨f, g⟩
  simp only [mem_preimage, mem_univ_pi, prod_mk_mem_set_prod_eq, Subtype.forall, ← forall_and]
  refine forall_congr' fun i => ?_
  dsimp only [Subtype.coe_mk]
  by_cases hi : p i <;> simp [hi]
@[simps!]
def sigmaPreimageEquiv {α β} (f : α → β) : (Σb, f ⁻¹' {b}) ≃ α :=
  sigmaFiberEquiv f
@[simps!]
def ofPreimageEquiv {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c}) : α ≃ β :=
  Equiv.ofFiberEquiv e
theorem ofPreimageEquiv_map {α β γ} {f : α → γ} {g : β → γ} (e : ∀ c, f ⁻¹' {c} ≃ g ⁻¹' {c})
    (a : α) : g (ofPreimageEquiv e a) = f a :=
  Equiv.ofFiberEquiv_map e a
end Equiv
noncomputable def Set.BijOn.equiv {α : Type*} {β : Type*} {s : Set α} {t : Set β} (f : α → β)
    (h : BijOn f s t) : s ≃ t :=
  Equiv.ofBijective _ h.bijective
theorem dite_comp_equiv_update {α : Type*} {β : Sort*} {γ : Sort*} {p : α → Prop}
    (e : β ≃ Subtype p)
    (v : β → γ) (w : α → γ) (j : β) (x : γ) [DecidableEq β] [DecidableEq α]
    [∀ j, Decidable (p j)] :
    (fun i : α => if h : p i then (Function.update v j x) (e.symm ⟨i, h⟩) else w i) =
      Function.update (fun i : α => if h : p i then v (e.symm ⟨i, h⟩) else w i) (e j) x := by
  ext i
  by_cases h : p i
  · rw [dif_pos h, Function.update_apply_equiv_apply, Equiv.symm_symm,
      Function.update_apply, Function.update_apply, dif_pos h]
    have h_coe : (⟨i, h⟩ : Subtype p) = e j ↔ i = e j :=
      Subtype.ext_iff.trans (by rw [Subtype.coe_mk])
    simp [h_coe]
  · have : i ≠ e j := by
      contrapose! h
      have : p (e j : α) := (e j).2
      rwa [← h] at this
    simp [h, this]
section Swap
variable {α : Type*} [DecidableEq α] {a b : α} {s : Set α}
theorem Equiv.swap_bijOn_self (hs : a ∈ s ↔ b ∈ s) : BijOn (Equiv.swap a b) s s := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a
    · rwa [swap_apply_left, ← hs]
    obtain (rfl | hxb) := eq_or_ne x b
    · rwa [swap_apply_right, hs]
    rwa [swap_apply_of_ne_of_ne hxa hxb]
  obtain (rfl | hxa) := eq_or_ne x a
  · simp [hs.1 hx]
  obtain (rfl | hxb) := eq_or_ne x b
  · simp [hs.2 hx]
  exact ⟨x, hx, swap_apply_of_ne_of_ne hxa hxb⟩
theorem Equiv.swap_bijOn_exchange (ha : a ∈ s) (hb : b ∉ s) :
    BijOn (Equiv.swap a b) s (insert b (s \ {a})) := by
  refine ⟨fun x hx ↦ ?_, (Equiv.injective _).injOn, fun x hx ↦ ?_⟩
  · obtain (rfl | hxa) := eq_or_ne x a
    · simp [swap_apply_left]
    rw [swap_apply_of_ne_of_ne hxa (by rintro rfl; contradiction)]
    exact .inr ⟨hx, hxa⟩
  obtain (rfl | hxb) := eq_or_ne x b
  · exact ⟨a, ha, by simp⟩
  simp only [mem_insert_iff, mem_diff, mem_singleton_iff, or_iff_right hxb] at hx
  exact ⟨x, hx.1, swap_apply_of_ne_of_ne hx.2 hxb⟩
end Swap