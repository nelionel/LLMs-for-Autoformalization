import Mathlib.Data.Part
import Mathlib.Data.Rel
import Batteries.WF
open Function
def PFun (α β : Type*) :=
  α → Part β
infixr:25 " →. " => PFun
namespace PFun
variable {α β γ δ ε ι : Type*}
instance inhabited : Inhabited (α →. β) :=
  ⟨fun _ => Part.none⟩
def Dom (f : α →. β) : Set α :=
  { a | (f a).Dom }
@[simp]
theorem mem_dom (f : α →. β) (x : α) : x ∈ Dom f ↔ ∃ y, y ∈ f x := by simp [Dom, Part.dom_iff_mem]
@[simp]
theorem dom_mk (p : α → Prop) (f : ∀ a, p a → β) : (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl
theorem dom_eq (f : α →. β) : Dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)
def fn (f : α →. β) (a : α) : Dom f a → β :=
  (f a).get
@[simp]
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)
theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2
def equivSubtype : (α →. β) ≃ Σp : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun _ =>
    funext fun _ => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr⟩
theorem asSubtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy
@[coe]
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)
instance coe : Coe (α → β) (α →. β) :=
  ⟨PFun.lift⟩
@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl
@[simp]
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.univ :=
  rfl
theorem lift_injective : Injective (PFun.lift : (α → β) → α →. β) := fun _ _ h =>
  funext fun a => Part.some_injective <| congr_fun h a
def graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }
def graph' (f : α →. β) : Rel α β := fun x y => y ∈ f x
def ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
  (f x).restrict (x ∈ p) (@H x)
@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) :
    b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a := by simp [restrict]
def res (f : α → β) (s : Set α) : α →. β :=
  (PFun.lift f).restrict s.subset_univ
theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [res, @eq_comm _ b]
theorem res_univ (f : α → β) : PFun.res f Set.univ = f :=
  rfl
theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem
theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
  show (∃ _ : True, f a = b) ↔ f a = b by simp
protected def pure (x : β) : α →. β := fun _ => Part.some x
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a
@[simp]
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f
instance monad : Monad (PFun α) where
  pure := PFun.pure
  bind := PFun.bind
  map := PFun.map
instance lawfulMonad : LawfulMonad (PFun α) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => funext fun _ => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
  (pure_bind := fun x f => funext fun _ => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)
theorem pure_defined (p : Set α) (x : β) : p ⊆ (@PFun.pure α _ x).Dom :=
  p.subset_univ
theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom)
    (H2 : ∀ x, p ⊆ (g x).Dom) : p ⊆ (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)
def fix (f : α →. β ⊕ α) : α →. β := fun a =>
  Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a) fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h
theorem dom_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixFEq] at h₂; exact h₂.fst.fst
theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixFEq] at h₂
    simp only [Part.mem_assert_iff] at h₂
    cases' h₂ with h₂ h₃
    split at h₃
    next e => simp only [Part.mem_some_iff] at h₃; subst b; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    simp only [fix, Part.mem_assert_iff]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixFEq]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp only [fix, Part.mem_assert_iff] at h₃
      cases' h₃ with h₃ h₄
      refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · cases' h with h₁ h₂
        rw [WellFounded.fixFEq]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e
        next e =>
          injection h₂.symm.trans e; subst a'; exact h₄⟩
theorem fix_stop {f : α →. β ⊕ α} {b : β} {a : α} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a := by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb
theorem fix_fwd_eq {f : α →. β ⊕ α} {a a' : α} (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' := by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    exact Or.inr ⟨a', ha', h⟩
theorem fix_fwd {f : α →. β ⊕ α} {b : β} {a a' : α} (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) :
    b ∈ f.fix a' := by rwa [← fix_fwd_eq ha']
@[elab_as_elim]
def fixInduction {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a := by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  generalize_proofs at h₂
  clear h
  induction ‹Acc _ _› with | intro a ha IH => _
  have h : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd
theorem fixInduction_spec {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun _ h' => fixInduction (fix_fwd h h') H := by
  unfold fixInduction
  generalize_proofs
  induction ‹Acc _ _›
  rfl
@[elab_as_elim]
def fixInduction' {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α}
    (h : b ∈ f.fix a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a := by
  refine fixInduction h fun a' h ih => ?_
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  · apply hbase
    convert e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)
theorem fixInduction'_stop {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (fa : Sum.inl b ∈ f a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa := by
  unfold fixInduction'
  rw [fixInduction_spec]
  refine Eq.rec (motive := fun x e ↦
      Sum.casesOn x ?_ ?_ (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
theorem fixInduction'_fwd {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a a' : α} (h : b ∈ f.fix a)
    (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) := by
  unfold fixInduction'
  rw [fixInduction_spec]
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y → C a) x ?_ ?_
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
variable (f : α →. β)
def image (s : Set α) : Set β :=
  f.graph'.image s
theorem image_def (s : Set α) : f.image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl
theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl
theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  Rel.image_mono _ h
theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  Rel.image_inter _ s t
theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  Rel.image_union _ s t
def preimage (s : Set β) : Set α :=
  Rel.image (fun x y => x ∈ f y) s
theorem Preimage_def (s : Set β) : f.preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl
@[simp]
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl
theorem preimage_subset_dom (s : Set β) : f.preimage s ⊆ f.Dom := fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
  Rel.preimage_mono _ h
theorem preimage_inter (s t : Set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
  Rel.preimage_inter _ s t
theorem preimage_union (s t : Set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
  Rel.preimage_union _ s t
theorem preimage_univ : f.preimage Set.univ = f.Dom := by ext; simp [mem_preimage, mem_dom]
theorem coe_preimage (f : α → β) (s : Set β) : (f : α →. β).preimage s = f ⁻¹' s := by ext; simp
def core (s : Set β) : Set α :=
  f.graph'.core s
theorem core_def (s : Set β) : f.core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl
@[simp]
theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl
theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx
theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  Rel.core_mono _ h
theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  Rel.core_inter _ s t
theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) :
    x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t := by simp [mem_core, mem_res]
theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t := by
  ext x
  rw [mem_core_res]
  by_cases h : x ∈ s <;> simp [h]
theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).core s = s.preimage f := by
  ext x; simp [core_def]
theorem preimage_subset_core (f : α →. β) (s : Set β) : f.preimage s ⊆ f.core s :=
  fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys
theorem preimage_eq (f : α →. β) (s : Set β) : f.preimage s = f.core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore _ (Part.get_mem _)
    show x ∈ f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩
theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.inter_union_distrib_right, Set.union_comm (Dom f), Set.compl_union_self,
    Set.inter_univ, Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]
theorem preimage_asSubtype (f : α →. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.preimage s := by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩
@[simp]
theorem dom_toSubtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl
@[simp]
theorem toSubtype_apply (p : β → Prop) (f : α → β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl
theorem dom_toSubtype_apply_iff {p : β → Prop} {f : α → β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl
theorem mem_toSubtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} :
    b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [toSubtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]
protected def id (α : Type*) : α →. α :=
  Part.some
@[simp]
theorem coe_id (α : Type*) : ((id : α → α) : α →. α) = PFun.id α :=
  rfl
@[simp]
theorem id_apply (a : α) : PFun.id α a = Part.some a :=
  rfl
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
@[simp]
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl
@[simp]
theorem id_comp (f : α →. β) : (PFun.id β).comp f = f :=
  ext fun _ _ => by simp
@[simp]
theorem comp_id (f : α →. β) : f.comp (PFun.id α) = f :=
  ext fun _ _ => by simp
@[simp]
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.preimage f.Dom := by
  ext
  simp_rw [mem_preimage, mem_dom, comp_apply, Part.mem_bind_iff, ← exists_and_right]
  rw [exists_comm]
  simp_rw [and_comm]
@[simp]
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) :
    (f.comp g).preimage s = g.preimage (f.preimage s) := by
  ext
  simp_rw [mem_preimage, comp_apply, Part.mem_bind_iff, ← exists_and_right, ← exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc, and_comm]
@[simp]
theorem Part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by
  ext c
  simp_rw [Part.mem_bind_iff, comp_apply, Part.mem_bind_iff, ← exists_and_right, ← exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc]
@[simp]
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, Part.bind_comp]
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]
def prodLift (f : α →. β) (g : α →. γ) : α →. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩
@[simp]
theorem dom_prodLift (f : α →. β) (g : α →. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl
theorem get_prodLift (f : α →. β) (g : α →. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl
@[simp]
theorem prodLift_apply (f : α →. β) (g : α →. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl
theorem mem_prodLift {f : α →. β} {g : α →. γ} {x : α} {y : β × γ} :
    y ∈ f.prodLift g x ↔ y.1 ∈ f x ∧ y.2 ∈ g x := by
  trans ∃ hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]
def prodMap (f : α →. γ) (g : β →. δ) : α × β →. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩
@[simp]
theorem dom_prodMap (f : α →. γ) (g : β →. δ) :
    (f.prodMap g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl
theorem get_prodMap (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
    (f.prodMap g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl
@[simp]
theorem prodMap_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
    f.prodMap g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl
theorem mem_prodMap {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
    y ∈ f.prodMap g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 := by
  trans ∃ hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]
@[simp]
theorem prodLift_fst_comp_snd_comp (f : α →. γ) (g : β →. δ) :
    prodLift (f.comp ((Prod.fst : α × β → α) : α × β →. α))
        (g.comp ((Prod.snd : α × β → β) : α × β →. β)) =
      prodMap f g :=
  ext fun a => by simp
@[simp]
theorem prodMap_id_id : (PFun.id α).prodMap (PFun.id β) = PFun.id _ :=
  ext fun _ _ ↦ by simp [eq_comm]
@[simp]
theorem prodMap_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
    (f₂.comp f₁).prodMap (g₂.comp g₁) = (f₂.prodMap g₂).comp (f₁.prodMap g₁) := 
  ext <| fun ⟨_, _⟩ ⟨_, _⟩ ↦
  ⟨fun ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ ↦ ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   fun ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ ↦ ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩
end PFun