import Mathlib.Logic.Relation
import Mathlib.Order.GaloisConnection
attribute [refl] Setoid.refl
attribute [symm] Setoid.symm
attribute [trans] Setoid.trans
variable {α : Type*} {β : Type*}
@[deprecated "No deprecation message was provided."  (since := "2024-08-29")]
def Setoid.Rel (r : Setoid α) : α → α → Prop :=
  @Setoid.r _ r
set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-10-09")]
instance Setoid.decidableRel (r : Setoid α) [h : DecidableRel r.r] : DecidableRel r.Rel :=
  h
set_option linter.deprecated false in
@[deprecated Quotient.eq' (since := "2024-10-09")]
theorem Quotient.eq_rel {r : Setoid α} {x y} :
    (Quotient.mk' x : Quotient r) = Quotient.mk' y ↔ r.Rel x y :=
  Quotient.eq
namespace Setoid
attribute [ext] ext
set_option linter.deprecated false in
@[deprecated Setoid.ext (since := "2024-10-09")]
theorem ext' {r s : Setoid α} (H : ∀ a b, r.Rel a b ↔ s.Rel a b) : r = s :=
  ext H
set_option linter.deprecated false in
@[deprecated Setoid.ext_iff (since := "2024-10-09")]
theorem ext'_iff {r s : Setoid α} : r = s ↔ ∀ a b, r.Rel a b ↔ s.Rel a b :=
  ⟨fun h _ _ => h ▸ Iff.rfl, ext'⟩
theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ ⇑r₁ = ⇑r₂ :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩
instance : LE (Setoid α) :=
  ⟨fun r s => ∀ ⦃x y⦄, r x y → s x y⟩
theorem le_def {r s : Setoid α} : r ≤ s ↔ ∀ {x y}, r x y → s x y :=
  Iff.rfl
@[refl]
theorem refl' (r : Setoid α) (x) : r x x := r.iseqv.refl x
@[symm]
theorem symm' (r : Setoid α) : ∀ {x y}, r x y → r y x := r.iseqv.symm
@[trans]
theorem trans' (r : Setoid α) : ∀ {x y z}, r x y → r y z → r x z := r.iseqv.trans
theorem comm' (s : Setoid α) {x y} : s x y ↔ s y x :=
  ⟨s.symm', s.symm'⟩
def ker (f : α → β) : Setoid α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩
@[simp]
theorem ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r :=
  ext fun _ _ => Quotient.eq
theorem ker_apply_mk_out {f : α → β} (a : α) : f (⟦a⟧ : Quotient (Setoid.ker f)).out = f a :=
  @Quotient.mk_out _ (Setoid.ker f) a
set_option linter.deprecated false in
@[deprecated ker_apply_mk_out (since := "2024-10-19")]
theorem ker_apply_mk_out' {f : α → β} (a : α) :
    f (Quotient.mk _ a : Quotient <| Setoid.ker f).out' = f a :=
  @Quotient.mk_out' _ (Setoid.ker f) a
theorem ker_def {f : α → β} {x y : α} : ker f x y ↔ f x = f y :=
  Iff.rfl
protected def prod (r : Setoid α) (s : Setoid β) :
    Setoid (α × β) where
  r x y := r x.1 y.1 ∧ s x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩
lemma prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β} :
    @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ @Setoid.r _ s y₁ y₂) :=
  Iff.rfl
lemma piSetoid_apply {ι : Sort*} {α : ι → Sort*} {r : ∀ i, Setoid (α i)} {x y : ∀ i, α i} :
    @Setoid.r _ (@piSetoid _ _ r) x y ↔ ∀ i, @Setoid.r _ (r i) (x i) (y i) :=
  Iff.rfl
@[simps]
def prodQuotientEquiv (r : Setoid α) (s : Setoid β) :
    Quotient r × Quotient s ≃ Quotient (r.prod s) where
  toFun := fun (x, y) ↦ Quotient.map₂ Prod.mk (fun _ _ hx _ _ hy ↦ ⟨hx, hy⟩) x y
  invFun := fun q ↦ Quotient.liftOn' q (fun xy ↦ (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy ↦ Prod.ext (by simpa using hxy.1) (by simpa using hxy.2)
  left_inv := fun q ↦ by
    rcases q with ⟨qa, qb⟩
    exact Quotient.inductionOn₂' qa qb fun _ _ ↦ rfl
  right_inv := fun q ↦ by
    simp only
    refine Quotient.inductionOn' q fun _ ↦ rfl
@[simps]
noncomputable def piQuotientEquiv {ι : Sort*} {α : ι → Sort*} (r : ∀ i, Setoid (α i)) :
    (∀ i, Quotient (r i)) ≃ Quotient (@piSetoid _ _ r) where
  toFun := fun x ↦ Quotient.mk'' fun i ↦ (x i).out
  invFun := fun q ↦ Quotient.liftOn' q (fun x i ↦ Quotient.mk'' (x i)) fun x y hxy ↦ by
    ext i
    simpa using hxy i
  left_inv := fun q ↦ by
    ext i
    simp
  right_inv := fun q ↦ by
    refine Quotient.inductionOn' q fun _ ↦ ?_
    simp only [Quotient.liftOn'_mk'', Quotient.eq'']
    intro i
    change Setoid.r _ _
    rw [← Quotient.eq'']
    simp
instance : Min (Setoid α) :=
  ⟨fun r s =>
    ⟨fun x y => r x y ∧ s x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩
theorem inf_def {r s : Setoid α} : ⇑(r ⊓ s) = ⇑r ⊓ ⇑s :=
  rfl
theorem inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s) x y ↔ r x y ∧ s x y :=
  Iff.rfl
instance : InfSet (Setoid α) :=
  ⟨fun S =>
    { r := fun x y => ∀ r ∈ S, r x y
      iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' <| h r hr, fun h1 h2 r hr =>
        r.trans' (h1 r hr) <| h2 r hr⟩ }⟩
theorem sInf_def {s : Set (Setoid α)} : ⇑(sInf s) = sInf ((⇑) '' s) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl
instance : PartialOrder (Setoid α) where
  le := (· ≤ ·)
  lt r s := r ≤ s ∧ ¬s ≤ r
  le_refl _ _ _ := id
  le_trans _ _ _ hr hs _ _ h := hs <| hr h
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩
instance completeLattice : CompleteLattice (Setoid α) :=
  { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Min.min
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨fun _ => trivial, fun h => h, fun h1 _ => h1⟩⟩
    le_top := fun _ _ _ _ => trivial
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    bot_le := fun r x _ h => h ▸ r.2.1 x }
@[simp]
theorem top_def : ⇑(⊤ : Setoid α) = ⊤ :=
  rfl
@[simp]
theorem bot_def : ⇑(⊥ : Setoid α) = (· = ·) :=
  rfl
theorem eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ ∀ x y : α, s x y := by
  rw [_root_.eq_top_iff, Setoid.le_def, Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]
lemma sInf_equiv {S : Set (Setoid α)} {x y : α} :
    letI := sInf S
    x ≈ y ↔ ∀ s ∈ S, s x y := Iff.rfl
lemma sInf_iff {S : Set (Setoid α)} {x y : α} :
    sInf S x y ↔ ∀ s ∈ S, s x y := Iff.rfl
lemma quotient_mk_sInf_eq {S : Set (Setoid α)} {x y : α} :
    Quotient.mk (sInf S) x = Quotient.mk (sInf S) y ↔ ∀ s ∈ S, s x y := by
  simp [sInf_iff]
def map_of_le {s t : Setoid α} (h : s ≤ t) : Quotient s → Quotient t :=
  Quotient.map' id h
def map_sInf {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) :
    Quotient (sInf S) → Quotient s :=
  Setoid.map_of_le fun _ _ a ↦ a s h
section EqvGen
open Relation
theorem eqvGen_eq (r : α → α → Prop) :
    EqvGen.setoid r = sInf { s : Setoid α | ∀ ⦃x y⦄, r x y → s x y } :=
  le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)
theorem sup_eq_eqvGen (r s : Setoid α) :
    r ⊔ s = EqvGen.setoid fun x y => r x y ∨ s x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]
theorem sup_def {r s : Setoid α} : r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s) := by
  rw [sup_eq_eqvGen]; rfl
theorem sSup_eq_eqvGen (S : Set (Setoid α)) :
    sSup S = EqvGen.setoid fun x y => ∃ r : Setoid α, r ∈ S ∧ r x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩
theorem sSup_def {s : Set (Setoid α)} : sSup s = EqvGen.setoid (sSup ((⇑) '' s)) := by
  rw [sSup_eq_eqvGen, sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]
@[simp]
theorem eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid r.r = r :=
  le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel
theorem eqvGen_idem (r : α → α → Prop) : EqvGen.setoid (EqvGen.setoid r) = EqvGen.setoid r :=
  eqvGen_of_setoid _
theorem eqvGen_le {r : α → α → Prop} {s : Setoid α} (h : ∀ x y, r x y → s x y) :
    EqvGen.setoid r ≤ s := by rw [eqvGen_eq]; exact sInf_le h
theorem eqvGen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) :
    EqvGen.setoid r ≤ EqvGen.setoid s :=
  eqvGen_le fun _ _ hr => EqvGen.rel _ _ <| h _ _ hr
def gi : @GaloisInsertion (α → α → Prop) (Setoid α) _ _ EqvGen.setoid (⇑) where
  choice r _ := EqvGen.setoid r
  gc _ s := ⟨fun H _ _ h => H <| EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl
end EqvGen
open Function
theorem injective_iff_ker_bot (f : α → β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoid α) _ _ (ker f)).symm
theorem ker_iff_mem_preimage {f : α → β} {x y} : ker f x y ↔ x ∈ f ⁻¹' {f y} :=
  Iff.rfl
def liftEquiv (r : Setoid α) : { f : α → β // r ≤ ker f } ≃ (Quotient r → β) where
  toFun f := Quotient.lift (f : α → β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  left_inv := fun ⟨_, _⟩ => Subtype.eq <| funext fun _ => rfl
  right_inv _ := funext fun x => Quotient.inductionOn' x fun _ => rfl
theorem lift_unique {r : Setoid α} {f : α → β} (H : r ≤ ker f) (g : Quotient r → β)
    (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g := by
  ext ⟨x⟩
  erw [Quotient.lift_mk f H, Hg]
  rfl
theorem ker_lift_injective (f : α → β) : Injective (@Quotient.lift _ _ (ker f) f fun _ _ h => h) :=
  fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h
theorem ker_eq_lift_of_injective {r : Setoid α} (f : α → β) (H : ∀ x y, r x y → f x = f y)
    (h : Injective (Quotient.lift f H)) : ker f = r :=
  le_antisymm
    (fun x y hk =>
      Quotient.exact <| h <| show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H
variable (r : Setoid α) (f : α → β)
noncomputable def quotientKerEquivRange : Quotient (ker f) ≃ Set.range f :=
  Equiv.ofBijective
    ((@Quotient.lift _ (Set.range f) (ker f) fun x => ⟨f x, Set.mem_range_self x⟩) fun _ _ h =>
      Subtype.ext_val h)
    ⟨fun x y h => ker_lift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
      fun ⟨_, z, hz⟩ =>
      ⟨@Quotient.mk'' _ (ker f) z, Subtype.ext_iff_val.2 hz⟩⟩
@[simps]
def quotientKerEquivOfRightInverse (g : β → α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β where
  toFun a := (Quotient.liftOn' a f) fun _ _ => id
  invFun b := Quotient.mk'' (g b)
  left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' <| hf (f a)
  right_inv := hf
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)
variable {r f}
def map (r : Setoid α) (f : α → β) : Setoid β :=
  Relation.EqvGen.setoid fun x y => ∃ a b, f a = x ∧ f b = y ∧ r a b
def mapOfSurjective (r) (f : α → β) (h : ker f ≤ r) (hf : Surjective f) : Setoid β :=
  ⟨fun x y => ∃ a b, f a = x ∧ f b = y ∧ r a b,
    ⟨fun x =>
      let ⟨y, hy⟩ := hf x
      ⟨y, y, hy, hy, r.refl' y⟩,
      fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, r.symm' h⟩,
      fun ⟨x, y, hx, hy, h₁⟩ ⟨y', z, hy', hz, h₂⟩ =>
      ⟨x, z, hx, hz, r.trans' h₁ <| r.trans' (h <| by rwa [← hy'] at hy) h₂⟩⟩⟩
theorem mapOfSurjective_eq_map (h : ker f ≤ r) (hf : Surjective f) :
    map r f = mapOfSurjective r f h hf := by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl
abbrev comap (f : α → β) (r : Setoid β) : Setoid α :=
  ⟨r on f, r.iseqv.comap _⟩
theorem comap_rel (f : α → β) (r : Setoid β) (x y : α) : comap f r x y ↔ r (f x) (f y) :=
  Iff.rfl
theorem comap_eq {f : α → β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r ∘ f) :=
  ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl
noncomputable def comapQuotientEquiv (f : α → β) (r : Setoid β) :
    Quotient (comap f r) ≃ Set.range (@Quotient.mk'' _ r ∘ f) :=
  (Quotient.congrRight <| Setoid.ext_iff.1 comap_eq).trans <| quotientKerEquivRange <|
    Quotient.mk'' ∘ f
variable (r f)
def quotientQuotientEquivQuotient (s : Setoid α) (h : r ≤ s) :
    Quotient (ker (Quot.mapRight h)) ≃ Quotient s where
  toFun x :=
    (Quotient.liftOn' x fun w =>
        (Quotient.liftOn' w (@Quotient.mk'' _ s)) fun _ _ H => Quotient.sound <| h H)
      fun x y => Quotient.inductionOn₂' x y fun _ _ H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Quotient.mk'' _ r w)
      fun _ _ H => Quotient.sound' <| show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotient.sound H
  left_inv x :=
    Quotient.inductionOn' x fun y => Quotient.inductionOn' y fun w => by show ⟦_⟧ = _; rfl
  right_inv x := Quotient.inductionOn' x fun y => by show ⟦_⟧ = _; rfl
variable {r f}
open Quotient
def correspondence (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r) where
  toFun s := ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ ↦ Eq.propIntro
      (fun h ↦ s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h ↦ s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, @fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ s.1.2.2,
      @fun x y z ↦ Quotient.inductionOn₃ x y z fun _ _ _ ↦ s.1.2.3⟩⟩
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, Quotient.eq'.2 h]⟩
  left_inv _ := rfl
  right_inv _ := ext fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ Iff.rfl
  map_rel_iff' :=
    ⟨fun h x y hs ↦ @h ⟦x⟧ ⟦y⟧ hs, fun h x y ↦ Quotient.inductionOn₂ x y fun _ _ hs ↦ h hs⟩
def sigmaQuotientEquivOfLe {r s : Setoid α} (hle : r ≤ s) :
    (Σ q : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α))) ≃
      Quotient r :=
  .trans (.symm <| .sigmaCongrRight fun _ ↦ .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ _ (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl)
    (.sigmaFiberEquiv fun a ↦ a.lift (Quotient.mk s) fun _ _ h ↦ Quotient.sound <| hle h)
end Setoid
@[simp]
theorem Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s = ⊤ := by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply,
    forall_const]
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq']
theorem Quot.subsingleton_iff (r : α → α → Prop) :
    Subsingleton (Quot r) ↔ Relation.EqvGen r = ⊤ := by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply, forall_const]
  refine Quot.mk_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quot.mk_surjective.forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp only [forall_const, le_Prop_eq, Pi.top_apply, Prop.top_eq_true, true_implies]