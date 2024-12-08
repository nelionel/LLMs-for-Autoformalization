import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Relation
universe v u
open CategoryTheory Limits
namespace CategoryTheory.Limits.Types
example : HasProducts.{v} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasProducts.{v} (Type u) := inferInstance
instance : HasProducts.{v} (Type v) := inferInstance
@[simp 1001]
theorem pi_lift_π_apply {β : Type v} [Small.{u} β] (f : β → Type u) {P : Type u}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_fun (limit.lift_π (Fan.mk P s) ⟨b⟩) x
theorem pi_lift_π_apply' {β : Type v} (f : β → Type v) {P : Type v}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x := by
  simp
@[simp 1001]
theorem pi_map_π_apply {β : Type v} [Small.{u} β] {f g : β → Type u}
    (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ᶜ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ᶜ f → f b) x) :=
  Limit.map_π_apply.{v, u} _ _ _
theorem pi_map_π_apply' {β : Type v} {f g : β → Type v} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ᶜ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ᶜ f → f b) x) := by
  simp
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) where
  cone :=
    { pt := PUnit
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun _ _ => PUnit.unit
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by
        funext
        subsingleton }
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  limit.isoLimitCone terminalLimitCone.{u, 0}
noncomputable def isTerminalPunit : IsTerminal (PUnit : Type u) :=
  terminalIsTerminal.ofIso terminalIso
noncomputable instance : Inhabited (⊤_ (Type u)) :=
  ⟨@terminal.from (Type u) _ _ (ULift (Fin 1)) (ULift.up 0)⟩
instance : Subsingleton (⊤_ (Type u)) := ⟨fun a b =>
  congr_fun (@Subsingleton.elim (_ ⟶ ⊤_ (Type u)) _
    (fun _ => a) (fun _ => b)) (ULift.up (0 : Fin 1))⟩
noncomputable instance : Unique (⊤_ (Type u)) := Unique.mk' _
noncomputable def isTerminalEquivUnique (X : Type u) : IsTerminal X ≃ Unique X :=
  equivOfSubsingletonOfSubsingleton
    (fun h => ((Iso.toEquiv (terminalIsoIsTerminal h).symm).unique))
    (fun _ => IsTerminal.ofIso terminalIsTerminal (Equiv.toIso (Equiv.equivOfUnique _ _)))
noncomputable def isTerminalEquivIsoPUnit (X : Type u) : IsTerminal X ≃ (X ≅ PUnit) := by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit.{u + 1}) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => by rintro ⟨⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by funext x; cases x }
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}
noncomputable def isInitialPunit : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso
lemma initial_iff_empty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
    exact ⟨IsInitial.ofIso Types.isInitialPunit <| Equiv.toIso <| Equiv.equivOfIsEmpty PEmpty X⟩
open CategoryTheory.Limits.WalkingPair
@[simps! pt]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk _root_.Prod.fst _root_.Prod.snd
@[simp]
theorem binaryProductCone_fst (X Y : Type u) : (binaryProductCone X Y).fst = _root_.Prod.fst :=
  rfl
@[simp]
theorem binaryProductCone_snd (X Y : Type u) : (binaryProductCone X Y).snd = _root_.Prod.snd :=
  rfl
@[simps]
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) x := (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Prod.ext (congr_fun (w ⟨left⟩) x) (congr_fun (w ⟨right⟩) x)
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)
@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.fst = _root_.Prod.fst :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.snd = _root_.Prod.snd :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
@[simps]
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj X :=
    { obj := fun Y => X × Y
      map := fun { _ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk _root_.Prod.fst (_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      (binaryProductLimit X₂ Y).lift (BinaryFan.mk (_root_.Prod.fst ≫ f) _root_.Prod.snd) }
noncomputable def binaryProductIsoProd : binaryProductFunctor ≅ (prod.functor : Type u ⥤ _) := by
  refine NatIso.ofComponents (fun X => ?_) (fun _ => ?_)
  · refine NatIso.ofComponents (fun Y => ?_) (fun _ => ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl
@[simps!]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr
@[simps]
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Sum.casesOn x (congr_fun (w ⟨left⟩)) (congr_fun (w ⟨right⟩))
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ X ⊕ Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)
@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾(Sum.inl : X ⟶ X ⊕ Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾(Sum.inr : Y ⟶ X ⊕ Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
open Function (Injective)
theorem binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g x
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        funext x
        dsimp
        simp [h₁.eq_iff]
      · intro T f g
        funext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply,
          dite_eq_right_iff, forall_exists_index]
        intro y e
        have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        funext x
        dsimp
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (Subtype.val : ↑(Set.range f)ᶜ → Y)) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val
def productLimitCone {J : Type v} (F : J → TypeMax.{v, u}) :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := ∀ j, F j
      π := Discrete.natTrans (fun ⟨j⟩ f => f j) }
  isLimit :=
    { lift := fun s x j => s.π.app ⟨j⟩ x
      uniq := fun _ _ w => funext fun x => funext fun j => (congr_fun (w ⟨j⟩) x : _) }
noncomputable def productIso {J : Type v} (F : J → TypeMax.{v, u}) : ∏ᶜ F ≅ ∀ j, F j :=
  limit.isoLimitCone (productLimitCone.{v, u} F)
@[simp]
theorem productIso_hom_comp_eval {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    ((productIso.{v, u} F).hom ≫ fun f => f j) = Pi.π F j :=
  rfl
@[simp]
theorem productIso_hom_comp_eval_apply {J : Type v} (F : J → TypeMax.{v, u}) (j : J) (x) :
    ((productIso.{v, u} F).hom x) j = Pi.π F j x :=
  rfl
@[elementwise (attr := simp)]
theorem productIso_inv_comp_π {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = fun f => f j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩
namespace Small
variable {J : Type v} (F : J → Type u) [Small.{u} J]
noncomputable def productLimitCone :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := Shrink (∀ j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ f => (equivShrink (∀ j, F j)).symm f j) }
  isLimit :=
    have : Small.{u} (∀ j, F j) := inferInstance
    { lift := fun s x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => funext fun x => Shrink.ext <| funext fun j => by
        simpa using (congr_fun (w ⟨j⟩) x : _) }
noncomputable def productIso :
    (∏ᶜ F : Type u) ≅ Shrink.{u} (∀ j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)
@[simp]
theorem productIso_hom_comp_eval (j : J) :
    ((productIso.{v, u} F).hom ≫ fun f => (equivShrink (∀ j, F j)).symm f j) = Pi.π F j :=
  limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩
@[simp]
theorem productIso_hom_comp_eval_apply (j : J) (x) :
    (equivShrink (∀ j, F j)).symm ((productIso F).hom x) j = Pi.π F j x :=
  congr_fun (productIso_hom_comp_eval F j) x
@[elementwise (attr := simp)]
theorem productIso_inv_comp_π (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = fun f => ((equivShrink (∀ j, F j)).symm f) j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩
end Small
def coproductColimitCocone {J : Type v} (F : J → TypeMax.{v, u}) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σj, F j
      ι := Discrete.natTrans (fun ⟨j⟩ x => ⟨j, x⟩)}
  isColimit :=
    { desc := fun s x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        funext ⟨j, x⟩
        exact congr_fun (w ⟨j⟩) x }
noncomputable def coproductIso {J : Type v} (F : J → TypeMax.{v, u}) : ∐ F ≅ Σj, F j :=
  colimit.isoColimitCocone (coproductColimitCocone F)
@[elementwise (attr := simp)]
theorem coproductIso_ι_comp_hom {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = fun x : F j => (⟨j, x⟩ : Σj, F j) :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩
theorem coproductIso_mk_comp_inv {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    (↾fun x : F j => (⟨j, x⟩ : Σj, F j)) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl
section Fork
variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_fun s.condition i
    · funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).1
    · intro m hm
      funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).2 _ (congr_fun hm i)
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_fun (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply Fork.IsLimit.hom_ext t
  funext ⟨⟩
  apply hx'.trans (congr_fun (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm
theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨fun i => ⟨s.ι i, by apply congr_fun s.condition i⟩, rfl, fun hm =>
        funext fun x => Subtype.ext (congr_fun hm x)⟩
variable (g h)
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit
@[simp]
theorem equalizerIso_hom_comp_subtype : (equalizerIso g h).hom ≫ Subtype.val = equalizer.ι g h := by
  rfl
@[elementwise (attr := simp)]
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero
end Fork
section Cofork
variable {X Y Z : Type u} (f g : X ⟶ Y)
inductive CoequalizerRel : Y → Y → Prop
  | Rel (x : X) : CoequalizerRel (f x) (g x)
def coequalizerColimit : Limits.ColimitCocone (parallelPair f g) where
  cocone :=
    Cofork.ofπ (Quot.mk (CoequalizerRel f g)) (funext fun x => Quot.sound (CoequalizerRel.Rel x))
  isColimit :=
    Cofork.IsColimit.mk _
      (fun s => Quot.lift s.π
        (fun a b (h : CoequalizerRel f g a b) => by
          cases h
          apply congr_fun s.condition))
      (fun _ => rfl)
      (fun _ _ hm => funext (fun x => Quot.inductionOn x (congr_fun hm)))
theorem coequalizer_preimage_image_eq_of_preimage_eq (π : Y ⟶ Z) (e : f ≫ π = g ≫ π)
    (h : IsColimit (Cofork.ofπ π e)) (U : Set Y) (H : f ⁻¹' U = g ⁻¹' U) : π ⁻¹' (π '' U) = U := by
  have lem : ∀ x y, CoequalizerRel f g x y → (x ∈ U ↔ y ∈ U) := by
    rintro _ _ ⟨x⟩
    change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U
    rw [H]
  have eqv : _root_.Equivalence fun x y => x ∈ U ↔ y ∈ U :=
    { refl := by tauto
      symm := by tauto
      trans := by tauto }
  ext
  constructor
  · rw [←
      show _ = π from
        h.comp_coconePointUniqueUpToIso_inv (coequalizerColimit f g).2
          WalkingParallelPair.one]
    rintro ⟨y, hy, e'⟩
    dsimp at e'
    replace e' :=
      (mono_iff_injective
            (h.coconePointUniqueUpToIso (coequalizerColimit f g).isColimit).inv).mp
        inferInstance e'
    exact (eqv.eqvGen_iff.mp (Relation.EqvGen.mono lem (Quot.eqvGen_exact e'))).mp hy
  · exact fun hx => ⟨_, hx, rfl⟩
noncomputable def coequalizerIso : coequalizer f g ≅ _root_.Quot (CoequalizerRel f g) :=
  colimit.isoColimitCocone (coequalizerColimit f g)
@[elementwise (attr := simp)]
theorem coequalizerIso_π_comp_hom :
    coequalizer.π f g ≫ (coequalizerIso f g).hom = Quot.mk (CoequalizerRel f g) :=
  colimit.isoColimitCocone_ι_hom (coequalizerColimit f g) WalkingParallelPair.one
@[simp]
theorem coequalizerIso_quot_comp_inv :
    ↾Quot.mk (CoequalizerRel f g) ≫ (coequalizerIso f g).inv = coequalizer.π f g :=
  rfl
end Cofork
section Pullback
instance : HasPullbacks.{u} (Type u) :=
  hasPullbacks_of_hasWidePullbacks.{u} (Type u)
instance : HasPushouts.{u} (Type u) :=
  hasPushouts_of_hasWidePushouts.{u} (Type u)
variable {X Y Z : Type u} {X' Y' Z' : Type v}
variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }
example (p : PullbackObj f g) : X × Y :=
  p
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_fun s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
      funext fun x =>
        Subtype.ext <|
          Prod.ext (congr_fun (w WalkingCospan.left) x) (congr_fun (w WalkingCospan.right) x)
end Pullback
end Types
section Pullback
variable {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : PullbackCone f g}
namespace PullbackCone
namespace IsLimit
variable (hc : IsLimit c)
noncomputable def equivPullbackObj : c.pt ≃ Types.PullbackObj f g :=
  (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv
@[simp]
lemma equivPullbackObj_apply_fst (x : c.pt) : (equivPullbackObj hc x).1.1 = c.fst x :=
  congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left) x
@[simp]
lemma equivPullbackObj_apply_snd (x : c.pt) : (equivPullbackObj hc x).1.2 = c.snd x :=
  congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right) x
@[simp]
lemma equivPullbackObj_symm_apply_fst (x : Types.PullbackObj f g) :
    c.fst ((equivPullbackObj hc).symm x) = x.1.1 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp
@[simp]
lemma equivPullbackObj_symm_apply_snd (x : Types.PullbackObj f g) :
    c.snd ((equivPullbackObj hc).symm x) = x.1.2 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp
include hc in
lemma type_ext {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y) : x = y :=
  (equivPullbackObj hc).injective (by ext <;> assumption)
end IsLimit
variable (c)
@[simps coe_fst coe_snd]
def toPullbackObj (x : c.pt) : Types.PullbackObj f g :=
  ⟨⟨c.fst x, c.snd x⟩, congr_fun c.condition x⟩
noncomputable def isLimitEquivBijective :
    IsLimit c ≃ Function.Bijective c.toPullbackObj where
  toFun h := (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl
end PullbackCone
end Pullback
namespace Types
section Pullback
open CategoryTheory.Limits.WalkingCospan
variable {W X Y Z : Type u}
variable (f : X ⟶ Z) (g : Y ⟶ Z)
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso
@[simp]
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p
@[simp]
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p
@[simp]
theorem pullbackIsoPullback_inv_fst_apply (x : (Types.pullbackCone f g).pt) :
    (pullback.fst f g) ((pullbackIsoPullback f g).inv x) = (fun p => (p.1 : X × Y).fst) x :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) x
@[simp]
theorem pullbackIsoPullback_inv_snd_apply (x : (Types.pullbackCone f g).pt) :
    (pullback.snd f g) ((pullbackIsoPullback f g).inv x) = (fun p => (p.1 : X × Y).snd) x :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) x
@[simp]
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst _ _ = fun p => (p.1 : X × Y).fst := by aesop
@[simp]
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd _ _ = fun p => (p.1 : X × Y).snd := by aesop
end Pullback
section Pushout
variable {S X₁ X₂ : Type u} (f : S ⟶ X₁) (g : S ⟶ X₂)
inductive Pushout.Rel (f : S ⟶ X₁) (g : S ⟶ X₂) : X₁ ⊕ X₂ → X₁ ⊕ X₂ → Prop
  | inl_inr (s : S) : Pushout.Rel f g (Sum.inl (f s)) (Sum.inr (g s))
def Pushout : Type u := _root_.Quot (Pushout.Rel f g)
inductive Pushout.Rel' : X₁ ⊕ X₂ → X₁ ⊕ X₂ → Prop
  | refl (x : X₁ ⊕ X₂) : Rel' x x
  | inl_inl (x₀ y₀ : S) (h : g x₀ = g y₀) : Rel' (Sum.inl (f x₀)) (Sum.inl (f y₀))
  | inl_inr (s : S) : Rel' (Sum.inl (f s)) (Sum.inr (g s))
  | inr_inl (s : S) : Rel' (Sum.inr (g s)) (Sum.inl (f s))
def Pushout' : Type u := _root_.Quot (Pushout.Rel' f g)
namespace Pushout
@[simp]
def inl : X₁ ⟶ Pushout f g := fun x => Quot.mk _ (Sum.inl x)
@[simp]
def inr : X₂ ⟶ Pushout f g := fun x => Quot.mk _ (Sum.inr x)
lemma condition : f ≫ inl f g = g ≫ inr f g := by
  ext x
  exact Quot.sound (Rel.inl_inr x)
@[simps!]
def cocone : PushoutCocone f g := PushoutCocone.mk _ _ (condition f g)
def isColimitCocone : IsColimit (cocone f g) :=
  PushoutCocone.IsColimit.mk _ (fun s => Quot.lift (fun x => match x with
      | Sum.inl x₁ => s.inl x₁
      | Sum.inr x₂ => s.inr x₂) (by
    rintro _ _ ⟨t⟩
    exact congr_fun s.condition t)) (fun _ => rfl) (fun _ => rfl) (fun s m h₁ h₂ => by
      ext ⟨x₁|x₂⟩
      · exact congr_fun h₁ x₁
      · exact congr_fun h₂ x₂)
@[simp]
lemma inl_rel'_inl_iff (x₁ y₁ : X₁) :
    Rel' f g (Sum.inl x₁) (Sum.inl y₁) ↔ x₁ = y₁ ∨
      ∃ (x₀ y₀ : S) (_ : g x₀ = g y₀), x₁ = f x₀ ∧ y₁ = f y₀ := by
  constructor
  · rintro (_|⟨_, _, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, h, rfl, rfl⟩
  · rintro (rfl | ⟨_,_ , h, rfl, rfl⟩)
    · apply Rel'.refl
    · exact Rel'.inl_inl _ _ h
@[simp]
lemma inl_rel'_inr_iff (x₁ : X₁) (x₂ : X₂) :
    Rel' f g (Sum.inl x₁) (Sum.inr x₂) ↔
      ∃ (s : S), x₁ = f s ∧ x₂ = g s := by
  constructor
  · rintro ⟨_⟩
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl⟩
    exact Rel'.inl_inr _
@[simp]
lemma inr_rel'_inr_iff (x₂ y₂ : X₂) :
    Rel' f g (Sum.inr x₂) (Sum.inr y₂) ↔ x₂ = y₂ := by
  constructor
  · rintro ⟨_⟩
    rfl
  · rintro rfl
    apply Rel'.refl
variable {f g}
lemma Rel'.symm {x y : X₁ ⊕ X₂} (h : Rel' f g x y) :
    Rel' f g y x := by
  obtain _|⟨_, _, h⟩|_|_ := h
  · apply Rel'.refl
  · exact Rel'.inl_inl _ _ h.symm
  · exact Rel'.inr_inl _
  · exact Rel'.inl_inr _
variable (f g)
lemma equivalence_rel' [Mono f] : _root_.Equivalence (Rel' f g) where
  refl := Rel'.refl
  symm h := h.symm
  trans := by
    rintro x y z (_|⟨_, _, h⟩|s|_) hyz
    · exact hyz
    · obtain z₁|z₂ := z
      · rw [inl_rel'_inl_iff] at hyz
        obtain rfl|⟨_, _, h', h'', rfl⟩ := hyz
        · exact Rel'.inl_inl _ _ h
        · obtain rfl := (mono_iff_injective f).1 inferInstance h''
          exact Rel'.inl_inl _ _ (h.trans h')
      · rw [inl_rel'_inr_iff] at hyz
        obtain ⟨s, hs, rfl⟩ := hyz
        obtain rfl := (mono_iff_injective f).1 inferInstance hs
        rw [← h]
        apply Rel'.inl_inr
    · obtain z₁|z₂ := z
      · replace hyz := hyz.symm
        rw [inl_rel'_inr_iff] at hyz
        obtain ⟨s', rfl, hs'⟩ := hyz
        exact Rel'.inl_inl _ _ hs'
      · rw [inr_rel'_inr_iff] at hyz
        subst hyz
        apply Rel'.inl_inr
    · obtain z₁|z₂ := z
      · rw [inl_rel'_inl_iff] at hyz
        obtain rfl|⟨_, _, h, h', rfl⟩  := hyz
        · apply Rel'.inr_inl
        · obtain rfl := (mono_iff_injective f).1 inferInstance h'
          rw [h]
          apply Rel'.inr_inl
      · rw [inl_rel'_inr_iff] at hyz
        obtain ⟨s, hs, rfl⟩ := hyz
        obtain rfl := (mono_iff_injective f).1 inferInstance hs
        apply Rel'.refl
def equivPushout' : Pushout f g ≃ Pushout' f g where
  toFun := Quot.lift (Quot.mk _) (by
    rintro _ _ ⟨⟩
    apply Quot.sound
    apply Rel'.inl_inr)
  invFun := Quot.lift (Quot.mk _) (by
    rintro a b (_|⟨x₀, y₀, h⟩|_|_)
    · rfl
    · have h₀ : Rel f g _ _ := Rel.inl_inr x₀
      rw [Quot.sound h₀, h]
      symm
      apply Quot.sound
      apply Rel.inl_inr
    · apply Quot.sound
      apply Rel.inl_inr
    · symm
      apply Quot.sound
      apply Rel.inl_inr)
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by rintro ⟨x⟩; rfl
lemma quot_mk_eq_iff [Mono f] (a b : X₁ ⊕ X₂) :
    (Quot.mk _ a : Pushout f g) = Quot.mk _ b ↔ Rel' f g a b := by
  rw [← (equivalence_rel' f g).quot_mk_eq_iff]
  exact ⟨fun h => (equivPushout' f g).symm.injective h,
    fun h => (equivPushout' f g).injective h⟩
lemma inl_eq_inr_iff [Mono f] (x₁ : X₁) (x₂ : X₂) :
    (inl f g x₁ = inr f g x₂) ↔
      ∃ (s : S), f s = x₁ ∧ g s = x₂ := by
  refine (Pushout.quot_mk_eq_iff f g (Sum.inl x₁) (Sum.inr x₂)).trans ?_
  constructor
  · rintro ⟨⟩
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl⟩
    apply Rel'.inl_inr
end Pushout
variable {f g}
lemma pushoutCocone_inl_eq_inr_imp_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ : X₁) (x₂ : X₂) (h : c.inl x₁ = c.inr x₂) :
    c'.inl x₁ = c'.inr x₂ := by
  convert congr_arg e.hom.hom h
  · exact congr_fun (e.hom.w WalkingSpan.left).symm x₁
  · exact congr_fun (e.hom.w WalkingSpan.right).symm x₂
lemma pushoutCocone_inl_eq_inr_iff_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ : X₁) (x₂ : X₂) :
    c.inl x₁ = c.inr x₂ ↔ c'.inl x₁ = c'.inr x₂ := by
  constructor
  · apply pushoutCocone_inl_eq_inr_imp_of_iso e
  · apply pushoutCocone_inl_eq_inr_imp_of_iso e.symm
lemma pushoutCocone_inl_eq_inr_iff_of_isColimit {c : PushoutCocone f g} (hc : IsColimit c)
    (h₁ : Function.Injective f) (x₁ : X₁) (x₂ : X₂) :
    c.inl x₁ = c.inr x₂ ↔ ∃ (s : S), f s = x₁ ∧ g s = x₂ := by
  rw [pushoutCocone_inl_eq_inr_iff_of_iso
    (Cocones.ext (IsColimit.coconePointUniqueUpToIso hc (Pushout.isColimitCocone f g))
    (by aesop_cat))]
  have := (mono_iff_injective f).2 h₁
  apply Pushout.inl_eq_inr_iff
end Pushout
end Types
section Multiequalizer
variable (I : MulticospanIndex (Type u))
@[ext]
structure MulticospanIndex.sections where
  val (i : I.L) : I.left i
  property (r : I.R) : I.fst r (val _) = I.snd r (val _)
@[simps]
def MulticospanIndex.sectionsEquiv :
    I.sections ≃ I.multicospan.sections where
  toFun s :=
    { val := fun i ↦ match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_|_|r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i ↦ s.val (.left i)
      property := fun r ↦ (s.property (.fst r)).trans (s.property (.snd r)).symm }
  left_inv _ := rfl
  right_inv s := by
    ext (_|r)
    · rfl
    · exact s.property (.fst r)
namespace Multifork
variable {I}
variable (c : Multifork I)
@[simps]
def toSections (x : c.pt) : I.sections where
  val i := c.ι i x
  property r := congr_fun (c.condition r) x
lemma toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections := rfl
lemma isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections := by
  rw [Types.isLimit_iff_bijective_sectionOfCone, ← toSections_fac, EquivLike.comp_bijective]
namespace IsLimit
variable {c}
variable (hc : IsLimit c)
noncomputable def sectionsEquiv : I.sections ≃ c.pt :=
  (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm
@[simp]
lemma sectionsEquiv_symm_apply_val (x : c.pt) (i : I.L) :
    ((sectionsEquiv hc).symm x).val i = c.ι i x := rfl
@[simp]
lemma sectionsEquiv_apply_val (s : I.sections) (i : I.L) :
    c.ι i (sectionsEquiv hc s) = s.val i := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp
end IsLimit
end Multifork
end Multiequalizer
end CategoryTheory.Limits