import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Thin
universe w w' v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Limits
variable (J : Type w)
def WidePullbackShape := Option J
instance : Inhabited (WidePullbackShape J) where
  default := none
def WidePushoutShape := Option J
instance : Inhabited (WidePushoutShape J) where
  default := none
namespace WidePullbackShape
variable {J}
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq
attribute [nolint unusedArguments] instDecidableEqHom
instance struct : CategoryStruct (WidePullbackShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _
instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩
open Lean Elab Tactic
def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _) ))
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash
instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl
instance category : SmallCategory (WidePullbackShape J) :=
  thin_category
@[simp]
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl
attribute [nolint simpNF] Hom.id.sizeOf_spec
variable {C : Type u} [Category.{v} C]
@[simps]
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  NatIso.ofComponents fun j => eqToIso <| by aesop_cat
@[simps]
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> dsimp <;> simp [w] } }
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))
end WidePullbackShape
namespace WidePushoutShape
variable {J}
inductive Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, Hom X X
  | init : ∀ j : J, Hom none (some j)
  deriving DecidableEq
attribute [nolint unusedArguments] instDecidableEqHom
instance struct : CategoryStruct (WidePushoutShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _
instance Hom.inhabited : Inhabited (Hom (none : WidePushoutShape J) none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩
open Lean Elab Tactic
def evalCasesBash' : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePushoutShape _,
      (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _) ))
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash'
instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl
instance category : SmallCategory (WidePushoutShape J) :=
  thin_category
@[simp]
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl
attribute [nolint simpNF] Hom.id.sizeOf_spec
variable {C : Type u} [Category.{v} C]
@[simps]
def wideSpan (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [Eq.ndrec, hom_id, eq_rec_constant, Category.id_comp]; congr
    · cases g
      simp only [Eq.ndrec, hom_id, eq_rec_constant, Category.comp_id]; congr
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
  NatIso.ofComponents fun j => eqToIso <| by cases j; repeat rfl
@[simps]
def mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : ∀ j, F.obj (some j) ⟶ X)
    (w : ∀ j, F.map (Hom.init j) ≫ ι j = f) : Cocone F :=
  { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> dsimp <;> simp [w] } }
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ WidePushoutShape J' where
  functor := wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePushoutShape J)) ≌ WidePushoutShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))
end WidePushoutShape
variable (C : Type u) [Category.{v} C]
abbrev HasWidePullbacks : Prop :=
  ∀ J : Type w, HasLimitsOfShape (WidePullbackShape J) C
abbrev HasWidePushouts : Prop :=
  ∀ J : Type w, HasColimitsOfShape (WidePushoutShape J) C
variable {C J}
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)
abbrev HasWidePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : Prop :=
  HasColimit (WidePushoutShape.wideSpan B objs arrows)
noncomputable abbrev widePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)
noncomputable abbrev widePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j)
    [HasWidePushout B objs arrows] : C :=
  colimit (WidePushoutShape.wideSpan B objs arrows)
namespace WidePullback
variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none
@[reassoc (attr := simp)]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)
variable {arrows}
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)
variable (arrows)
variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)
@[reassoc]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]
@[reassoc]
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]
theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by aesop_cat) := by
  apply eq_lift_of_comp_eq
  · aesop_cat
  · rfl  
@[ext 1100]
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (∀ j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
end WidePullback
namespace WidePushout
variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)
variable [HasWidePushout B objs arrows]
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none
@[reassoc (attr := simp)]
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)
attribute [nolint simpNF] WidePushout.arrow_ι WidePushout.arrow_ι_assoc
variable {arrows}
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X)
    (w : ∀ j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)
variable (arrows)
variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)
@[reassoc]
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]
@[reassoc]
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]
theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w := by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← Category.assoc]
        simp := by
  apply eq_desc_of_comp_eq
  · aesop_cat
  · rfl 
@[ext 1100]
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (∀ j : J,
    ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
end WidePushout
variable (J)
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)
@[simps]
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂
def widePushoutShapeOpMap :
    ∀ X Y : WidePushoutShape J,
      (X ⟶ Y) → ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, WidePushoutShape.Hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, WidePushoutShape.Hom.init _ => Quiver.Hom.op (WidePullbackShape.Hom.term _)
@[simps]
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  obj X := op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y
@[simps!]
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp
@[simps!]
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _
@[simps]
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J
@[simps]
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
end CategoryTheory.Limits