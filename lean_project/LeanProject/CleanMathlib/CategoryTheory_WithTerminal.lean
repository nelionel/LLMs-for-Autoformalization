import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
namespace CategoryTheory
universe v u
variable (C : Type u) [Category.{v} C]
inductive WithTerminal : Type u
  | of : C → WithTerminal
  | star : WithTerminal
  deriving Inhabited
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal
inductive WithInitial : Type u
  | of : C → WithInitial
  | star : WithInitial
  deriving Inhabited
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial
namespace WithTerminal
variable {C}
@[simp]
def Hom : WithTerminal C → WithTerminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of _ => PEmpty
  | _, star => PUnit
attribute [nolint simpNF] Hom.eq_3
@[simp]
def id : ∀ X : WithTerminal C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit
@[simp]
def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | of _X, _, star => fun _f _g => PUnit.unit
  | star, of _X, _ => fun f _g => PEmpty.elim f
  | _, star, of _Y => fun _f g => PEmpty.elim g
  | star, star, star => fun _ _ => PUnit.unit
attribute [nolint simpNF] comp.eq_3
attribute [nolint simpNF] comp.eq_4
instance : Category.{v} (WithTerminal C) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;> cases b <;> cases c <;> cases d <;> try aesop_cat
    · exact (h : PEmpty).elim
    · exact (g : PEmpty).elim
    · exact (h : PEmpty).elim
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl
@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_from_star {X : C} (f : star ⟶ of X) : False := (f : PEmpty).elim
def incl : C ⥤ WithTerminal C where
  obj := of
  map f := f
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩
instance : (incl : C ⥤ _).Faithful where
@[simps]
def map {D : Type*} [Category D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of _, star, _ => PUnit.unit
    | star, star, _ => PUnit.unit
@[simps!]
def mapId (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)
@[simps!]
def mapComp {D E : Type*} [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)
@[simps]
def map₂ {D : Type*} [Category D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | of x, star, _ => rfl
    | star, star, _ => rfl
@[simps]
def prelaxfunctor : PrelaxFunctor Cat Cat where
  obj C := Cat.of (WithTerminal C)
  map := map
  map₂ := map₂
  map₂_id := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_comp := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
@[simps]
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
  mapId C := mapId C
  mapComp := mapComp
  map₂_whisker_left := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, Cat.whiskerLeft_app, mapComp_hom_app,
        Iso.refl_hom, mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, Cat.whiskerRight_app, mapComp_hom_app,
        Iso.refl_hom, map_map, mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    dsimp
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerRight_app,
        map_map, down_id, Functor.map_id, Cat.whiskerLeft_app, mapComp_inv_app, Iso.refl_inv,
        Category.comp_id, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Bicategory.whiskerRight, whiskerRight_app, map_obj, mapComp_hom_app,
        Iso.refl_hom, map_map, down_id, Functor.map_id, Bicategory.whiskerLeft, whiskerLeft_app,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.leftUnitor_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerRight_app,
        mapId_hom_app, map_map, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, map_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.rightUnitor_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerLeft_app,
        mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, map_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
instance {X : WithTerminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of _ => PUnit.unit
    | star => PUnit.unit
  uniq := by aesop_cat
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _
@[simps]
def lift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | of x, star, _ => M x
    | star, star, _ => 𝟙 Z
@[simps!]
def inclLift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
@[simps!]
def liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
theorem lift_map_liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).hom =
      (inclLift F M hM).hom.app x ≫ M x := by
  erw [Category.id_comp, Category.comp_id]
  rfl
@[simp]
def liftUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
        exact hh _
      · cases f
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)
@[simps!]
def liftToTerminal {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    WithTerminal C ⥤ D :=
  lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _
@[simps!]
def inclLiftToTerminal {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _
@[simps!]
def liftToTerminalUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _
@[simp]
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _
instance isIso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩
end WithTerminal
namespace WithInitial
variable {C}
@[simp]
def Hom : WithInitial C → WithInitial C → Type v
  | of X, of Y => X ⟶ Y
  | of _, _ => PEmpty
  | star, _ => PUnit
attribute [nolint simpNF] Hom.eq_2
@[simp]
def id : ∀ X : WithInitial C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit
@[simp]
def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | star, _, of _X => fun _f _g => PUnit.unit
  | _, of _X, star => fun _f g => PEmpty.elim g
  | of _Y, star, _ => fun f _g => PEmpty.elim f
  | star, star, star => fun _ _ => PUnit.unit
attribute [nolint simpNF] comp.eq_3
attribute [nolint simpNF] comp.eq_4
instance : Category.{v} (WithInitial C) where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g
  assoc {a b c d} f g h := by
    cases a <;> cases b <;> cases c <;> cases d <;> try aesop_cat
    · exact (g : PEmpty).elim
    · exact (f : PEmpty).elim
    · exact (f : PEmpty).elim
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f
@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl
@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_to_star {X : C} (f : of X ⟶ star) : False := (f : PEmpty).elim
def incl : C ⥤ WithInitial C where
  obj := of
  map f := f
instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩
instance : (incl : C ⥤ _).Faithful where
@[simps]
def map {D : Type*} [Category D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => PUnit.unit
    | star, star, _ => PUnit.unit
@[simps!]
def mapId (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithInitial C) :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)
@[simps!]
def mapComp {D E : Type*} [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)
@[simps]
def map₂ {D : Type*} [Category D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | star, of x, _ => rfl
    | star, star, _ => rfl
@[simps]
def prelaxfunctor : PrelaxFunctor Cat Cat where
  obj C := Cat.of (WithInitial C)
  map := map
  map₂ := map₂
  map₂_id := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_comp := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
@[simps]
def pseudofunctor : Pseudofunctor Cat Cat where
  toPrelaxFunctor := prelaxfunctor
  mapId C := mapId C
  mapComp := mapComp
  map₂_whisker_left := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, Cat.whiskerLeft_app, mapComp_hom_app,
        Iso.refl_hom, mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, Cat.whiskerRight_app, mapComp_hom_app,
        Iso.refl_hom, map_map, mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerRight_app,
        map_map, down_id, Functor.map_id, Cat.whiskerLeft_app, mapComp_inv_app, Iso.refl_inv,
        Category.comp_id, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, map_obj, Category.comp_id]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.leftUnitor_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerRight_app,
        mapId_hom_app, map_map, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, map_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_obj,
        prelaxfunctor_toPrelaxFunctorStruct_toPrefunctor_map, map_obj, Cat.comp_obj,
        Bicategory.Strict.rightUnitor_eqToIso, eqToIso_refl, Iso.refl_hom,
        prelaxfunctor_toPrelaxFunctorStruct_map₂, map₂_app, mapComp_hom_app, Cat.whiskerLeft_app,
        mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, map_obj, Category.comp_id]
      rw [← Functor.map_id, Cat.id_map]
      rfl
    · rfl
instance {X : WithInitial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of _x => PUnit.unit
    | star => PUnit.unit
  uniq := by aesop_cat
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _
@[simps]
def lift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of _, of _, f => F.map (down f)
    | star, of _, _ => M _
    | star, star, _ => 𝟙 _
@[simps!]
def inclLift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
@[simps!]
def liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
theorem liftStar_lift_map {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) =
      M x ≫ (inclLift F M hM).hom.app x := by
  erw [Category.id_comp, Category.comp_id]
  rfl
@[simp]
def liftUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
      · cases f
        change G.map _ ≫ h.hom.app _ = hG.hom ≫ _
        symm
        erw [← Iso.eq_inv_comp, ← Category.assoc, hh]
        simp
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)
@[simps!]
def liftToInitial {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    WithInitial C ⥤ D :=
  lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _
@[simps!]
def inclLiftToInitial {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _
@[simps!]
def liftToInitialUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _
@[simp]
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _
instance isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩
end WithInitial
end CategoryTheory