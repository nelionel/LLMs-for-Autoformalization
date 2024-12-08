import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
universe v v₁ u₁ u
open CategoryTheory LinearMap Opposite
variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
variable (R) in
structure PresheafOfModules where
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' _ (R.map_id X)).inv.app _ := by aesop_cat
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' _ _ _ (R.map_comp f g)).inv.app _ := by aesop_cat
namespace PresheafOfModules
attribute [simp] map_id map_comp
attribute [reassoc] map_comp
variable (M M₁ M₂ : PresheafOfModules.{v} R)
lemma map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X) :
    M.map f (r • m) = R.map f r • M.map f m := by simp
lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]
@[ext]
structure Hom where
  app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f)).map (app Y) =
        app X ≫ M₂.map f := by aesop_cat
attribute [reassoc (attr := simp)] Hom.naturality
instance : Category (PresheafOfModules.{v} R) where
  Hom := Hom
  id _ := { app := fun _ ↦ 𝟙 _ }
  comp f g := { app := fun _ ↦ f.app _ ≫ g.app _ }
variable {M₁ M₂}
@[ext]
lemma hom_ext {f g : M₁ ⟶ M₂} (h : ∀ (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext (by ext1; apply h)
@[simp]
lemma id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : Hom.app (𝟙 M) X = 𝟙 _ := by
  rfl
@[simp]
lemma comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (f ≫ g).app X = f.app X ≫ g.app X := by
  rfl
lemma naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x) :=
  congr_fun ((forget _).congr_map (Hom.naturality f g)) x
@[simps!]
def isoMk (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f)).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by aesop_cat) : M₁ ≅ M₂ where
  hom := { app := fun X ↦ (app X).hom }
  inv :=
    { app := fun X ↦ (app X).inv
      naturality := fun {X Y} f ↦ by
        rw [← cancel_epi (app X).hom, ← reassoc_of% (naturality f), Iso.map_hom_inv_id,
          Category.comp_id, Iso.hom_inv_id_assoc]}
def presheaf : Cᵒᵖ ⥤ Ab where
  obj X := (forget₂ _ _).obj (M.obj X)
  map f := AddMonoidHom.mk' (M.map f) (by simp)
@[simp]
lemma presheaf_obj_coe (X : Cᵒᵖ) :
    (M.presheaf.obj X : Type _) = M.obj X := rfl
@[simp]
lemma presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f) x = M.map f x := rfl
instance (M : PresheafOfModules R) (X : Cᵒᵖ) :
    Module (R.obj X) (M.presheaf.obj X) :=
  inferInstanceAs (Module (R.obj X) (M.obj X))
variable (R) in
def toPresheaf : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  obj M := M.presheaf
  map f :=
    { app := fun X ↦ AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g ↦ by ext x; exact naturality_apply f g x }
@[simp]
lemma toPresheaf_obj_coe (X : Cᵒᵖ) :
    (((toPresheaf R).obj M).obj X : Type _) = M.obj X := rfl
@[simp]
lemma toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) :
    DFunLike.coe (α := M₁.obj X) (β := fun _ ↦ M₂.obj X)
      (((toPresheaf R).map f).app X) x = f.app X x := rfl
instance : (toPresheaf R).Faithful where
  map_injective {_ _ f g} h := by
    ext X x
    exact congr_fun (((evaluation _ _).obj X ⋙ forget _).congr_map h) x
section
variable (M : Cᵒᵖ ⥤ Ab.{v}) [∀ X, Module (R.obj X) (M.obj X)]
  (map_smul : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : R.obj X) (m : M.obj X),
    M.map f (r • m) = R.map f r • M.map f m)
@[simps]
def ofPresheaf : PresheafOfModules.{v} R where
  obj X := ModuleCat.of _ (M.obj X)
  map f :=
    { toFun := fun x ↦ M.map f x
      map_add' := by simp
      map_smul' := fun r m ↦ map_smul f r m }
@[simp]
lemma ofPresheaf_presheaf : (ofPresheaf M map_smul).presheaf = M := rfl
end
@[simps]
def homMk (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : ∀ (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    M₁ ⟶ M₂ where
  app X :=
    { toFun := φ.app X
      map_add' := by simp
      map_smul' := hφ X }
  naturality := fun f ↦ by
    ext x
    exact congr_fun ((forget _).congr_map (φ.naturality f)) x
instance : Zero (M₁ ⟶ M₂) where
  zero := { app := fun _ ↦ 0 }
variable (M₁ M₂) in
@[simp] lemma zero_app (X : Cᵒᵖ) : (0 : M₁ ⟶ M₂).app X = 0 := rfl
instance : Neg (M₁ ⟶ M₂) where
  neg f :=
    { app := fun X ↦ -f.app X
      naturality := fun {X Y} h ↦ by
        ext x
        dsimp
        erw [map_neg]
        rw [← naturality_apply]
        rfl }
instance : Add (M₁ ⟶ M₂) where
  add f g :=
    { app := fun X ↦ f.app X + g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        dsimp
        erw [map_add]
        rw [← naturality_apply, ← naturality_apply]
        rfl }
instance : Sub (M₁ ⟶ M₂) where
  sub f g :=
    { app := fun X ↦ f.app X - g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        dsimp
        erw [map_sub]
        rw [← naturality_apply, ← naturality_apply]
        rfl }
@[simp] lemma neg_app (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (-f).app X = -f.app X := rfl
@[simp] lemma add_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl
@[simp] lemma sub_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl
instance : AddCommGroup (M₁ ⟶ M₂) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
instance : Preadditive (PresheafOfModules R) where
instance : (toPresheaf R).Additive where
lemma zsmul_app (n : ℤ) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl
variable (R)
@[simps]
def evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
  obj M := M.obj X
  map f := f.app X
instance (X : Cᵒᵖ) : (evaluation.{v} R X).Additive where
@[simps]
noncomputable def restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    evaluation R X ⟶ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f) where
  app M := M.map f
def unit : PresheafOfModules R where
  obj X := ModuleCat.of _ (R.obj X)
  map {X Y } f :=
    { toFun := fun x ↦ R.map f x
      map_add' := by simp
      map_smul' := by aesop_cat }
lemma unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unit R).map f (1 : R.obj X) = (1 : R.obj Y) :=
  (R.map f).map_one
variable {R}
def sections (M : PresheafOfModules.{v} R) : Type _ := (M.presheaf ⋙ forget _).sections
abbrev sections.eval {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ) : M.obj X := s.1 X
@[simp]
lemma sections_property {M : PresheafOfModules.{v} R} (s : M.sections)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y := s.2 f
@[simps]
def sectionsMk {M : PresheafOfModules.{v} R} (s : ∀ X, M.obj X)
    (hs : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s Y) : M.sections where
  val := s
  property f := hs f
@[ext]
lemma sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections)
    (h : ∀ (X : Cᵒᵖ), s.val X = t.val X) : s = t :=
  Subtype.ext (by ext; apply h)
@[simps!]
def sectionsMap {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  N.sectionsMk (fun X ↦ f.app X (s.1 _))
    (fun X Y g ↦ by rw [← naturality_apply, sections_property])
@[simp]
lemma sectionsMap_comp {M N P : PresheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl
@[simp]
lemma sectionsMap_id {M : PresheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl
@[simps! apply_coe]
def unitHomEquiv (M : PresheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X ↦ Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X ↦ (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm (s.val X)
      naturality := fun {X Y} f ↦ by
        ext (x : R.obj X)
        change R.map f x • s.eval Y = M.map f (x • s.eval X)
        simp }
  left_inv f := by
    ext1 X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm_apply_apply (f.app X)
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).apply_symm_apply (s.val X)
section module_over_initial
variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)
section
variable (M : PresheafOfModules.{v} R)
noncomputable abbrev forgetToPresheafModuleCatObjObj (Y : Cᵒᵖ) : ModuleCat (R.obj X) :=
  (ModuleCat.restrictScalars (R.map (hX.to Y))).obj (M.obj Y)
@[simp]
lemma forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) :
    (forgetToPresheafModuleCatObjObj X hX M Y : Type _) = M.obj Y := rfl
def forgetToPresheafModuleCatObjMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    forgetToPresheafModuleCatObjObj X hX M Y ⟶
      forgetToPresheafModuleCatObjObj X hX M Z where
  toFun x := M.map f x
  map_add' := by simp
  map_smul' r x := by
    simp only [ModuleCat.restrictScalars.smul_def, AddHom.toFun_eq_coe, AddHom.coe_mk,
      RingHom.id_apply, M.map_smul]
    rw [← CategoryTheory.comp_apply, ← R.map_comp]
    congr
    apply hX.hom_ext
@[simp]
lemma forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y) :
    DFunLike.coe (α := M.obj Y) (β := fun _ ↦ M.obj Z)
      (forgetToPresheafModuleCatObjMap X hX M f) m = M.map f m := rfl
@[simps]
noncomputable def forgetToPresheafModuleCatObj
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (M : PresheafOfModules.{v} R) :
    Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj Y := forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f
end
noncomputable def forgetToPresheafModuleCatMap
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) {M N : PresheafOfModules.{v} R} (f : M ⟶ N) :
    forgetToPresheafModuleCatObj X hX M ⟶ forgetToPresheafModuleCatObj X hX N where
  app Y :=
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r ↦ (f.app Y).map_smul (R.1.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x
@[simps]
noncomputable def forgetToPresheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj M := forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f
end module_over_initial
end PresheafOfModules