import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
open CategoryTheory.Limits
universe v u
namespace CategoryTheory
variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]
structure DifferentialObject where
  obj : C
  d : obj ⟶ obj⟦(1 : S)⟧
  d_squared : d ≫ d⟦(1 : S)⟧' = 0 := by aesop_cat
attribute [reassoc (attr := simp)] DifferentialObject.d_squared
variable {S C}
namespace DifferentialObject
@[ext] 
structure Hom (X Y : DifferentialObject S C) where
  f : X.obj ⟶ Y.obj
  comm : X.d ≫ f⟦1⟧' = f ≫ Y.d := by aesop_cat
attribute [reassoc (attr := simp)] Hom.comm
namespace Hom
@[simps]
def id (X : DifferentialObject S C) : Hom X X where
  f := 𝟙 X.obj
@[simps]
def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f
end Hom
instance categoryOfDifferentialObjects : Category (DifferentialObject S C) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
@[ext]
theorem ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by aesop_cat) : f = g :=
  Hom.ext w
@[simp]
theorem id_f (X : DifferentialObject S C) : (𝟙 X : X ⟶ X).f = 𝟙 X.obj := rfl
@[simp]
theorem comp_f {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f :=
  rfl
@[simp]
theorem eqToHom_f {X Y : DifferentialObject S C} (h : X = Y) :
    Hom.f (eqToHom h) = eqToHom (congr_arg _ h) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl]
  rfl
variable (S C)
def forget : DifferentialObject S C ⥤ C where
  obj X := X.obj
  map f := f.f
instance forget_faithful : (forget S C).Faithful where
variable {S C}
section
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]
instance {X Y : DifferentialObject S C} : Zero (X ⟶ Y) := ⟨{f := 0}⟩
@[simp]
theorem zero_f (P Q : DifferentialObject S C) : (0 : P ⟶ Q).f = 0 := rfl
instance hasZeroMorphisms : HasZeroMorphisms (DifferentialObject S C) where
end
@[simps]
def isoApp {X Y : DifferentialObject S C} (f : X ≅ Y) : X.obj ≅ Y.obj where
  hom := f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]
@[simp]
theorem isoApp_refl (X : DifferentialObject S C) : isoApp (Iso.refl X) = Iso.refl X.obj := rfl
@[simp]
theorem isoApp_symm {X Y : DifferentialObject S C} (f : X ≅ Y) : isoApp f.symm = (isoApp f).symm :=
  rfl
@[simp]
theorem isoApp_trans {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z) :
    isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g := rfl
@[simps]
def mkIso {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d) :
    X ≅ Y where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Functor.mapIso_hom,
      hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id
end DifferentialObject
namespace Functor
universe v' u'
variable (D : Type u') [Category.{v'} D]
variable [HasZeroMorphisms D] [HasShift D S]
@[simps]
def mapDifferentialObject (F : C ⥤ D)
    (η : (shiftFunctor C (1 : S)).comp F ⟶ F.comp (shiftFunctor D (1 : S)))
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : DifferentialObject S C ⥤ DifferentialObject S D where
  obj X :=
    { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp, ← Functor.comp_map F (shiftFunctor D (1 : S))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [Functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        rw [zero_comp, zero_comp] }
  map f :=
    { f := F.map f.f
      comm := by
        dsimp
        slice_lhs 2 3 => rw [← Functor.comp_map F (shiftFunctor D (1 : S)), ← η.naturality f.f]
        slice_lhs 1 2 => rw [Functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        rw [Category.assoc] }
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp
end Functor
end CategoryTheory
namespace CategoryTheory
namespace DifferentialObject
variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroObject C] [HasZeroMorphisms C] [HasShift C S]
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]
open scoped ZeroObject
instance hasZeroObject : HasZeroObject (DifferentialObject S C) where
  zero := ⟨{ obj := 0, d := 0 },
    { unique_to := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩,
      unique_from := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩ }⟩
end DifferentialObject
namespace DifferentialObject
variable (S : Type*) [AddMonoidWithOne S]
variable (C : Type (u + 1)) [LargeCategory C] [ConcreteCategory C] [HasZeroMorphisms C]
variable [HasShift C S]
instance concreteCategoryOfDifferentialObjects : ConcreteCategory (DifferentialObject S C) where
  forget := forget S C ⋙ CategoryTheory.forget C
instance : HasForget₂ (DifferentialObject S C) C where
  forget₂ := forget S C
end DifferentialObject
namespace DifferentialObject
variable {S : Type*} [AddCommGroupWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]
noncomputable section
@[simps]
def shiftFunctor (n : S) : DifferentialObject S C ⥤ DifferentialObject S C where
  obj X :=
    { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp, Category.assoc, shiftComm_hom_comp_assoc, ← Functor.map_comp_assoc,
          X.d_squared, Functor.map_zero, zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := by
        dsimp
        erw [Category.assoc, shiftComm_hom_comp, ← Functor.map_comp_assoc, f.comm,
          Functor.map_comp_assoc]
        rfl }
  map_id X := by ext1; dsimp; rw [Functor.map_id]
  map_comp f g := by ext1; dsimp; rw [Functor.map_comp]
@[simps!]
nonrec def shiftFunctorAdd (m n : S) :
    shiftFunctor C (m + n) ≅ shiftFunctor C m ⋙ shiftFunctor C n := by
  refine NatIso.ofComponents (fun X => mkIso (shiftAdd X.obj _ _) ?_) (fun f => ?_)
  · dsimp
    rw [← cancel_epi ((shiftFunctorAdd C m n).inv.app X.obj)]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← NatTrans.naturality_assoc]
    dsimp
    simp only [Functor.map_comp, Category.assoc,
      shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app 1 m n X.obj,
      Iso.inv_hom_id_app_assoc]
  · ext; dsimp; exact NatTrans.naturality _ _
section
@[simps!]
def shiftZero : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C) := by
  refine NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) ?_) (fun f => ?_)
  · erw [← NatTrans.naturality]
    dsimp
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
  · aesop_cat
end
instance : HasShift (DifferentialObject S C) S :=
  hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        convert shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        dsimp [shiftFunctorAdd']
        simp
      zero_add_hom_app := fun n X => by
        ext1
        convert shiftFunctorAdd_zero_add_hom_app n X.obj
        simp
      add_zero_hom_app := fun n X => by
        ext1
        convert shiftFunctorAdd_add_zero_hom_app n X.obj
        simp }
end
end DifferentialObject
end CategoryTheory