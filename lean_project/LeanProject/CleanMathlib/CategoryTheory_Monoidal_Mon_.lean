import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Algebra.PUnitInstances.Algebra
universe v₁ v₂ u₁ u₂ u
open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
class Mon_Class (X : C) where
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul' : one ▷ X ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one' : X ◁ one ≫ mul = (ρ_ X).hom := by aesop_cat
  mul_assoc' : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat
namespace Mon_Class
@[inherit_doc] scoped notation "μ" => Mon_Class.mul
@[inherit_doc] scoped notation "μ["M"]" => Mon_Class.mul (X := M)
@[inherit_doc] scoped notation "η" => Mon_Class.one
@[inherit_doc] scoped notation "η["M"]" => Mon_Class.one (X := M)
attribute [reassoc] one_mul' mul_one' mul_assoc'
@[reassoc (attr := simp)]
theorem one_mul (X : C) [Mon_Class X] : η ▷ X ≫ μ = (λ_ X).hom := one_mul'
@[reassoc (attr := simp)]
theorem mul_one (X : C) [Mon_Class X] : X ◁ η ≫ μ = (ρ_ X).hom := mul_one'
@[reassoc (attr := simp)]
theorem mul_assoc (X : C) [Mon_Class X] : μ ▷ X ≫ μ = (α_ X X X).hom ≫ X ◁ μ ≫ μ := mul_assoc'
end Mon_Class
open scoped Mon_Class
variable {M N : C} [Mon_Class M] [Mon_Class N]
class IsMon_Hom (f : M ⟶ N) : Prop where
  one_hom : η ≫ f = η := by aesop_cat
  mul_hom : μ ≫ f = (f ⊗ f) ≫ μ := by aesop_cat
attribute [reassoc (attr := simp)] IsMon_Hom.one_hom IsMon_Hom.mul_hom
variable (C)
structure Mon_ where
  X : C
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by aesop_cat
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by aesop_cat
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by aesop_cat
attribute [reassoc] Mon_.one_mul Mon_.mul_one
attribute [simp] Mon_.one_mul Mon_.mul_one
attribute [reassoc (attr := simp)] Mon_.mul_assoc
namespace Mon_
variable {C}
@[simps]
def mk' (X : C) [Mon_Class X] : Mon_ C where
  X := X
  one := η
  mul := μ
instance {M : Mon_ C} : Mon_Class M.X where
  one := M.one
  mul := M.mul
  one_mul' := M.one_mul
  mul_one' := M.mul_one
  mul_assoc' := M.mul_assoc
variable (C)
@[simps]
def trivial : Mon_ C where
  X := 𝟙_ C
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence
instance : Inhabited (Mon_ C) :=
  ⟨trivial C⟩
variable {C}
variable {M : Mon_ C}
@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, M.one_mul, leftUnitor_naturality]
@[simp]
theorem mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, M.mul_one, rightUnitor_naturality]
theorem mul_assoc_flip :
    (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul := by simp
@[ext]
structure Hom (M N : Mon_ C) where
  hom : M.X ⟶ N.X
  one_hom : M.one ≫ hom = N.one := by aesop_cat
  mul_hom : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul := by aesop_cat
attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom
@[simps]
def id (M : Mon_ C) : Hom M M where
  hom := 𝟙 M.X
instance homInhabited (M : Mon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩
@[simps]
def comp {M N O : Mon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom
instance : Category (Mon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g
@[ext]
lemma ext {X Y : Mon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Hom.ext w
@[simp]
theorem id_hom' (M : Mon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl
@[simp]
theorem comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl
section
variable (C)
@[simps]
def forget : Mon_ C ⥤ C where
  obj A := A.X
  map f := f.hom
end
instance forget_faithful : (forget C).Faithful where
instance {A B : Mon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩
@[simps]
def mkIso {M N : Mon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
    (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat) : M ≅ N where
  hom := { hom := f.hom }
  inv :=
  { hom := f.inv
    one_hom := by rw [← one_f]; simp
    mul_hom := by
      rw [← cancel_mono f.hom]
      slice_rhs 2 3 => rw [mul_f]
      simp }
@[simps]
instance uniqueHomFromTrivial (A : Mon_ C) : Unique (trivial C ⟶ A) where
  default :=
  { hom := A.one
    mul_hom := by simp [A.one_mul, unitors_equal] }
  uniq f := by
    ext
    simp only [trivial_X]
    rw [← Category.id_comp f.hom]
    erw [f.one_hom]
open CategoryTheory.Limits
instance : HasInitial (Mon_ C) :=
  hasInitial_of_unique (trivial C)
end Mon_
namespace CategoryTheory.Functor
variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
#adaptation_note
set_option maxHeartbeats 400000 in
@[simps]
def mapMon (F : C ⥤ D) [F.LaxMonoidal] : Mon_ C ⥤ Mon_ D where
  obj A :=
    { X := F.obj A.X
      one := ε F ≫ F.map A.one
      mul := «μ» F _ _ ≫ F.map A.mul
      one_mul := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          LaxMonoidal.left_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.one_mul]
      mul_one := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
          LaxMonoidal.right_unitality]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_one]
      mul_assoc := by
        simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
        slice_lhs 3 4 => rw [← F.map_comp, A.mul_assoc]
        simp }
  map f :=
    { hom := F.map f.hom
      one_hom := by dsimp; rw [Category.assoc, ← F.map_comp, f.one_hom]
      mul_hom := by
        rw [Category.assoc, μ_natural_assoc, ← F.map_comp, ← F.map_comp,
          f.mul_hom] }
variable (C D)
@[simps] 
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon_ C ⥤ Mon_ D where
  obj F := F.mapMon
  map α := { app := fun A => { hom := α.hom.app A.X } }
  map_comp _ _ := rfl
end CategoryTheory.Functor
namespace Mon_
namespace EquivLaxMonoidalFunctorPUnit
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ Mon_ C where
  obj F := (F.mapMon : Mon_ _ ⥤ Mon_ C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _
variable {C}
@[simps!]
def monToLaxMonoidalObj (A : Mon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X
instance (A : Mon_ C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε' := A.one
  μ' := fun _ _ => A.mul
@[simp]
lemma monToLaxMonoidalObj_ε (A : Mon_ C) :
    ε (monToLaxMonoidalObj A) = A.one := rfl
@[simp]
lemma monToLaxMonoidalObj_μ (A : Mon_ C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = A.mul := rfl
variable (C)
@[simps]
def monToLaxMonoidal : Mon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
set_option maxHeartbeats 400000 in
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))
end EquivLaxMonoidalFunctorPUnit
open EquivLaxMonoidalFunctorPUnit
attribute [local simp] eqToIso_map
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ Mon_ C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C
end Mon_
namespace Mon_
variable {C}
theorem one_associator {M N P : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ P.one)) ≫ (α_ M.X N.X P.X).hom =
      (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ (λ_ (𝟙_ C)).inv ≫ (N.one ⊗ P.one)) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp P.one, tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp M.one, tensor_comp]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp
theorem one_leftUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.X).hom = M.one := by
  simp
theorem one_rightUnitor {M : Mon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.X).hom = M.one := by
  simp [← unitors_equal]
section BraidedCategory
variable [BraidedCategory C]
theorem Mon_tensor_one_mul (M N : Mon_ C) :
    (((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ▷ (M.X ⊗ N.X)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (λ_ (M.X ⊗ N.X)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul M, one_mul N]
  symm
  exact tensor_left_unitality M.X N.X
theorem Mon_tensor_mul_one (M N : Mon_ C) :
    (M.X ⊗ N.X) ◁ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (ρ_ (M.X ⊗ N.X)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one M, mul_one N]
  symm
  exact tensor_right_unitality M.X N.X
theorem Mon_tensor_mul_assoc (M N : Mon_ C) :
    ((tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul)) ▷ (M.X ⊗ N.X)) ≫
        tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) =
      (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
        ((M.X ⊗ N.X) ◁ (tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul))) ≫
          tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc M, mul_assoc N, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp
theorem mul_associator {M N P : Mon_ C} :
    (tensorμ (M.X ⊗ N.X) P.X (M.X ⊗ N.X) P.X ≫
          (tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
        (α_ M.X N.X P.X).hom =
      ((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫
        tensorμ M.X (N.X ⊗ P.X) M.X (N.X ⊗ P.X) ≫
          (M.mul ⊗ tensorμ N.X P.X N.X P.X ≫ (N.mul ⊗ P.mul)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp P.mul, tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]
theorem mul_leftUnitor {M : Mon_ C} :
    (tensorμ (𝟙_ C) M.X (𝟙_ C) M.X ≫ ((λ_ (𝟙_ C)).hom ⊗ M.mul)) ≫ (λ_ M.X).hom =
      ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp M.mul, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]
theorem mul_rightUnitor {M : Mon_ C} :
    (tensorμ M.X (𝟙_ C) M.X (𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M.X).hom =
      ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul := by
  rw [← Category.id_comp M.mul, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]
@[simps tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (Mon_ C) :=
  let tensorObj (M N : Mon_ C) : Mon_ C :=
    { X := M.X ⊗ N.X
      one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)
      mul := tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul)
      one_mul := Mon_tensor_one_mul M N
      mul_one := Mon_tensor_mul_one M N
      mul_assoc := Mon_tensor_mul_assoc M N }
  let tensorHom {X₁ Y₁ X₂ Y₂ : Mon_ C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
      tensorObj _ _ ⟶ tensorObj _ _ :=
    { hom := f.hom ⊗ g.hom
      one_hom := by
        dsimp
        slice_lhs 2 3 => rw [← tensor_comp, Hom.one_hom f, Hom.one_hom g]
      mul_hom := by
        dsimp
        slice_rhs 1 2 => rw [tensorμ_natural]
        slice_lhs 2 3 => rw [← tensor_comp, Hom.mul_hom f, Hom.mul_hom g, tensor_comp]
        simp only [Category.assoc] }
  { tensorObj := tensorObj
    tensorHom := tensorHom
    whiskerRight := fun f Y => tensorHom f (𝟙 Y)
    whiskerLeft := fun X _ _ g => tensorHom (𝟙 X) g
    tensorUnit := trivial C
    associator := fun M N P ↦ mkIso (α_ M.X N.X P.X) one_associator mul_associator
    leftUnitor := fun M ↦ mkIso (λ_ M.X) one_leftUnitor mul_leftUnitor
    rightUnitor := fun M ↦ mkIso (ρ_ M.X) one_rightUnitor mul_rightUnitor }
@[simp]
theorem tensorUnit_X : (𝟙_ (Mon_ C)).X = 𝟙_ C := rfl
@[simp]
theorem tensorUnit_one : (𝟙_ (Mon_ C)).one = 𝟙 (𝟙_ C) := rfl
@[simp]
theorem tensorUnit_mul : (𝟙_ (Mon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl
@[simp]
theorem tensorObj_one (X Y : Mon_ C) : (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl
@[simp]
theorem tensorObj_mul (X Y : Mon_ C) :
    (X ⊗ Y).mul = tensorμ X.X Y.X X.X Y.X ≫ (X.mul ⊗ Y.mul) := rfl
@[simp]
theorem whiskerLeft_hom {X Y : Mon_ C} (f : X ⟶ Y) (Z : Mon_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rw [← tensorHom_id]; rfl
@[simp]
theorem whiskerRight_hom (X : Mon_ C) {Y Z : Mon_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rw [← id_tensorHom]; rfl
@[simp]
theorem leftUnitor_hom_hom (X : Mon_ C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl
@[simp]
theorem leftUnitor_inv_hom (X : Mon_ C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl
@[simp]
theorem rightUnitor_hom_hom (X : Mon_ C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl
@[simp]
theorem rightUnitor_inv_hom (X : Mon_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl
@[simp]
theorem associator_hom_hom (X Y Z : Mon_ C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl
@[simp]
theorem associator_inv_hom (X Y Z : Mon_ C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl
@[simp]
theorem tensor_one (M N : Mon_ C) : (M ⊗ N).one = (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) := rfl
@[simp]
theorem tensor_mul (M N : Mon_ C) : (M ⊗ N).mul =
    tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := rfl
instance monMonoidal : MonoidalCategory (Mon_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
@[simps!]
instance {M N : C} [Mon_Class M] [Mon_Class N] : Mon_Class (M ⊗ N) :=
  inferInstanceAs <| Mon_Class (Mon_.mk' M ⊗ Mon_.mk' N).X
variable (C)
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }
@[simp] theorem forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Mon_ C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : Mon_ C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
variable {C}
theorem one_braiding {X Y : Mon_ C} : (X ⊗ Y).one ≫ (β_ X.X Y.X).hom = (Y ⊗ X).one := by
  simp only [monMonoidalStruct_tensorObj_X, tensor_one, Category.assoc,
    BraidedCategory.braiding_naturality, braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal
end BraidedCategory
section SymmetricCategory
variable [SymmetricCategory C]
theorem mul_braiding {X Y : Mon_ C} :
    (X ⊗ Y).mul ≫ (β_ X.X Y.X).hom = ((β_ X.X Y.X).hom ⊗ (β_ X.X Y.X).hom) ≫ (Y ⊗ X).mul := by
  dsimp
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right, BraidedCategory.braiding_tensor_left,
    comp_whiskerRight, whisker_assoc, MonoidalCategory.whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
    pentagon_inv_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]
instance : SymmetricCategory (Mon_ C) where
  braiding := fun X Y => mkIso (β_ X.X Y.X) one_braiding mul_braiding
  symmetry := fun X Y => by
    ext
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]
end SymmetricCategory
end Mon_