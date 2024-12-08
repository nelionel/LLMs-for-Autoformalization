import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.FinCategory.Basic
universe v₁ u₁
noncomputable section
open CategoryTheory.Limits
open scoped Classical
namespace CategoryTheory
section Bicone
inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq
variable (J : Type u₁)
instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩
instance finBicone [Fintype J] : Fintype (Bicone J) where
  elems := [Bicone.left, Bicone.right].toFinset ∪ Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp [Fintype.complete]
variable [Category.{v₁} J]
inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)
instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩
instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  cases f <;> cases g <;> simp only [diagram.injEq] <;> infer_instance
@[simps]
instance biconeCategoryStruct : CategoryStruct (Bicone J) where
  Hom := BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
    · exact g
    · cases g
      apply BiconeHom.left
    · cases g
      apply BiconeHom.right
    · rcases g with (_|_|_|_|g)
      exact BiconeHom.diagram (f ≫ g)
instance biconeCategory : Category (Bicone J) where
  id_comp f := by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp
end Bicone
section SmallCategory
variable (J : Type v₁) [SmallCategory J]
@[simps]
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C where
  obj X := Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_|_|_|_|f)
    · exact 𝟙 _
    · exact 𝟙 _
    · exact c₁.π.app _
    · exact c₂.π.app _
    · exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_|_|_|_|_)
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · cases g
      exact (Category.id_comp _).symm.trans (c₁.π.naturality _)
    · cases g
      exact (Category.id_comp _).symm.trans (c₂.π.naturality _)
    · cases g
      apply F.map_comp
instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
      { elems := {BiconeHom.right_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := {BiconeHom.right _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := Finset.image BiconeHom.diagram Fintype.elems
      complete := fun f => by
        rcases f with (_|_|_|_|f)
        simp only [Finset.mem_image]
        use f
        simpa using Fintype.complete _ }
instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J
instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where
end SmallCategory
end CategoryTheory