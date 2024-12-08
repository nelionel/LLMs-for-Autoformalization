import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens
namespace TopCat
variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)
namespace Presheaf
nonrec def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) F
theorem isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf :=
  fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by aesop_cat, fun _ => by aesop_cat⟩
theorem isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  Presheaf.isSheaf_of_iso_iff α
theorem isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf :=
  (isSheaf_iso_iff α).1 h
end Presheaf
variable (C X)
nonrec def Sheaf : Type max u v w :=
  Sheaf (Opens.grothendieckTopology X) C
instance SheafCat : Category (Sheaf C X) :=
  show Category (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) from inferInstance
variable {C X}
abbrev Sheaf.presheaf (F : X.Sheaf C) : TopCat.Presheaf C X :=
  F.1
variable (C X)
instance sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩
namespace Sheaf
def forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X :=
  sheafToPresheaf _ _
instance forget_full : (forget C X).Full where
  map_surjective f := ⟨Sheaf.Hom.mk f, rfl⟩
instance forgetFaithful : (forget C X).Faithful where
  map_injective := Sheaf.Hom.ext
theorem id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ :=
  rfl
theorem comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
    (f ≫ g).1.app t = f.1.app t ≫ g.1.app t :=
  rfl
end Sheaf
end TopCat