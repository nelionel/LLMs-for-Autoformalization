import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
universe v v' u u'
namespace CategoryTheory
open Opposite
namespace Limits
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)
@[simps]
def multicospanIndexEnd : MulticospanIndex C where
  L := J
  R := Arrow J
  fstTo f := f.left
  sndTo f := f.right
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right
abbrev Wedge := Multifork (multicospanIndexEnd F)
namespace Wedge
variable {F}
section Constructor
variable (pt : C) (π : ∀ (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : ∀ ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)
@[simps! pt]
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f ↦ hπ f.hom)
@[simp]
lemma mk_ι (j : J) : (mk pt π hπ).ι j = π j := rfl
end Constructor
@[reassoc]
lemma condition (c : Wedge F) {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)
namespace IsLimit
variable {c : Wedge F} (hc : IsLimit c)
lemma hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.ι j = g ≫ c.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext hc h
def lift (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ ↦ hf _)
@[reassoc (attr := simp)]
lemma lift_ι (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) (j : J) :
    lift hc f hf ≫ c.ι j = f j := by
  apply IsLimit.fac
end IsLimit
end Wedge
section End
abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)
variable [HasEnd F]
noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)
noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _
@[reassoc]
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply Wedge.condition
variable {F}
@[ext]
lemma hom_ext {X : C} {f g : X ⟶ end_ F} (h : ∀ j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ ↦ h _)
section
variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)
noncomputable def end_.lift : X ⟶ end_ F :=
  Wedge.IsLimit.lift (limit.isLimit _) f hf
@[reassoc (attr := simp)]
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac
end
end End
end Limits
end CategoryTheory