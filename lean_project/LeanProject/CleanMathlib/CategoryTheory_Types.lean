import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.PPWithUniv
namespace CategoryTheory
universe v v' w u u'
@[to_additive existing CategoryTheory.types]
instance types : LargeCategory (Type u) where
  Hom a b := a → b
  id _ := id
  comp f g := g ∘ f
theorem types_hom {α β : Type u} : (α ⟶ β) = (α → β) :=
  rfl
@[ext] theorem types_ext {α β : Type u} (f g : α ⟶ β) (h : ∀ a : α, f a = g a) : f = g := by
  funext x
  exact h x
theorem types_id (X : Type u) : 𝟙 X = id :=
  rfl
theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f :=
  rfl
@[simp]
theorem types_id_apply (X : Type u) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
@[simp]
theorem types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl
@[simp]
theorem hom_inv_id_apply {X Y : Type u} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  congr_fun f.hom_inv_id x
@[simp]
theorem inv_hom_id_apply {X Y : Type u} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y
abbrev asHom {α β : Type u} (f : α → β) : α ⟶ β :=
  f
@[inherit_doc]
scoped notation "↾" f:200 => CategoryTheory.asHom f
section
variable (α β γ : Type u) (f : α → β) (g : β → γ)
example : α → γ :=
  ↾f ≫ ↾g
example [IsIso (↾f)] : Mono (↾f) := by infer_instance
example [IsIso (↾f)] : ↾f ≫ inv (↾f) = 𝟙 α := by simp
end
namespace Functor
variable {J : Type u} [Category.{v} J]
def sections (F : J ⥤ Type w) : Set (∀ j, F.obj j) :=
  { u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }
@[simp]
lemma sections_property {F : J ⥤ Type w} (s : (F.sections : Type _))
    {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j' :=
  s.property f
lemma sections_ext_iff {F : J ⥤ Type w} {x y : F.sections} : x = y ↔ ∀ j, x.val j = y.val j :=
  Subtype.ext_iff.trans funext_iff
variable (J)
@[simps]
def sectionsFunctor : (J ⥤ Type w) ⥤ Type max u w where
  obj F := F.sections
  map {F G} φ x := ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    (congr_fun (φ.naturality f) (x.1 j)).symm.trans (by simp [x.2 f])⟩
end Functor
namespace FunctorToTypes
variable {C : Type u} [Category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}
variable (σ : F ⟶ G) (τ : G ⟶ H)
@[simp]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) := by simp [types_comp]
@[simp]
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a := by simp [types_id]
theorem naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
  congr_fun (σ.naturality f) x
@[simp]
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  rfl
@[simp]
theorem eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) :
    F.map (eqToHom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x := by
  aesop_cat
variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}
@[simp]
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl
@[simp]
theorem map_inv_map_hom_apply (f : X ≅ Y) (x : F.obj X) : F.map f.inv (F.map f.hom x) = x :=
  congr_fun (F.mapIso f).hom_inv_id x
@[simp]
theorem map_hom_map_inv_apply (f : X ≅ Y) (y : F.obj Y) : F.map f.hom (F.map f.inv y) = y :=
  congr_fun (F.mapIso f).inv_hom_id y
@[simp]
theorem hom_inv_id_app_apply (α : F ≅ G) (X) (x) : α.inv.app X (α.hom.app X x) = x :=
  congr_fun (α.hom_inv_id_app X) x
@[simp]
theorem inv_hom_id_app_apply (α : F ≅ G) (X) (x) : α.hom.app X (α.inv.app X x) = x :=
  congr_fun (α.inv_hom_id_app X) x
end FunctorToTypes
def uliftTrivial (V : Type u) : ULift.{u} V ≅ V where
  hom a := a.1
  inv a := .up a
@[pp_with_univ]
def uliftFunctor : Type u ⥤ Type max u v where
  obj X := ULift.{v} X
  map {X} {_} f := fun x : ULift.{v} X => ULift.up (f x.down)
@[simp]
theorem uliftFunctor_obj {X : Type u} : uliftFunctor.obj.{v} X = ULift.{v} X :=
  rfl
@[simp]
theorem uliftFunctor_map {X Y : Type u} (f : X ⟶ Y) (x : ULift.{v} X) :
    uliftFunctor.map f x = ULift.up (f x.down) :=
  rfl
instance uliftFunctor_full : Functor.Full.{u} uliftFunctor where
  map_surjective f := ⟨fun x => (f (ULift.up x)).down, rfl⟩
instance uliftFunctor_faithful : uliftFunctor.Faithful where
  map_injective {_X} {_Y} f g p :=
    funext fun x =>
      congr_arg ULift.down (congr_fun p (ULift.up x) : ULift.up (f x) = ULift.up (g x))
def uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial
def homOfElement {X : Type u} (x : X) : PUnit ⟶ X := fun _ => x
theorem homOfElement_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => congr_fun H PUnit.unit, by aesop⟩
theorem mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono f).mp h
  · exact fun H => ⟨fun g g' h => H.comp_left h⟩
theorem injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf
theorem epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.symm.injective.comp_left.eq_iff]
    apply H
    change ULift.up ∘ g₁ ∘ f = ULift.up ∘ g₂ ∘ f
    rw [hg]
  · exact fun H => ⟨fun g g' h => H.injective_comp_right h⟩
theorem surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf
section
def ofTypeFunctor (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m] : Type u ⥤ Type v where
  obj := m
  map f := Functor.map f
  map_id := fun α => by funext X; apply id_map  
  map_comp f g := funext fun _ => LawfulFunctor.comp_map f g _
variable (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m]
@[simp]
theorem ofTypeFunctor_obj : (ofTypeFunctor m).obj = m :=
  rfl
@[simp]
theorem ofTypeFunctor_map {α β} (f : α → β) :
    (ofTypeFunctor m).map f = (Functor.map f : m α → m β) :=
  rfl
end
end CategoryTheory
namespace Equiv
universe u
variable {X Y : Type u}
def toIso (e : X ≃ Y) : X ≅ Y where
  hom := e.toFun
  inv := e.invFun
  hom_inv_id := funext e.left_inv
  inv_hom_id := funext e.right_inv
@[simp]
theorem toIso_hom {e : X ≃ Y} : e.toIso.hom = e :=
  rfl
@[simp]
theorem toIso_inv {e : X ≃ Y} : e.toIso.inv = e.symm :=
  rfl
end Equiv
universe u
namespace CategoryTheory.Iso
open CategoryTheory
variable {X Y : Type u}
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := congr_fun i.hom_inv_id x
  right_inv y := congr_fun i.inv_hom_id y
@[simp]
theorem toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X → Y) = i.hom :=
  rfl
@[simp]
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm : Y → X) = i.inv :=
  rfl
@[simp]
theorem toEquiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl
@[simp]
theorem toEquiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
    (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl
end CategoryTheory.Iso
namespace CategoryTheory
theorem isIso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom
instance : SplitEpiCategory (Type u) where
  isSplitEpi_of_epi f hf :=
    IsSplitEpi.mk' <|
      { section_ := Function.surjInv <| (epi_iff_surjective f).1 hf
        id := funext <| Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf }
end CategoryTheory
@[simps]
def equivIsoIso {X Y : Type u} : X ≃ Y ≅ X ≅ Y where
  hom e := e.toIso
  inv i := i.toEquiv
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y) :=
  equivIsoIso.toEquiv
@[simp]
theorem equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl
@[simp]
theorem equivEquivIso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl