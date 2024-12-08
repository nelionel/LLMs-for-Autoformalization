import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.NatIso
namespace CategoryTheory
namespace Sigma
universe w₁ w₂ w₃ v₁ v₂ u₁ u₂
variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
inductive SigmaHom : (Σi, C i) → (Σi, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → SigmaHom ⟨i, X⟩ ⟨i, Y⟩
namespace SigmaHom
def id : ∀ X : Σi, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)
instance (X : Σi, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩
def comp : ∀ {X Y Z : Σi, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)
instance : CategoryStruct (Σi, C i) where
  Hom := SigmaHom
  id := id
  comp f g := comp f g
@[simp]
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl
lemma assoc : ∀ {X Y Z W : Σi, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk _, mk _, mk _ => congr_arg mk (Category.assoc _ _ _)
lemma id_comp : ∀ {X Y : Σi, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk _ => congr_arg mk (Category.id_comp _)
lemma comp_id : ∀ {X Y : Σi, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk _ => congr_arg mk (Category.comp_id _)
end SigmaHom
instance sigma : Category (Σi, C i) where
  id_comp := SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc
@[simps map]
def incl (i : I) : C i ⥤ Σi, C i where
  obj X := ⟨i, X⟩
  map := SigmaHom.mk
@[simp]
lemma incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl
instance (i : I) : Functor.Full (incl i : C i ⥤ Σi, C i) where
  map_surjective := fun ⟨f⟩ => ⟨f, rfl⟩
instance (i : I) : Functor.Faithful (incl i : C i ⥤ Σi, C i) where
  map_injective {_ _ _ _} h := by injection h
section
variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)
def natTrans {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality
@[simp]
lemma natTrans_app {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl
def descMap : ∀ X Y : Σi, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, SigmaHom.mk g => (F _).map g
@[simps obj]
def desc : (Σi, C i) ⥤ D where
  obj X := (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp
@[simp]
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents fun _ => Iso.refl _
@[simp]
lemma inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).obj X) :=
  rfl
@[simp]
lemma inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl
def descUniq (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f
@[simp]
lemma descUniq_hom_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X :=
  rfl
@[simp]
lemma descUniq_inv_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl
@[simps]
def natIso {q₁ q₂ : (Σi, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  hom := natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv
end
section
variable (C) {J : Type w₂} (g : J → I)
def map : (Σj : J, C (g j)) ⥤ Σi : I, C i :=
  desc fun j => incl (g j)
@[simp]
lemma map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl
@[simp]
lemma map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl
@[simps!]
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _
variable (I)
@[simps!]
def mapId : map C (id : I → I) ≅ 𝟭 (Σi, C i) :=
  natIso fun i => NatIso.ofComponents fun _ => Iso.refl _
variable {I} {K : Type w₃}
@[simps!]
def mapComp (f : K → J) (g : J → I) : map (fun x ↦ C (g x)) f ⋙ (map C g : _) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (isoWhiskerRight (inclCompMap (fun i => C (g i)) f k) (map C g : _) : _) ≪≫ inclCompMap _ _ _
end
namespace Functor
variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
def sigma (F : ∀ i, C i ⥤ D i) : (Σi, C i) ⥤ Σi, D i :=
  desc fun i => F i ⋙ incl i
end Functor
namespace natTrans
variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
variable {F G : ∀ i, C i ⥤ D i}
def sigma (α : ∀ i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where
  app f := SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]
end natTrans
end Sigma
end CategoryTheory