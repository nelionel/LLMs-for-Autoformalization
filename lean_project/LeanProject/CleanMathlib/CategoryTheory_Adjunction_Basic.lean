import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Yoneda
namespace CategoryTheory
open Category
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  left_triangle_components (X : C) :
      F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) := by aesop_cat
  right_triangle_components (Y : D) :
      unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) := by aesop_cat
infixl:15 " ⊣ " => Adjunction
namespace Functor
class IsLeftAdjoint (left : C ⥤ D) : Prop where
  exists_rightAdjoint : ∃ (right : D ⥤ C), Nonempty (left ⊣ right)
class IsRightAdjoint (right : D ⥤ C) : Prop where
  exists_leftAdjoint : ∃ (left : C ⥤ D), Nonempty (left ⊣ right)
noncomputable def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  (IsRightAdjoint.exists_leftAdjoint (right := R)).choose
noncomputable def rightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : D ⥤ C :=
  (IsLeftAdjoint.exists_rightAdjoint (left := L)).choose
end Functor
noncomputable def Adjunction.ofIsLeftAdjoint (left : C ⥤ D) [left.IsLeftAdjoint] :
    left ⊣ left.rightAdjoint :=
  Functor.IsLeftAdjoint.exists_rightAdjoint.choose_spec.some
noncomputable def Adjunction.ofIsRightAdjoint (right : C ⥤ D) [right.IsRightAdjoint] :
    right.leftAdjoint ⊣ right :=
  Functor.IsRightAdjoint.exists_leftAdjoint.choose_spec.some
namespace Adjunction
attribute [reassoc (attr := simp)] left_triangle_components right_triangle_components
@[simps (config := .lemmasOnly)]
def homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) where
  toFun := fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp, assoc, ← Functor.comp_map, adj.counit.naturality, ← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_comp]
    rw [← assoc, ← Functor.comp_map, ← adj.unit.naturality]
    simp
alias homEquiv_unit := homEquiv_apply
alias homEquiv_counit := homEquiv_symm_apply
end Adjunction
attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit
namespace Adjunction
section
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
lemma isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
lemma isRightAdjoint (adj : F ⊣ G) : G.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
instance (R : D ⥤ C) [R.IsRightAdjoint] : R.leftAdjoint.IsLeftAdjoint :=
  (ofIsRightAdjoint R).isLeftAdjoint
instance (L : C ⥤ D) [L.IsLeftAdjoint] : L.rightAdjoint.IsRightAdjoint :=
  (ofIsLeftAdjoint L).isRightAdjoint
variable {X' X : C} {Y Y' : D}
theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp
theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp
theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  simp
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, eq_self_iff_true, homEquiv_naturality_left_symm]
theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  simp
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, eq_self_iff_true, Equiv.apply_symm_apply]
@[reassoc]
theorem homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right, w]
@[reassoc]
theorem homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm, w]
theorem homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') :
    (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k) ↔
      (F.map f ≫ g = h ≫ k) :=
  ⟨fun w ↦ by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩
theorem homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') :
    (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k) ↔
      (f ≫ g = h ≫ G.map k) :=
  ⟨fun w ↦ by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩
@[simp]
theorem left_triangle : whiskerRight adj.unit F ≫ whiskerLeft F adj.counit = 𝟙 _ := by
  ext; simp
@[simp]
theorem right_triangle : whiskerLeft G adj.unit ≫ whiskerRight adj.counit G = 𝟙 _ := by
  ext; simp
@[reassoc (attr := simp)]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f
@[reassoc (attr := simp)]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm
lemma unit_comp_map_eq_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.unit.app A ≫ G.map f = g ↔ f = F.map g ≫ adj.counit.app B :=
  ⟨fun h => by simp [← h], fun h => by simp [h]⟩
lemma eq_unit_comp_map_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.unit.app A ≫ G.map f ↔ F.map g ≫ adj.counit.app B = f :=
  ⟨fun h => by simp [h], fun h => by simp [← h]⟩
theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  unit_comp_map_eq_iff adj f g
theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  eq_unit_comp_map_iff adj f g
@[simps]
def corepresentableBy (X : C) :
    (G ⋙ coyoneda.obj (Opposite.op X)).CorepresentableBy (F.obj X) where
  homEquiv := adj.homEquiv _ _
  homEquiv_comp := by aesop_cat
@[simps]
def representableBy (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm
  homEquiv_comp := by aesop_cat
end
end Adjunction
namespace Adjunction
structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  unit : 𝟭 C ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭 D
  homEquiv_unit : ∀ {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f := by aesop_cat
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by aesop_cat
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  homEquiv_naturality_left_symm :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    aesop_cat
  homEquiv_naturality_right :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    aesop_cat
namespace CoreHomEquiv
attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right
variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp
end CoreHomEquiv
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  left_triangle :
    whiskerRight unit F ≫ (Functor.associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    aesop_cat
  right_triangle :
    whiskerLeft G unit ≫ (Functor.associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    aesop_cat
namespace CoreUnitCounit
attribute [simp] left_triangle right_triangle
end CoreUnitCounit
variable {F : C ⥤ D} {G : D ⥤ C}
attribute [local simp] CoreHomEquivUnitCounit.homEquiv_unit CoreHomEquivUnitCounit.homEquiv_counit
@[simps]
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit, (adj.homEquiv _ _).symm_apply_eq, adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit, ← (adj.homEquiv _ _).eq_symm_apply, adj.homEquiv_counit]
    simp
lemma mk'_homEquiv (adj : CoreHomEquivUnitCounit F G) : (mk' adj).homEquiv = adj.homEquiv := by
  ext
  rw [homEquiv_unit, adj.homEquiv_unit, mk'_unit]
@[simps!]
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm] }
    homEquiv := adj.homEquiv
    homEquiv_unit := fun {X Y f} => by simp [← adj.homEquiv_naturality_right]
    homEquiv_counit := fun {X Y f} => by simp [← adj.homEquiv_naturality_left_symm] }
@[simp]
lemma mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) :
    (mkOfHomEquiv adj).homEquiv = adj.homEquiv := by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]
@[simps!]
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.right_triangle] using this Y
def id : 𝟭 C ⊣ 𝟭 C where
  unit := 𝟙 _
  counit := 𝟙 _
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩
@[simps]
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp
@[simps]
def equivHomsetRightOfNatIso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} :
    (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) where
  toFun f := f ≫ iso.hom.app _
  invFun g := g ≫ iso.inv.app _
  left_inv f := by simp
  right_inv g := by simp
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (equivHomsetLeftOfNatIso iso.symm).trans (adj.homEquiv X Y) }
def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (adj.homEquiv X Y).trans (equivHomsetRightOfNatIso iso) }
@[simps!]
def compYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm
@[simps!]
def compCoyonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    F.op ⋙ coyoneda ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso
section
variable {E : Type u₃} [ℰ : Category.{v₃} E] {H : D ⥤ E} {I : E ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
def comp : F ⋙ H ⊣ I ⋙ G :=
  mk' {
    homEquiv := fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ (whiskerLeft F <| whiskerRight adj₂.unit G) ≫ (Functor.associator _ _ _).inv
    counit :=
      (Functor.associator _ _ _).hom ≫ (whiskerLeft I <| whiskerRight adj₁.counit H) ≫ adj₂.counit }
@[simp, reassoc]
lemma comp_unit_app (X : C) :
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) := by
  simp [Adjunction.comp]
@[simp, reassoc]
lemma comp_counit_app (X : E) :
    (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]
lemma comp_homEquiv :  (adj₁.comp adj₂).homEquiv =
    fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _) :=
  mk'_homEquiv _
end
section ConstructLeft
variable {F_obj : C → D}
variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
@[simps!]
def leftAdjointOfEquiv (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g) : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc, ← he, id_comp, Equiv.apply_symm_apply]
    simp
variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
@[simps!]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq, he]; simp
        simp [← this, ← Equiv.apply_eq_iff_eq (e X' Y), ← he] }
end ConstructLeft
section ConstructRight
variable {G_obj : D → C}
variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
private theorem he'' (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
    {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply, he]; simp
@[simps!]
def rightAdjointOfEquiv (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply, ← he'' e he, Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc, he'' e he, comp_id, Equiv.symm_apply_apply]
    simp
@[simps!]
def adjunctionOfEquivRight (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) :
    F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }
end ConstructRight
@[simps!]
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.unit.app X)]
    [∀ Y, IsIso (adj.counit.app Y)] : C ≌ D where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)
end Adjunction
open Adjunction
lemma Functor.isEquivalence_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofIsRightAdjoint G).unit.app X)]
    [∀ Y, IsIso ((Adjunction.ofIsRightAdjoint G).counit.app Y)] : G.IsEquivalence :=
  (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse
namespace Equivalence
variable (e : C ≌ D)
@[simps]
def toAdjunction : e.functor ⊣ e.inverse where
  unit := e.unit
  counit := e.counit
lemma isLeftAdjoint_functor : e.functor.IsLeftAdjoint where
  exists_rightAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩
lemma isRightAdjoint_inverse : e.inverse.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩
lemma isLeftAdjoint_inverse : e.inverse.IsLeftAdjoint :=
  e.symm.isLeftAdjoint_functor
lemma isRightAdjoint_functor : e.functor.IsRightAdjoint :=
  e.symm.isRightAdjoint_inverse
end Equivalence
namespace Functor
instance isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩
instance isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  exists_leftAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩
lemma isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] :
    IsRightAdjoint G where
  exists_leftAdjoint := ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩
lemma isLeftAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [IsLeftAdjoint F] :
    IsLeftAdjoint G where
  exists_rightAdjoint := ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).ofNatIsoLeft h⟩⟩
noncomputable def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction
instance (priority := 10) isLeftAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsLeftAdjoint F :=
  F.asEquivalence.isLeftAdjoint_functor
instance (priority := 10) isRightAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsRightAdjoint F :=
  F.asEquivalence.isRightAdjoint_functor
end Functor
end CategoryTheory