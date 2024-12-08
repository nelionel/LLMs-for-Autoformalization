import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Products.Unitor
namespace CategoryTheory
open Category
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {A' : Type u₄} [Category.{v₄} A']
variable {B' : Type u₅} [Category.{v₅} B']
variable {T' : Type u₆} [Category.{v₆} T']
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  left : A
  right : B
  hom : L.obj left ⟶ R.obj right
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 default }
variable {L : A ⥤ T} {R : B ⥤ T}
@[ext]
structure CommaMorphism (X Y : Comma L R) where
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right := by aesop_cat
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
    ⟨{ left := 𝟙 _, right := 𝟙 _}⟩
attribute [reassoc (attr := simp)] CommaMorphism.w
instance commaCategory : Category (Comma L R) where
  Hom X Y := CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }
namespace Comma
section
variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}
@[ext]
lemma hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f = g :=
  CommaMorphism.ext h₁ h₂
@[simp]
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl
@[simp]
theorem id_right : (𝟙 X : CommaMorphism X X).right = 𝟙 X.right :=
  rfl
@[simp]
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl
@[simp]
theorem comp_right : (f ≫ g).right = f.right ≫ g.right :=
  rfl
end
variable (L) (R)
@[simps]
def fst : Comma L R ⥤ A where
  obj X := X.left
  map f := f.left
@[simps]
def snd : Comma L R ⥤ B where
  obj X := X.right
  map f := f.right
@[simps]
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.hom
@[simp]
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl
@[simp]
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.right (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl
section
variable {L R} {X Y : Comma L R} (e : X ⟶ Y)
instance [IsIso e] : IsIso e.left :=
  (Comma.fst L R).map_isIso e
instance [IsIso e] : IsIso e.right :=
  (Comma.snd L R).map_isIso e
@[simp]
lemma inv_left [IsIso e] : (inv e).left = inv e.left := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_left, IsIso.hom_inv_id, id_left]
@[simp]
lemma inv_right [IsIso e] : (inv e).right = inv e.right := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_right, IsIso.hom_inv_id, id_right]
lemma left_hom_inv_right [IsIso e] : L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right) = X.hom := by
  simp
lemma inv_left_hom_right [IsIso e] : L.map (inv e.left) ≫ X.hom ≫ R.map e.right = Y.hom := by
  simp
end
section
variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}
@[simps!]
def leftIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.left ≅ Y.left := (fst L₁ R₁).mapIso α
@[simps!]
def rightIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.right ≅ Y.right := (snd L₁ R₁).mapIso α
@[simps]
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom := by aesop_cat) : X ≅ Y where
  hom :=
    { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l, Iso.inv_comp_eq, L₁.mapIso_hom, ← Category.assoc, h,
          Category.assoc, ← R₁.map_comp]
        simp }
section
variable {L R}
variable {L' : A' ⥤ T'} {R' : B' ⥤ T'}
  {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')
@[simps]
def map : Comma L R ⥤ Comma L' R' where
  obj X :=
    { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc, assoc]
        erw [α.naturality_assoc, ← β.naturality]
        dsimp
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, φ.w] }
instance faithful_map [F₁.Faithful] [F₂.Faithful] : (map α β).Faithful where
  map_injective {X Y} f g h := by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)
instance full_map [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β] : (map α β).Full where
  map_surjective {X Y} φ :=
   ⟨{ left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _), ← cancel_epi (α.app _), F.map_comp, F.map_comp,
          assoc, assoc]
        erw [← α.naturality_assoc, β.naturality]
        dsimp
        rw [F₁.map_preimage, F₂.map_preimage]
        simpa using φ.w) }, by aesop_cat⟩
instance essSurj_map [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] :
    (map α β).EssSurj where
  mem_essImage X :=
    ⟨{  left := F₁.objPreimage X.left
        right := F₂.objPreimage X.right
        hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
          X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
            ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso X.right) (by
              dsimp
              simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.map_preimage, assoc,
                IsIso.inv_hom_id, comp_id, IsIso.hom_inv_id_assoc]
              rw [← R'.map_comp, Iso.inv_hom_id, R'.map_id, comp_id])⟩⟩
noncomputable instance isEquivalenceMap
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F.Faithful] [F.Full] [IsIso α] [IsIso β] :
    (map α β).IsEquivalence where
@[simp]
theorem map_fst : map α β ⋙ fst L' R' = fst L R ⋙ F₁ :=
  rfl
@[simps!]
def mapFst : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)
@[simp]
theorem map_snd : map α β ⋙ snd L' R' = snd L R ⋙ F₂ :=
  rfl
@[simps!]
def mapSnd : map α β ⋙ snd L' R' ≅ snd L R ⋙ F₂ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)
end
@[simps]
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where
  obj X :=
    { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }
@[simps!]
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
    mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapLeftEq (l l' : L₁ ⟶ L₂) (h : l = l') : mapLeft R l ≅ mapLeft R l' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapLeftIso (i : L₁ ≅ L₂) : Comma L₁ R ≌ Comma L₂ R where
  functor := mapLeft _ i.inv
  inverse := mapLeft _ i.hom
  unitIso := (mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _
  counitIso := (mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _
@[simps]
def mapRight (r : R₁ ⟶ R₂) : Comma L R₁ ⥤ Comma L R₂ where
  obj X :=
    { left := X.left
      right := X.right
      hom := X.hom ≫ r.app X.right }
  map f :=
    { left := f.left
      right := f.right }
@[simps!]
def mapRightId : mapRight L (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapRightComp (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) :
    mapRight L (r ≫ r') ≅ mapRight L r ⋙ mapRight L r' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapRightEq (r r' : R₁ ⟶ R₂) (h : r = r') : mapRight L r ≅ mapRight L r' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
@[simps!]
def mapRightIso (i : R₁ ≅ R₂) : Comma L R₁ ≌ Comma L R₂ where
  functor := mapRight _ i.hom
  inverse := mapRight _ i.inv
  unitIso := (mapRightId _ _).symm ≪≫ mapRightEq _ _ _ i.hom_inv_id.symm ≪≫ mapRightComp _ _ _
  counitIso := (mapRightComp _ _ _).symm ≪≫ mapRightEq _ _ _ i.inv_hom_id ≪≫ mapRightId _ _
end
section
variable {C : Type u₄} [Category.{v₄} C]
@[simps]
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using f.w }
def preLeftIso (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    preLeft F L R ≅ map (F ⋙ L).rightUnitor.inv (R.rightUnitor.hom ≫ R.leftUnitor.inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Faithful] : (preLeft F L R).Faithful :=
  Functor.Faithful.of_iso (preLeftIso F L R).symm
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Full] : (preLeft F L R).Full :=
  Functor.Full.of_iso (preLeftIso F L R).symm
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.EssSurj] : (preLeft F L R).EssSurj :=
  Functor.essSurj_of_iso (preLeftIso F L R).symm
instance isEquivalence_preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence] :
    (preLeft F L R).IsEquivalence where
@[simps]
def preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) : Comma L (F ⋙ R) ⥤ Comma L R where
  obj X :=
    { left := X.left
      right := F.obj X.right
      hom := X.hom }
  map f :=
    { left := f.left
      right := F.map f.right }
def preRightIso (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) :
    preRight L F R ≅ map (L.leftUnitor.hom ≫ L.rightUnitor.inv) (F ⋙ R).rightUnitor.hom :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.Faithful] : (preRight L F R).Faithful :=
  Functor.Faithful.of_iso (preRightIso L F R).symm
instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.Full] : (preRight L F R).Full :=
  Functor.Full.of_iso (preRightIso L F R).symm
instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.EssSurj] : (preRight L F R).EssSurj :=
  Functor.essSurj_of_iso (preRightIso L F R).symm
instance isEquivalence_preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.IsEquivalence] :
    (preRight L F R).IsEquivalence where
@[simps]
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F) where
  obj X :=
    { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }
def postIso (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) :
    post L R F ≅ map (F₁ := 𝟭 _) (F₂ := 𝟭 _) (L ⋙ F).leftUnitor.hom (R ⋙ F).leftUnitor.inv :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : (post L R F).Faithful :=
  Functor.Faithful.of_iso (postIso L R F).symm
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Faithful] : (post L R F).Full :=
  Functor.Full.of_iso (postIso L R F).symm
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Full] : (post L R F).EssSurj :=
  Functor.essSurj_of_iso (postIso L R F).symm
instance isEquivalence_post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.IsEquivalence] :
    (post L R F).IsEquivalence where
@[simps]
def fromProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    A × B ⥤ Comma L R where
  obj X :=
    { left := X.1
      right := X.2
      hom := Discrete.eqToHom rfl }
  map {X} {Y} f :=
    { left := f.1
      right := f.2 }
@[simps!]
def equivProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ A × B where
  functor := (fst L R).prod' (snd L R)
  inverse := fromProd L R
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps!]
def toPUnitIdEquiv (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUnit) :
    Comma L R ≌ A :=
  (equivProd L _).trans (prod.rightUnitorEquivalence A)
@[simp]
theorem toPUnitIdEquiv_functor_iso {L : A ⥤ Discrete PUnit}
    {R : Discrete PUnit ⥤ Discrete PUnit} :
    (toPUnitIdEquiv L R).functor = fst L R :=
  rfl
@[simps!]
def toIdPUnitEquiv (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ B :=
  (equivProd _ R).trans (prod.leftUnitorEquivalence B)
@[simp]
theorem toIdPUnitEquiv_functor_iso {L : Discrete PUnit ⥤ Discrete PUnit}
    {R : B ⥤ Discrete PUnit} :
    (toIdPUnitEquiv L R).functor = snd L R :=
  rfl
end
section Opposite
open Opposite
@[simps]
def opFunctor : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where
  obj X := ⟨op X.right, op X.left, op X.hom⟩
  map f := ⟨op f.right, op f.left, Quiver.Hom.unop_inj (by simp)⟩
@[simps!]
def opFunctorCompFst : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op :=
  Iso.refl _
@[simps!]
def opFunctorCompSnd : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op :=
  Iso.refl _
@[simps]
def unopFunctor : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  obj X := ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using f.w.symm)⟩
@[simps!]
def unopFunctorCompFst : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _ :=
  Iso.refl _
@[simps!]
def unopFunctorCompSnd : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _ :=
  Iso.refl _
@[simps]
def opEquiv : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where
  functor := opFunctor L R
  inverse := (unopFunctor R L).leftOp
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
end Opposite
end Comma
end CategoryTheory