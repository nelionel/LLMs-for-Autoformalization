import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
namespace CategoryTheory
open Category
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C]
namespace Monad
structure Algebra (T : Monad C) : Type max u₁ v₁ where
  A : C
  a : (T : C ⥤ C).obj A ⟶ A
  unit : T.η.app A ≫ a = 𝟙 A := by aesop_cat
  assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by aesop_cat
attribute [reassoc] Algebra.unit Algebra.assoc
namespace Algebra
variable {T : Monad C}
@[ext]
structure Hom (A B : Algebra T) where
  f : A.A ⟶ B.A
  h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f := by aesop_cat
attribute [reassoc (attr := simp)] Hom.h
namespace Hom
def id (A : Algebra T) : Hom A A where f := 𝟙 A.A
instance (A : Algebra T) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩
def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
end Hom
instance : CategoryStruct (Algebra T) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _
@[ext]
lemma Hom.ext' (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h
@[simp]
theorem comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl
@[simp]
theorem id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A :=
  rfl
@[simp]
theorem id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl
@[simp]
theorem comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl
instance eilenbergMoore : Category (Algebra T) where
@[simps]
def isoMk {A B : Algebra T} (h : A.A ≅ B.A)
    (w : (T : C ⥤ C).map h.hom ≫ B.a = A.a ≫ h.hom := by aesop_cat) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }
end Algebra
variable (T : Monad C)
@[simps]
def forget : Algebra T ⥤ C where
  obj A := A.A
  map f := f.f
@[simps]
def free : C ⥤ Algebra T where
  obj X :=
    { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }
instance [Inhabited C] : Inhabited (Algebra T) :=
  ⟨(free T).obj default⟩
@[simps! unit counit]
def adj : T.free ⊣ T.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by
                dsimp
                simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            dsimp
            simp
          right_inv := fun f => by
            dsimp only [forget_obj]
            rw [← T.η.naturality_assoc, Y.unit]
            apply Category.comp_id } }
theorem algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{   f := inv f.f
        h := by
          rw [IsIso.eq_comp_inv f.f, Category.assoc, ← f.h]
          simp },
      by aesop_cat⟩⟩
instance forget_reflects_iso : T.forget.ReflectsIsomorphisms where
  reflects {_ _} f := fun [IsIso f.f] => algebra_iso_of_iso T f
instance forget_faithful : T.forget.Faithful where
theorem algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget T).epi_of_epi_map h
theorem algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget T).mono_of_mono_map h
instance : T.forget.IsRightAdjoint  :=
  ⟨T.free, ⟨T.adj⟩⟩
@[simps]
def algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Algebra T₂ where
  obj A :=
    { A := A.A
      a := h.app A.A ≫ A.a
      unit := by
        dsimp
        simp [A.unit]
      assoc := by
        dsimp
        simp [A.assoc] }
  map f := { f := f.f }
@[simps (config := { rhsMd := .default })]
def algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)
@[simps (config := { rhsMd := .default })]
def algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFunctorOfMonadHom f :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)
@[simps (config := { rhsMd := .default })]
def algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
    algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)
@[simps]
def algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Algebra T₂ where
  functor := algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomId
@[simp]
theorem algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) :
    algebraFunctorOfMonadHom h ⋙ forget _ = forget _ :=
  rfl
end Monad
namespace Comonad
structure Coalgebra (G : Comonad C) : Type max u₁ v₁ where
  A : C
  a : A ⟶ (G : C ⥤ C).obj A
  counit : a ≫ G.ε.app A = 𝟙 A := by aesop_cat
  coassoc : a ≫ G.δ.app A = a ≫ G.map a := by aesop_cat
attribute [reassoc] Coalgebra.counit Coalgebra.coassoc
namespace Coalgebra
variable {G : Comonad C}
@[ext]
structure Hom (A B : Coalgebra G) where
  f : A.A ⟶ B.A
  h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a := by aesop_cat
attribute [reassoc (attr := simp)] Hom.h
namespace Hom
def id (A : Coalgebra G) : Hom A A where f := 𝟙 A.A
def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
end Hom
instance : CategoryStruct (Coalgebra G) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _
@[ext]
lemma Hom.ext' (X Y : Coalgebra G) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h
@[simp]
theorem comp_eq_comp {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
    Coalgebra.Hom.comp f g = f ≫ g :=
  rfl
@[simp]
theorem id_eq_id (A : Coalgebra G) : Coalgebra.Hom.id A = 𝟙 A :=
  rfl
@[simp]
theorem id_f (A : Coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl
@[simp]
theorem comp_f {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl
instance eilenbergMoore : Category (Coalgebra G) where
@[simps]
def isoMk {A B : Coalgebra G} (h : A.A ≅ B.A)
    (w : A.a ≫ (G : C ⥤ C).map h.hom = h.hom ≫ B.a := by aesop_cat) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp, ← reassoc_of% w, ← Functor.map_comp]
        simp }
end Coalgebra
variable (G : Comonad C)
@[simps]
def forget : Coalgebra G ⥤ C where
  obj A := A.A
  map f := f.f
@[simps]
def cofree : C ⥤ Coalgebra G where
  obj X :=
    { A := G.obj X
      a := G.δ.app X
      coassoc := (G.coassoc _).symm }
  map f :=
    { f := G.map f
      h := (G.δ.naturality _).symm }
@[simps! unit counit]
def adj : G.forget ⊣ G.cofree :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h := by
                dsimp
                simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc, G.ε.naturality, Functor.id_map, X.counit_assoc]
          right_inv := fun g => by
            ext1; dsimp
            rw [Functor.map_comp, g.h_assoc, cofree_obj_a, Comonad.right_counit]
            apply comp_id } }
theorem coalgebra_iso_of_iso {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{   f := inv f.f
        h := by
          rw [IsIso.eq_inv_comp f.f, ← f.h_assoc]
          simp },
      by aesop_cat⟩⟩
instance forget_reflects_iso : G.forget.ReflectsIsomorphisms where
  reflects {_ _} f := fun [IsIso f.f] => coalgebra_iso_of_iso G f
instance forget_faithful : (forget G).Faithful where
theorem algebra_epi_of_epi {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget G).epi_of_epi_map h
theorem algebra_mono_of_mono {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget G).mono_of_mono_map h
instance : G.forget.IsLeftAdjoint  :=
  ⟨_, ⟨G.adj⟩⟩
end Comonad
end CategoryTheory