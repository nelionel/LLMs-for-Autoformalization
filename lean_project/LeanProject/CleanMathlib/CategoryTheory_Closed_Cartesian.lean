import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Closed.Monoidal
universe v v₂ u u₂
noncomputable section
namespace CategoryTheory
open Category Limits MonoidalCategory
abbrev Exponentiable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] (X : C) :=
  Closed X
abbrev Exponentiable.mk {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] (X : C)
    (exp : C ⥤ C) (adj : MonoidalCategory.tensorLeft X ⊣ exp) :
    Exponentiable X where
  adj := adj
def binaryProductExponentiable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] {X Y : C}
    (hX : Exponentiable X) (hY : Exponentiable Y) : Exponentiable (X ⊗ Y) :=
  tensorClosed hX hY
def terminalExponentiable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] :
    Exponentiable (𝟙_ C) :=
  unitClosed
abbrev CartesianClosed (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :=
  MonoidalClosed C
def CartesianClosed.mk (C : Type u) [Category.{v} C] [ChosenFiniteProducts C]
    (exp : ∀ (X : C), Exponentiable X) :
    CartesianClosed C where
  closed X := exp X
variable {C : Type u} [Category.{v} C] (A B : C) {X X' Y Y' Z : C}
variable [ChosenFiniteProducts C] [Exponentiable A]
abbrev exp : C ⥤ C :=
  ihom A
namespace exp
abbrev adjunction : tensorLeft A ⊣ exp A :=
  ihom.adjunction A
abbrev ev : exp A ⋙ tensorLeft A ⟶ 𝟭 C :=
  ihom.ev A
abbrev coev : 𝟭 C ⟶ tensorLeft A ⋙ exp A :=
  ihom.coev A
set_option quotPrecheck false in
notation:20 A " ⟹ " B:19 => (exp A).obj B
open Lean PrettyPrinter.Delaborator SubExpr in
@[delab app.Prefunctor.obj]
def delabPrefunctorObjExp : Delab := whenPPOption getPPNotation <| withOverApp 6 <| do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Prefunctor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``Functor.toPrefunctor 5
    withNaryArg 4 do
      let e ← getExpr
      guard <| e.isAppOfArity' ``exp 5
      withNaryArg 2 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)
set_option quotPrecheck false in
notation:30 B " ^^ " A:30 => (exp A).obj B
@[reassoc]
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B : C) :=
  ihom.ev_coev A B
@[reassoc]
theorem coev_ev : (coev A).app (A ⟹ B) ≫ (exp A).map ((ev A).app B) = 𝟙 (A ⟹ B) :=
  ihom.coev_ev A B
end exp
instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits
variable {A}
namespace CartesianClosed
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
  (exp.adjunction A).homEquiv _ _
def uncurry : (Y ⟶ A ⟹ X) → (A ⊗ Y ⟶ X) :=
  ((exp.adjunction A).homEquiv _ _).symm
@[simp, nolint simpNF]
theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (exp.adjunction A).homEquiv _ _ f = curry f :=
  rfl
@[simp, nolint simpNF]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟹ X) :
    ((exp.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl
@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) :
    curry (_ ◁ f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _
@[reassoc]
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (exp _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _
@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟹ Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (exp _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _
@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟹ Y) :
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _
@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f
@[simp]
theorem curry_uncurry (f : X ⟶ A ⟹ Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f
theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟹ X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (exp.adjunction A) f g
theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟹ X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (exp.adjunction A) f g
theorem uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = (A ◁ g) ≫ (exp.ev A).app X :=
  rfl
theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (exp.coev A).app Y ≫ (exp A).map g :=
  rfl
theorem uncurry_id_eq_ev (A X : C) [Exponentiable A] : uncurry (𝟙 (A ⟹ X)) = (exp.ev A).app X := by
  rw [uncurry_eq, whiskerLeft_id_assoc]
theorem curry_id_eq_coev (A X : C) [Exponentiable A] : curry (𝟙 _) = (exp.coev A).app X := by
  rw [curry_eq, (exp A).map_id (A ⊗ _)]; apply comp_id
theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
  (Closed.adj.homEquiv _ _).injective
theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟹ X) → (A ⊗ Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective
end CartesianClosed
open CartesianClosed
def expUnitNatIso [Exponentiable (𝟙_ C)] : 𝟭 C ≅ exp (𝟙_ C) :=
  MonoidalClosed.unitNatIso (C := C)
def expUnitIsoSelf [Exponentiable (𝟙_ C)] : (𝟙_ C) ⟹ X ≅ X :=
  (expUnitNatIso.app X).symm
def internalizeHom (f : A ⟶ Y) : ⊤_ C ⟶ A ⟹ Y :=
  CartesianClosed.curry (ChosenFiniteProducts.fst _ _ ≫ f)
section Pre
variable {B}
def pre (f : B ⟶ A) [Exponentiable B] : exp A ⟶ exp B :=
  conjugateEquiv (exp.adjunction _) (exp.adjunction _) ((tensoringLeft _).map f)
theorem prod_map_pre_app_comp_ev (f : B ⟶ A) [Exponentiable B] (X : C) :
    (B ◁ (pre f).app X) ≫ (exp.ev B).app X =
      f ▷ (A ⟹ X) ≫ (exp.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft _).map f) X
theorem uncurry_pre (f : B ⟶ A) [Exponentiable B] (X : C) :
    CartesianClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (exp.ev A).app X := by
  rw [uncurry_eq, prod_map_pre_app_comp_ev]
theorem coev_app_comp_pre_app (f : B ⟶ A) [Exponentiable B] :
    (exp.coev A).app X ≫ (pre f).app (A ⊗ X) =
      (exp.coev B).app X ≫ (exp B).map (f ⊗ 𝟙 _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft _).map f) X
@[simp]
theorem pre_id (A : C) [Exponentiable A] : pre (𝟙 A) = 𝟙 _ := by
  simp only [pre, Functor.map_id]
  aesop_cat
@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Exponentiable A₁] [Exponentiable A₂] [Exponentiable A₃]
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) : pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp]
  simp
end Pre
def internalHom [CartesianClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := exp X.unop
  map f := pre f.unop
@[simps]
def zeroMul {I : C} (t : IsInitial I) : A ⊗ I ≅ I where
  hom := ChosenFiniteProducts.snd _ _
  inv := t.to _
  hom_inv_id := by
    have : ChosenFiniteProducts.snd A I = CartesianClosed.uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _
def mulZero {I : C} (t : IsInitial I) : I ⊗ A ≅ I :=
  β_ _ _ ≪≫ zeroMul t
def powZero {I : C} (t : IsInitial I) [CartesianClosed C] : I ⟹ B ≅ ⊤_ C where
  hom := default
  inv := CartesianClosed.curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext
def prodCoprodDistrib [HasBinaryCoproducts C] [CartesianClosed C] (X Y Z : C) :
    (Z ⊗ X) ⨿ Z ⊗ Y ≅ Z ⊗ (X ⨿ Y) where
  hom := coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
  inv :=
    CartesianClosed.uncurry
      (coprod.desc (CartesianClosed.curry coprod.inl) (CartesianClosed.curry coprod.inr))
  hom_inv_id := by
    ext
    · rw [coprod.inl_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inl_desc, uncurry_curry]
    rw [coprod.inr_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inr_desc, uncurry_curry]
  inv_hom_id := by
    rw [← uncurry_natural_right, ← eq_curry_iff]
    ext
    · rw [coprod.inl_desc_assoc, ← curry_natural_right, coprod.inl_desc, ← curry_natural_left,
        comp_id]
    rw [coprod.inr_desc_assoc, ← curry_natural_right, coprod.inr_desc, ← curry_natural_left,
      comp_id]
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : Mono f := by
    rw [← ChosenFiniteProducts.lift_snd (𝟙 A) f, ← zeroMul_hom t]
    exact mono_comp _ _
  haveI : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi
instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [CartesianClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩
instance Initial.mono_to [HasInitial C] (B : C) [CartesianClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial
variable {D : Type u₂} [Category.{v₂} D]
section Functor
variable [ChosenFiniteProducts D]
def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D :=
  letI := e.inverse.monoidalOfChosenFiniteProducts
  MonoidalClosed.ofEquiv (e.inverse) e.symm.toAdjunction
end Functor
attribute [nolint simpNF] CategoryTheory.CartesianClosed.homEquiv_apply_eq
  CategoryTheory.CartesianClosed.homEquiv_symm_apply_eq
end CategoryTheory