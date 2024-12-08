import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Conj
universe u v
open CategoryTheory Limits
variable (V : Type (u + 1)) [LargeCategory V]
structure Action (G : MonCat.{u}) where
  V : V
  ρ : G ⟶ MonCat.of (End V)
namespace Action
variable {V}
@[simp 1100]
theorem ρ_one {G : MonCat.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V := by rw [MonoidHom.map_one]; rfl
@[simps]
def ρAut {G : Grp.{u}} (A : Action V (MonCat.of G)) : G ⟶ Grp.of (Aut A.V) where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)
attribute [nolint simpNF] Action.ρAut_apply_inv Action.ρAut_apply_hom
variable (G : MonCat.{u})
section
instance inhabited' : Inhabited (Action (Type u) G) :=
  ⟨⟨PUnit, 1⟩⟩
def trivial : Action AddCommGrp G where
  V := AddCommGrp.of PUnit
  ρ := 1
instance : Inhabited (Action AddCommGrp G) :=
  ⟨trivial G⟩
end
variable {G}
@[ext]
structure Hom (M N : Action V G) where
  hom : M.V ⟶ N.V
  comm : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by aesop_cat
namespace Hom
attribute [reassoc] comm
attribute [local simp] comm comm_assoc
@[simps]
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V
instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩
@[simps]
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom
end Hom
instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g
@[ext]
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext h
@[simp]
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl
@[simp]
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl
@[simp]
theorem hom_inv_hom {M N : Action V G} (f : M ≅ N) :
    f.hom.hom ≫ f.inv.hom = 𝟙 M.V := by
  rw [← comp_hom, Iso.hom_inv_id, id_hom]
@[simp]
theorem inv_hom_hom {M N : Action V G} (f : M ≅ N) :
    f.inv.hom ≫ f.hom.hom = 𝟙 N.V := by
  rw [← comp_hom, Iso.inv_hom_id, id_hom]
@[simps]
def mkIso {M N : Action V G} (f : M.V ≅ N.V)
    (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g := by aesop_cat) : M ≅ N where
  hom :=
    { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }
instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := (mkIso (asIso f.hom) f.comm).isIso_hom
instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  (mkIso (asIso f) w).isIso_hom
instance {M N : Action V G} (f : M ≅ N) : IsIso f.hom.hom where
  out := ⟨f.inv.hom, by simp⟩
instance {M N : Action V G} (f : M ≅ N) : IsIso f.inv.hom where
  out := ⟨f.hom.hom, by simp⟩
namespace FunctorCategoryEquivalence
@[simps]
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj M :=
    { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }
@[simps]
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }
@[simps!]
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _
end FunctorCategoryEquivalence
section
open FunctorCategoryEquivalence
variable (V G)
@[simps]
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
instance : (FunctorCategoryEquivalence.functor (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_functor
instance : (FunctorCategoryEquivalence.inverse (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_inverse
end
section Forget
variable (V G)
@[simps]
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom
instance : (forget V G).Faithful where map_injective w := Hom.ext w
instance [ConcreteCategory V] : ConcreteCategory (Action V G) where
  forget := forget V G ⋙ ConcreteCategory.forget
instance hasForgetToV [ConcreteCategory V] : HasForget₂ (Action V G) V where forget₂ := forget V G
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _
noncomputable instance preservesLimits_forget [HasLimits V] :
    PreservesLimits (forget V G) :=
  Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)
noncomputable instance preservesColimits_forget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)
end Forget
theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by
      rw [Iso.conj_apply, Iso.eq_inv_comp]; simp [f.hom.comm]
def actionPunitEquivalence : Action V (MonCat.of PUnit) ≌ V where
  functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [MonCat.oneHom_apply, MonCat.one_of, End.one_def, id_eq, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _
variable (V)
@[simps]
def res {G H : MonCat} (f : G ⟶ H) : Action V H ⥤ Action V G where
  obj M :=
    { V := M.V
      ρ := f ≫ M.ρ }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }
@[simps!]
def resId {G : MonCat} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
@[simps!]
def resComp {G H K : MonCat} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)
end Action
namespace CategoryTheory.Functor
variable {V} {W : Type (u + 1)} [LargeCategory W]
@[simps]
def mapAction (F : V ⥤ W) (G : MonCat.{u}) : Action V G ⥤ Action W G where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp only [End.one_def, Action.ρ_one, F.map_id, MonCat.one_of]
          map_mul' := fun g h => by
            dsimp
            rw [map_mul, MonCat.mul_of, End.mul_def, End.mul_def, F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]
end CategoryTheory.Functor