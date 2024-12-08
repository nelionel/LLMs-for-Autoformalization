import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.Functor.Const
universe v₁ u₁ v₂ u₂ v₃ u₃
namespace CategoryTheory
open IsHomLift
namespace Functor
variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := { a : 𝒳 // p.obj a = S }
namespace Fiber
variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}
instance fiberCategory : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩
def fiberInclusion : Fiber p S ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1
instance {a b : Fiber p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) (fiberInclusion.map φ) := φ.2
@[ext]
lemma hom_ext {a b : Fiber p S} {φ ψ : a ⟶ b}
    (h : fiberInclusion.map φ = fiberInclusion.map ψ) : φ = ψ :=
  Subtype.ext h
instance : (fiberInclusion : Fiber p S ⥤ _).Faithful where
@[simps!]
def fiberInclusionCompIsoConst : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S :=
  NatIso.ofComponents (fun X ↦ eqToIso X.2)
    (fun φ ↦ by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])
lemma fiberInclusion_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).obj S :=
  Functor.ext (fun x ↦ x.2) (fun _ _ φ ↦ IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ))
def mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩
@[simp]
lemma fiberInclusion_mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    fiberInclusion.obj (mk ha) = a :=
  rfl
def homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    mk (domain_eq p (𝟙 S) φ) ⟶ mk (codomain_eq p (𝟙 S) φ) :=
  ⟨φ, inferInstance⟩
@[simp]
lemma fiberInclusion_homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    fiberInclusion.map (homMk p S φ) = φ :=
  rfl
@[simp]
lemma homMk_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] :
    homMk p S (𝟙 a) = 𝟙 (mk (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl
@[simp]
lemma homMk_comp {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : homMk p S φ ≫ homMk p S ψ = homMk p S (φ ≫ ψ) :=
  rfl
section
variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)
@[simps]
def inducedFunctor : C ⥤ Fiber p S where
  obj x := ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
  map φ := ⟨F.map φ, of_commsq _ _ _ _ _ <| by simpa using (eqToIso hF).hom.naturality φ⟩
@[simp]
lemma inducedFunctor_map {X Y : C} (f : X ⟶ Y) :
    fiberInclusion.map ((inducedFunctor hF).map f) = F.map f := rfl
@[simps!]
def inducedFunctorCompIsoSelf : (inducedFunctor hF) ⋙ fiberInclusion ≅ F := Iso.refl _
lemma inducedFunctor_comp : (inducedFunctor hF) ⋙ fiberInclusion = F := rfl
end
end Fiber
end Functor
end CategoryTheory