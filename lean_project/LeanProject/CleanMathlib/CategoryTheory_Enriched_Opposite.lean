import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
universe v₁ u₁ v u
namespace CategoryTheory
open MonoidalCategory BraidedCategory
variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]
section
variable (C : Type u) [EnrichedCategory V C]
instance EnrichedCategory.opposite : EnrichedCategory V Cᵒᵖ where
  Hom y x := EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right]
end
@[reassoc]
lemma eComp_op_eq {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ) :
    eComp V z y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop :=
  rfl
@[reassoc]
lemma tensorHom_eComp_op_eq {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v w : V}
    (f : v ⟶ EnrichedCategory.Hom z y) (g : w ⟶ EnrichedCategory.Hom y x) :
    (f ⊗ g) ≫ eComp V z y x = (β_ v w).hom ≫ (g ⊗ f) ≫ eComp V x.unop y.unop z.unop := by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc f g _
section
open ForgetEnrichment
variable (C : Type u) [EnrichedCategory V C]
def forgetEnrichmentOppositeEquivalence.functor :
    ForgetEnrichment V Cᵒᵖ ⥤ (ForgetEnrichment V C)ᵒᵖ where
  obj x := x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this, forgetEnrichment_comp, Category.assoc, tensorHom_eComp_op_eq,
      leftUnitor_inv_braiding_assoc, ← unitors_inv_equal, ← Category.assoc]
    congr 1
def forgetEnrichmentOppositeEquivalence.inverse :
    (ForgetEnrichment V C)ᵒᵖ ⥤ ForgetEnrichment V Cᵒᵖ where
  obj x := x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this, forgetEnrichment_comp, Category.assoc, unitors_inv_equal,
      ← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop ⊗ homTo V f.unop) ≫
      eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
      ((homTo V f.unop) ⊗ (homTo V g.unop)) ≫ eComp V x y z := (tensorHom_eComp_op_eq V _ _).symm
    rw [this, ← Category.assoc]
    congr 1
@[simps]
def forgetEnrichmentOppositeEquivalence : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ where
  functor := forgetEnrichmentOppositeEquivalence.functor V C
  inverse := forgetEnrichmentOppositeEquivalence.inverse V C
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
instance EnrichedOrdinaryCategory.opposite {D : Type u} [Category.{v} D]
    [EnrichedOrdinaryCategory V D] : EnrichedOrdinaryCategory V Dᵒᵖ where
  homEquiv := Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [unop_comp, tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop
end
end CategoryTheory