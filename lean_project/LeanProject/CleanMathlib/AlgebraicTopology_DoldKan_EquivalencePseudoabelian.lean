import Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive
import Mathlib.AlgebraicTopology.DoldKan.Compatibility
import Mathlib.CategoryTheory.Idempotents.SimplicialObject
import Mathlib.Tactic.SuppressCompilation
suppress_compilation
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
variable {C : Type*} [Category C] [Preadditive C]
namespace CategoryTheory
namespace Idempotents
namespace DoldKan
open AlgebraicTopology.DoldKan
@[simps!, nolint unusedArguments]
def N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ ChainComplex C ℕ :=
  N₁ ⋙ (toKaroubiEquivalence _).inverse
@[simps!, nolint unusedArguments]
def Γ [IsIdempotentComplete C] [HasFiniteCoproducts C] : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀
variable [IsIdempotentComplete C] [HasFiniteCoproducts C]
def isoN₁ :
    (toKaroubiEquivalence (SimplicialObject C)).functor ⋙
      Preadditive.DoldKan.equivalence.functor ≅ N₁ := toKaroubiCompN₂IsoN₁
@[simp]
lemma isoN₁_hom_app_f (X : SimplicialObject C) :
    (isoN₁.hom.app X).f = PInfty := rfl
def isoΓ₀ :
    (toKaroubiEquivalence (ChainComplex C ℕ)).functor ⋙ Preadditive.DoldKan.equivalence.inverse ≅
      Γ ⋙ (toKaroubiEquivalence _).functor :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀
@[simp]
lemma N₂_map_isoΓ₀_hom_app_f (X : ChainComplex C ℕ) :
    (N₂.map (isoΓ₀.hom.app X)).f = PInfty := by
  ext
  apply comp_id
def equivalence : SimplicialObject C ≌ ChainComplex C ℕ :=
  Compatibility.equivalence isoN₁ isoΓ₀
theorem equivalence_functor : (equivalence : SimplicialObject C ≌ _).functor = N :=
  rfl
theorem equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ :=
  rfl
theorem hη :
    Compatibility.τ₀ =
      Compatibility.τ₁ isoN₁ isoΓ₀
        (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubiEquivalence (ChainComplex C ℕ)).functor) := by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp )
@[simps!]
def η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ) :=
  Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C ℕ ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)
theorem equivalence_counitIso :
    DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ)) :=
  Compatibility.equivalenceCounitIso_eq hη
theorem hε :
    Compatibility.υ (isoN₁) =
      (Γ₂N₁ : (toKaroubiEquivalence _).functor ≅
          (N₁ : SimplicialObject C ⥤ _) ⋙ Preadditive.DoldKan.equivalence.inverse) := by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv, Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app]
  erw [compatibility_Γ₂N₁_Γ₂N₂_natTrans X]
  rw [Compatibility.υ_hom_app, Preadditive.DoldKan.equivalence_unitIso, Iso.app_inv, assoc]
  erw [← NatTrans.comp_app_assoc, IsIso.hom_inv_id]
  rw [NatTrans.id_app, id_comp, NatTrans.id_app, Γ₂N₂ToKaroubiIso_inv_app]
  dsimp only [Preadditive.DoldKan.equivalence_inverse, Preadditive.DoldKan.Γ]
  rw [← Γ₂.map_comp, Iso.inv_hom_id_app, Γ₂.map_id]
  rfl
def ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ :=
  Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁
theorem equivalence_unitIso :
    DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ) :=
  Compatibility.equivalenceUnitIso_eq hε
end DoldKan
end Idempotents
end CategoryTheory