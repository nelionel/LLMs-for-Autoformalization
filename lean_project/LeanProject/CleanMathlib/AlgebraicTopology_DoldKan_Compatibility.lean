import Mathlib.CategoryTheory.Equivalence
open CategoryTheory CategoryTheory.Category
namespace AlgebraicTopology
namespace DoldKan
namespace Compatibility
variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B'] (eA : A ≌ A')
  (eB : B ≌ B') (e' : A' ≌ B') {F : A ⥤ B'} (hF : eA.functor ⋙ e'.functor ≅ F) {G : B ⥤ A}
  (hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor)
@[simps! functor inverse unitIso_hom_app]
def equivalence₀ : A ≌ B' :=
  eA.trans e'
variable {eA} {e'}
@[simps! functor]
def equivalence₁ : A ≌ B' := (equivalence₀ eA e').changeFunctor hF
theorem equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse :=
  rfl
@[simps!]
def equivalence₁CounitIso : (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
  calc
    (e'.inverse ⋙ eA.inverse) ⋙ F ≅ (e'.inverse ⋙ eA.inverse) ⋙ eA.functor ⋙ e'.functor :=
      isoWhiskerLeft _ hF.symm
    _ ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.functor) ⋙ e'.functor := Iso.refl _
    _ ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.functor := isoWhiskerLeft _ (isoWhiskerRight eA.counitIso _)
    _ ≅ e'.inverse ⋙ e'.functor := Iso.refl _
    _ ≅ 𝟭 B' := e'.counitIso
theorem equivalence₁CounitIso_eq : (equivalence₁ hF).counitIso = equivalence₁CounitIso hF := by
  ext Y
  simp [equivalence₁, equivalence₀]
@[simps!]
def equivalence₁UnitIso : 𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ eA.functor ⋙ eA.inverse := eA.unitIso
    _ ≅ eA.functor ⋙ 𝟭 A' ⋙ eA.inverse := Iso.refl _
    _ ≅ eA.functor ⋙ (e'.functor ⋙ e'.inverse) ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight e'.unitIso _)
    _ ≅ (eA.functor ⋙ e'.functor) ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
    _ ≅ F ⋙ e'.inverse ⋙ eA.inverse := isoWhiskerRight hF _
theorem equivalence₁UnitIso_eq : (equivalence₁ hF).unitIso = equivalence₁UnitIso hF := by
  ext X
  simp [equivalence₁]
@[simps! functor]
def equivalence₂ : A ≌ B :=
  (equivalence₁ hF).trans eB.symm
theorem equivalence₂_inverse :
    (equivalence₂ eB hF).inverse = eB.functor ⋙ e'.inverse ⋙ eA.inverse :=
  rfl
@[simps!]
def equivalence₂CounitIso : (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅
        eB.functor ⋙ (e'.inverse ⋙ eA.inverse ⋙ F) ⋙ eB.inverse :=
      Iso.refl _
    _ ≅ eB.functor ⋙ 𝟭 _ ⋙ eB.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight (equivalence₁CounitIso hF) _)
    _ ≅ eB.functor ⋙ eB.inverse := Iso.refl _
    _ ≅ 𝟭 B := eB.unitIso.symm
theorem equivalence₂CounitIso_eq :
    (equivalence₂ eB hF).counitIso = equivalence₂CounitIso eB hF := by
  ext Y'
  dsimp [equivalence₂, Iso.refl]
  simp only [equivalence₁CounitIso_eq, equivalence₂CounitIso_hom_app,
    equivalence₁CounitIso_hom_app, Functor.map_comp, assoc]
@[simps!]
def equivalence₂UnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ eB.functor ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse := equivalence₁UnitIso hF
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
    _ ≅ F ⋙ (eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _)
    _ ≅ (F ⋙ eB.inverse) ⋙ eB.functor ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
theorem equivalence₂UnitIso_eq : (equivalence₂ eB hF).unitIso = equivalence₂UnitIso eB hF := by
  ext X
  dsimp [equivalence₂]
  simp only [equivalence₂UnitIso_hom_app, equivalence₁UnitIso_eq, equivalence₁UnitIso_hom_app,
      assoc, NatIso.cancel_natIso_hom_left]
  rfl
variable {eB}
@[simps! inverse]
def equivalence : A ≌ B :=
  ((equivalence₂ eB hF).changeInverse
    (calc eB.functor ⋙ e'.inverse ⋙ eA.inverse ≅
        (eB.functor ⋙ e'.inverse) ⋙ eA.inverse := (Functor.associator _ _ _).symm
    _ ≅ (G ⋙ eA.functor) ⋙ eA.inverse := isoWhiskerRight hG _
    _ ≅ G ⋙ 𝟭 A := isoWhiskerLeft _ eA.unitIso.symm
    _ ≅ G := G.rightUnitor))
theorem equivalence_functor : (equivalence hF hG).functor = F ⋙ eB.inverse :=
  rfl
@[simps! hom_app]
def τ₀ : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor :=
  calc
    eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor ⋙ 𝟭 _ := isoWhiskerLeft _ e'.counitIso
    _ ≅ eB.functor := Functor.rightUnitor _
@[simps! hom_app]
def τ₁ (η : G ⋙ F ≅ eB.functor) : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor :=
  calc
    eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ (eB.functor ⋙ e'.inverse) ⋙ e'.functor :=
        Iso.refl _
    _ ≅ (G ⋙ eA.functor) ⋙ e'.functor := isoWhiskerRight hG _
    _ ≅ G ⋙ eA.functor ⋙ e'.functor := by rfl
    _ ≅ G ⋙ F := isoWhiskerLeft _ hF
    _ ≅ eB.functor := η
variable (η : G ⋙ F ≅ eB.functor)
@[simps!]
def equivalenceCounitIso : G ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    G ⋙ F ⋙ eB.inverse ≅ (G ⋙ F) ⋙ eB.inverse := Iso.refl _
    _ ≅ eB.functor ⋙ eB.inverse := isoWhiskerRight η _
    _ ≅ 𝟭 B := eB.unitIso.symm
variable {η hF hG}
theorem equivalenceCounitIso_eq (hη : τ₀ = τ₁ hF hG η) :
    (equivalence hF hG).counitIso = equivalenceCounitIso η := by
  ext1; apply NatTrans.ext; ext Y
  dsimp [equivalence]
  simp only [comp_id, id_comp, Functor.map_comp, equivalence₂CounitIso_eq,
    equivalence₂CounitIso_hom_app, assoc, equivalenceCounitIso_hom_app]
  simp only [← eB.inverse.map_comp_assoc, ← τ₀_hom_app, hη, τ₁_hom_app]
  erw [hF.inv.naturality_assoc, hF.inv.naturality_assoc]
  dsimp
  congr 2
  simp only [← e'.functor.map_comp_assoc, Equivalence.fun_inv_map, assoc,
    Iso.inv_hom_id_app_assoc, hG.inv_hom_id_app]
  dsimp
  rw [comp_id, eA.functor_unitIso_comp, e'.functor.map_id, id_comp, hF.inv_hom_id_app_assoc]
variable (hF)
@[simps!]
def υ : eA.functor ≅ F ⋙ e'.inverse :=
  calc
    eA.functor ≅ eA.functor ⋙ 𝟭 A' := (Functor.leftUnitor _).symm
    _ ≅ eA.functor ⋙ e'.functor ⋙ e'.inverse := isoWhiskerLeft _ e'.unitIso
    _ ≅ (eA.functor ⋙ e'.functor) ⋙ e'.inverse := Iso.refl _
    _ ≅ F ⋙ e'.inverse := isoWhiskerRight hF _
variable (ε : eA.functor ≅ F ⋙ e'.inverse) (hG)
@[simps!]
def equivalenceUnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ G :=
  calc
    𝟭 A ≅ eA.functor ⋙ eA.inverse := eA.unitIso
    _ ≅ (F ⋙ e'.inverse) ⋙ eA.inverse := isoWhiskerRight ε _
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
    _ ≅ F ⋙ (eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _)
    _ ≅ (F ⋙ eB.inverse) ⋙ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse := Iso.refl _
    _ ≅ (F ⋙ eB.inverse) ⋙ (G ⋙ eA.functor) ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight hG _)
    _ ≅ (F ⋙ eB.inverse ⋙ G) ⋙ eA.functor ⋙ eA.inverse := Iso.refl _
    _ ≅ (F ⋙ eB.inverse ⋙ G) ⋙ 𝟭 A := isoWhiskerLeft _ eA.unitIso.symm
    _ ≅ (F ⋙ eB.inverse) ⋙ G := Iso.refl _
variable {ε hF hG}
theorem equivalenceUnitIso_eq (hε : υ hF = ε) :
    (equivalence hF hG).unitIso = equivalenceUnitIso hG ε := by
  ext1; apply NatTrans.ext; ext X
  dsimp [equivalence]
  simp only [assoc, comp_id, equivalenceUnitIso_hom_app]
  erw [id_comp]
  simp only [equivalence₂UnitIso_eq eB hF, equivalence₂UnitIso_hom_app,
    ← eA.inverse.map_comp_assoc, assoc, ← hε, υ_hom_app]
end Compatibility
end DoldKan
end AlgebraicTopology