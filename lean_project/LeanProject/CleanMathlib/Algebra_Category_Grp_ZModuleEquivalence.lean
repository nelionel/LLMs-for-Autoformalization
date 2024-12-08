import Mathlib.Algebra.Category.ModuleCat.Basic
open CategoryTheory
open CategoryTheory.Equivalence
universe u
namespace ModuleCat
instance forget₂_addCommGroup_full : (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).Full where
  map_surjective {A B}
    f := ⟨@LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
        { toFun := f,
          map_add' := AddMonoidHom.map_add (show A.carrier →+ B.carrier from f) }
        (fun n x => by
          convert AddMonoidHom.map_zsmul (show A.carrier →+ B.carrier from f) x n <;>
            ext <;> apply int_smul_eq_zsmul), rfl⟩
instance forget₂_addCommGrp_essSurj : (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).EssSurj where
  mem_essImage A :=
    ⟨ModuleCat.of ℤ A,
      ⟨{  hom := 𝟙 A
          inv := 𝟙 A }⟩⟩
noncomputable instance forget₂AddCommGroupIsEquivalence :
    (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).IsEquivalence where
end ModuleCat