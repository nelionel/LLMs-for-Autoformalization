import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Rep
suppress_compilation
universe u
open CategoryTheory
open CategoryTheory.Limits
abbrev FDRep (k G : Type u) [Field k] [Monoid G] :=
  Action (FGModuleCat.{u} k) (MonCat.of G)
@[deprecated (since := "2024-07-05")]
alias FdRep := FDRep
namespace FDRep
variable {k G : Type u} [Field k] [Monoid G]
instance : LargeCategory (FDRep k G) := inferInstance
instance : ConcreteCategory (FDRep k G) := inferInstance
instance : Preadditive (FDRep k G) := inferInstance
instance : HasFiniteLimits (FDRep k G) := inferInstance
instance : Linear k (FDRep k G) := by infer_instance
instance : CoeSort (FDRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _
instance (V : FDRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance
instance (V : FDRep k G) : Module k V := by
  change Module k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance
instance (V : FDRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V); infer_instance
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))
def ρ (V : FDRep k G) : G →* V →ₗ[k] V :=
  Action.ρ V
def isoToLinearEquiv {V W : FDRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)
theorem Iso.conj_ρ {V W : FDRep k G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  erw [FDRep.isoToLinearEquiv, ← FGModuleCat.Iso.conj_eq_conj, Iso.conj_apply]
  rw [Iso.eq_inv_comp ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)]
  exact (i.hom.comm g).symm
@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FDRep k G :=
  ⟨FGModuleCat.of k V, ρ⟩
instance : HasForget₂ (FDRep k G) (Rep k G) where
  forget₂ := (forget₂ (FGModuleCat k) (ModuleCat k)).mapAction (MonCat.of G)
theorem forget₂_ρ (V : FDRep k G) : ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ = V.ρ := by
  ext g v; rfl
example : MonoidalCategory (FDRep k G) := by infer_instance
example : MonoidalPreadditive (FDRep k G) := by infer_instance
example : MonoidalLinear k (FDRep k G) := by infer_instance
open Module
open scoped Classical
instance : HasKernels (FDRep k G) := by infer_instance
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W
def forget₂HomLinearEquiv (X Y : FDRep k G) :
    ((forget₂ (FDRep k G) (Rep k G)).obj X ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj Y) ≃ₗ[k] X ⟶ Y where
  toFun f := ⟨f.hom, f.comm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom, f.comm⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
end FDRep
namespace FDRep
variable {k G : Type u} [Field k] [Group G]
noncomputable instance : RightRigidCategory (FDRep k G) := by
  change RightRigidCategory (Action (FGModuleCat k) (Grp.of G)); infer_instance
example : RigidCategory (FDRep k G) := by infer_instance
end FDRep
namespace FDRep
open Representation
variable {k G V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρV : Representation k G V) (W : FDRep k G)
open scoped MonoidalCategory
noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual ⊗ W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  @LinearEquiv.toFGModuleCatIso k _ (FDRep.of ρV.dual ⊗ W).V (V →ₗ[k] W)
    _ _ _ _ _ _ (dualTensorHomEquiv k V W)
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) ?_
  convert dualTensorHom_comm ρV W.ρ
@[simp]
theorem dualTensorIsoLinHom_hom_hom : (dualTensorIsoLinHom ρV W).hom.hom = dualTensorHom k V W :=
  rfl
end FDRep