import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Tactic.CategoryTheory.Elementwise
open CategoryTheory
open CategoryTheory.Limits
universe w u
namespace AddCommGrp
instance : HasBinaryBiproducts AddCommGrp :=
  HasBinaryBiproducts.of_hasBinaryProducts
instance : HasFiniteBiproducts AddCommGrp :=
  HasFiniteBiproducts.of_hasFiniteProducts
@[simps cone_pt isLimit_lift]
def binaryProductLimitCone (G H : AddCommGrp.{u}) : Limits.LimitCone (pair G H) where
  cone :=
    { pt := AddCommGrp.of (G × H)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun s => AddMonoidHom.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> rfl
      uniq := fun s m w => by
        simp_rw [← w ⟨WalkingPair.left⟩, ← w ⟨WalkingPair.right⟩]
        rfl }
@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrp.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl
@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrp.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl
noncomputable def biprodIsoProd (G H : AddCommGrp.{u}) :
    (G ⊞ H : AddCommGrp) ≅ AddCommGrp.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrp.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrp.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
namespace HasLimit
variable {J : Type w} (f : J → AddCommGrp.{max w u})
def lift (s : Fan f) : s.pt ⟶ AddCommGrp.of (∀ j, f j) where
  toFun x j := s.π.app ⟨j⟩ x
  map_zero' := by
    simp only [Functor.const_obj_obj, map_zero]
    rfl
  map_add' x y := by
    simp only [Functor.const_obj_obj, map_add]
    rfl
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGrp.of (∀ j, f j)
      π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x
        funext j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt → f j) x) (w ⟨j⟩) }
end HasLimit
open HasLimit
variable {J : Type} [Finite J]
noncomputable def biproductIsoPi (f : J → AddCommGrp.{u}) :
    (⨁ f : AddCommGrp) ≅ AddCommGrp.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit
@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrp.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
end AddCommGrp