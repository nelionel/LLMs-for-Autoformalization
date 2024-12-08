import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.IsConnected
universe v' u' v u
noncomputable section
open CategoryTheory CategoryTheory.Limits
variable {J : Type u'} [Category.{v'} J]
variable {C : Type u} [Category.{v} C]
variable {X : C}
namespace CategoryTheory.Over
namespace CreatesConnected
def natTransInOver {B : C} (F : J ⥤ Over B) :
    F ⋙ forget B ⟶ (CategoryTheory.Functor.const J).obj B where
  app j := (F.obj j).hom
@[simps]
def raiseCone [IsConnected J] {B : C} {F : J ⥤ Over B} (c : Cone (F ⋙ forget B)) :
    Cone F where
  pt := Over.mk (c.π.app (Classical.arbitrary J) ≫ (F.obj (Classical.arbitrary J)).hom)
  π :=
    { app := fun j =>
        Over.homMk (c.π.app j) (nat_trans_from_is_connected (c.π ≫ natTransInOver F) j _)
      naturality := by
        intro X Y f
        apply CommaMorphism.ext
        · simpa using (c.w f).symm
        · simp }
theorem raised_cone_lowers_to_original [IsConnected J] {B : C} {F : J ⥤ Over B}
    (c : Cone (F ⋙ forget B)) :
    (forget B).mapCone (raiseCone c) = c := by aesop_cat
def raisedConeIsLimit [IsConnected J] {B : C} {F : J ⥤ Over B} {c : Cone (F ⋙ forget B)}
    (t : IsLimit c) : IsLimit (raiseCone c) where
  lift s :=
    Over.homMk (t.lift ((forget B).mapCone s))
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]
end CreatesConnected
instance forgetCreatesConnectedLimits [IsConnected J] {B : C} :
    CreatesLimitsOfShape J (forget B) where
  CreatesLimit :=
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.raised_cone_lowers_to_original c)
        makesLimit := CreatesConnected.raisedConeIsLimit t }
instance has_connected_limits {B : C} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Over B) where
  has_limit F := hasLimit_of_created F (forget B)
end CategoryTheory.Over