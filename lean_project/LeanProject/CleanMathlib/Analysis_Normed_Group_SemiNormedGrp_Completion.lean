import Mathlib.Analysis.Normed.Group.SemiNormedGrp
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Analysis.Normed.Group.HomCompletion
noncomputable section
universe u
open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom
namespace SemiNormedGrp
@[simps]
def completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  obj V := SemiNormedGrp.of (Completion V)
  map f := f.completion
  map_id _ := completion_id
  map_comp f g := (completion_comp f g).symm
instance completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _
@[simps]
def completion.incl {V : SemiNormedGrp} : V ⟶ completion.obj V where
  toFun v := (v : Completion V)
  map_add' := Completion.coe_add
  bound' := ⟨1, fun v => by simp⟩
attribute [nolint simpNF] SemiNormedGrp.completion.incl_apply
theorem completion.norm_incl_eq {V : SemiNormedGrp} {v : V} : ‖completion.incl v‖ = ‖v‖ :=
  UniformSpace.Completion.norm_coe _
theorem completion.map_normNoninc {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.NormNoninc) :
    (completion.map f).NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f).le.trans <|
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf
variable (V W : SemiNormedGrp)
def completion.mapHom (V W : SemiNormedGrp.{u}) :
    have (V W : SemiNormedGrp.{u}) : AddGroup (V ⟶ W) :=
      inferInstanceAs <| AddGroup <| NormedAddGroupHom V W
    (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g => f.completion_add g
theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
  @AddMonoidHom.map_zero _ _ (_) (_) (completion.mapHom V W)
instance : Preadditive SemiNormedGrp.{u} where
  homGroup P Q := inferInstanceAs <| AddCommGroup <| NormedAddGroupHom P Q
  add_comp _ Q _ f f' g := by
    ext x
    rw [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]
    convert map_add g (f x) (f' x)
  comp_add _ _ _ _ _ _ := by
    ext
    rw [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]
instance : Functor.Additive completion where
  map_add := NormedAddGroupHom.completion_add _ _
def completion.lift {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W where
  toFun := f.extension
  map_add' := f.extension.toAddMonoidHom.map_add'
  bound' := f.extension.bound'
theorem completion.lift_comp_incl {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) : completion.incl ≫ completion.lift f = f :=
  ext <| NormedAddGroupHom.extension_coe _
theorem completion.lift_unique {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : completion.incl ≫ g = f → g = completion.lift f :=
  fun h => (NormedAddGroupHom.extension_unique _ fun v =>
    ((NormedAddGroupHom.ext_iff.1 h) v).symm).symm
end SemiNormedGrp