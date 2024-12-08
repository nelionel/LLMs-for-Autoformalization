import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Limits.Shapes.Types
noncomputable section
universe u
open CategoryTheory Limits
namespace AddCommGrp
def free : Type u ⥤ AddCommGrp where
  obj α := of (FreeAbelianGroup α)
  map := FreeAbelianGroup.map
  map_id _ := AddMonoidHom.ext FreeAbelianGroup.map_id_apply
  map_comp _ _ := AddMonoidHom.ext FreeAbelianGroup.map_comp_apply
@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl
def adj : free ⊣ forget AddCommGrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => FreeAbelianGroup.lift.symm
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp only [Equiv.symm_symm]
        apply FreeAbelianGroup.lift_comp }
instance : free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩
instance : (forget AddCommGrp.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩
instance : AddCommGrp.free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩
example {G H : AddCommGrp.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective (f : G → H)).mp (Functor.map_mono (forget AddCommGrp) f)
instance : (free.{u}).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    by_cases hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj free _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · simp only [not_isEmpty_iff] at hX
      have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsSplitMono f := IsSplitMono.mk' { retraction := g }
      infer_instance
end AddCommGrp
namespace Grp
def free : Type u ⥤ Grp where
  obj α := of (FreeGroup α)
  map := FreeGroup.map
  map_id := by
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
  map_comp := by
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
def adj : free ⊣ forget Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => FreeGroup.lift.symm
      homEquiv_naturality_left_symm := by
        intros
        ext1
        simp only [Equiv.symm_symm]
        apply Eq.symm
        apply FreeGroup.lift.unique
        intros
        apply FreeGroup.lift.of }
instance : (forget Grp.{u}).IsRightAdjoint  :=
  ⟨_, ⟨adj⟩⟩
section Abelianization
def abelianize : Grp.{u} ⥤ CommGrp.{u} where
  obj G := CommGrp.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)
  map_id := by
    intros; simp only [coe_id]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
  map_comp := by
    intros; simp only [coe_comp]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
def abelianizeAdj : abelianize ⊣ forget₂ CommGrp.{u} Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => Abelianization.lift.symm
      homEquiv_naturality_left_symm := by
        intros
        ext1
        simp only [Equiv.symm_symm]
        apply Eq.symm
        apply Abelianization.lift.unique
        intros
        apply Abelianization.lift.of }
end Abelianization
end Grp
@[simps]
def MonCat.units : MonCat.{u} ⥤ Grp.{u} where
  obj R := Grp.of Rˣ
  map f := Grp.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
def Grp.forget₂MonAdj : forget₂ Grp MonCat ⊣ MonCat.units.{u} := Adjunction.mk' {
  homEquiv := fun _ Y ↦
    { toFun := fun f => MonoidHom.toHomUnits f
      invFun := fun f => (Units.coeHom Y).comp f
      left_inv := fun _ => MonoidHom.ext fun _ => rfl
      right_inv := fun _ => MonoidHom.ext fun _ => Units.ext rfl }
  unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with }
      naturality := fun _ _ _ => MonoidHom.ext fun _ => Units.ext rfl }
  counit :=
    { app := fun X => Units.coeHom X
      naturality := by intros; exact MonoidHom.ext fun x => rfl } }
instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨Grp.forget₂MonAdj⟩⟩
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrp.{u} where
  obj R := CommGrp.of Rˣ
  map f := CommGrp.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
def CommGrp.forget₂CommMonAdj : forget₂ CommGrp CommMonCat ⊣ CommMonCat.units.{u} :=
  Adjunction.mk' {
    homEquiv := fun _ Y ↦
      { toFun := fun f => MonoidHom.toHomUnits f
        invFun := fun f => (Units.coeHom Y).comp f
        left_inv := fun _ => MonoidHom.ext fun _ => rfl
        right_inv := fun _ => MonoidHom.ext fun _ => Units.ext rfl }
    unit :=
      { app := fun X => { (@toUnits X _).toMonoidHom with }
        naturality := fun _ _ _ => MonoidHom.ext fun _ => Units.ext rfl }
    counit :=
      { app := fun X => Units.coeHom X
        naturality := by intros; exact MonoidHom.ext fun x => rfl } }
instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGrp.forget₂CommMonAdj⟩⟩