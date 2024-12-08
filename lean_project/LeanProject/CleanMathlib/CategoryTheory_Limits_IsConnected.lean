import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.HomCongr
universe w v u
namespace CategoryTheory.Limits.Types
variable (C : Type u) [Category.{v} C]
def constPUnitFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}
@[simps]
def pUnitCocone : Cocone (constPUnitFunctor.{w} C) where
  pt := PUnit
  ι := { app := fun _ => id }
noncomputable def isColimitPUnitCocone [IsConnected C] : IsColimit (pUnitCocone.{w} C) where
  desc s := s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    apply constant_of_preserves_morphisms (s.ι.app · PUnit.unit)
    intros X Y f
    exact congrFun (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]
instance instHasColimitConstPUnitFunctor [IsConnected C] : HasColimit (constPUnitFunctor.{w} C) :=
  ⟨_, isColimitPUnitCocone _⟩
instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (constPUnitFunctor.{w} C)] :
    Subsingleton (colimit (constPUnitFunctor.{w} C)) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (constPUnitFunctor.{w} C) ≅ PUnit.{w + 1} :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)
theorem zigzag_of_eqvGen_quot_rel (F : C ⥤ Type w) (c d : Σ j, F.obj j)
    (h : Relation.EqvGen (Quot.Rel F) c d) : Zigzag c.1 d.1 := by
  induction h with
  | rel _ _ h => exact Zigzag.of_hom <| Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact zigzag_symmetric ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
    [HasColimit (constPUnitFunctor.{w} C)] :
    IsConnected C ↔ Nonempty (colimit (constPUnitFunctor.{w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_quot_rel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl
theorem isConnected_iff_isColimit_pUnitCocone :
    IsConnected C ↔ Nonempty (IsColimit (pUnitCocone.{w} C)) := by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩
universe v₂ u₂
variable {C : Type u} {D : Type u₂} [Category.{v} C] [Category.{v₂} D]
theorem isConnected_iff_of_final (F : C ⥤ D) [CategoryTheory.Functor.Final F] :
    IsConnected C ↔ IsConnected D := by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C,
    isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
  exact Equiv.nonempty_congr <| Iso.isoCongrLeft <|
    CategoryTheory.Functor.Final.colimitIso F <| constPUnitFunctor.{max u v u₂ v₂} D
end CategoryTheory.Limits.Types