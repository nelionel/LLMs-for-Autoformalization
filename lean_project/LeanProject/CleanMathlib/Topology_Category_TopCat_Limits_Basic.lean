import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic
open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
universe v u w
noncomputable section
namespace TopCat
variable {J : Type v} [SmallCategory J]
local notation "forget" => forget TopCat
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j =>
        { toFun := fun u => u.val j
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        dsimp
        rw [Category.id_comp]
        apply ContinuousMap.ext
        intro a
        exact (a.2 f).symm }
def limitConeInfi (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt :=
    ⟨(Types.limitCone.{v,u} (F ⋙ forget)).pt,
      ⨅ j, (F.obj j).str.induced ((Types.limitCone.{v,u} (F ⋙ forget)).π.app j)⟩
  π :=
    { app := fun j =>
        ⟨(Types.limitCone.{v,u} (F ⋙ forget)).π.app j, continuous_iff_le_induced.mpr (iInf_le _ _)⟩
      naturality := fun _ _ f =>
        ContinuousMap.coe_injective ((Types.limitCone.{v,u} (F ⋙ forget)).π.naturality f) }
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v,u} F) where
  lift S :=
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    apply ContinuousMap.ext; intros a; apply Subtype.ext; funext j
    dsimp
    rw [← h]
    rfl
def limitConeInfiIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitConeInfi.{v,u} F) := by
  refine IsLimit.ofFaithful forget (Types.limitConeIsLimit.{v,u} (F ⋙ forget))
    (fun s => ⟨fun v => ⟨fun j => (Functor.mapCone forget s).π.app j v, ?_⟩, ?_⟩) fun s => ?_
  · dsimp [Functor.sections]
    intro _ _ _
    rw [← comp_apply', forget_map_eq_coe, ← s.π.naturality, forget_map_eq_coe]
    dsimp
    rw [Category.id_comp]
  · exact
    continuous_iff_coinduced_le.mpr
      (le_iInf fun j =>
        coinduced_le_iff_le_induced.mp <|
          (continuous_iff_coinduced_le.mp (s.π.app j).continuous : _))
  · rfl
instance topCat_hasLimitsOfSize : HasLimitsOfSize.{v, v} TopCat.{max v u} where
  has_limits_of_shape _ :=
    { has_limit := fun F =>
        HasLimit.mk
          { cone := limitCone.{v,u} F
            isLimit := limitConeIsLimit F } }
instance topCat_hasLimits : HasLimits TopCat.{u} :=
  TopCat.topCat_hasLimitsOfSize.{u, u}
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget : TopCat.{max v u} ⥤ _) where
  preservesLimitsOfShape {_} :=
    { preservesLimit := fun {F} =>
      preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v,u} F)
          (Types.limitConeIsLimit.{v,u} (F ⋙ forget)) }
instance forget_preservesLimits : PreservesLimits (forget : TopCat.{u} ⥤ _) :=
  TopCat.forget_preservesLimitsOfSize.{u, u}
def colimitCocone (F : J ⥤ TopCat.{max v u}) : Cocone F where
  pt :=
    ⟨(Types.TypeMax.colimitCocone.{v,u} (F ⋙ forget)).pt,
      ⨆ j, (F.obj j).str.coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j)⟩
  ι :=
    { app := fun j =>
        ⟨(Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j, continuous_iff_coinduced_le.mpr <|
          le_iSup (fun j =>
            coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j) (F.obj j).str) j⟩
      naturality := fun _ _ f =>
        ContinuousMap.coe_injective ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.naturality f) }
def colimitCoconeIsColimit (F : J ⥤ TopCat.{max v u}) : IsColimit (colimitCocone F) := by
  refine
    IsColimit.ofFaithful forget (Types.TypeMax.colimitCoconeIsColimit.{v, u} _) (fun s =>
      ⟨Quot.lift (fun p => (Functor.mapCocone forget s).ι.app p.fst p.snd) ?_, ?_⟩) fun s => ?_
  · intro _ _ ⟨_, h⟩
    dsimp
    rw [h, Functor.comp_map, ← comp_apply', s.ι.naturality]
    dsimp
    rw [Category.comp_id]
  · exact
    continuous_iff_le_induced.mpr
      (iSup_le fun j =>
        coinduced_le_iff_le_induced.mp <|
          (continuous_iff_coinduced_le.mp (s.ι.app j).continuous : _))
  · rfl
instance topCat_hasColimitsOfSize : HasColimitsOfSize.{v,v} TopCat.{max v u} where
  has_colimits_of_shape _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitCoconeIsColimit F } }
instance topCat_hasColimits : HasColimits TopCat.{u} :=
  TopCat.topCat_hasColimitsOfSize.{u, u}
instance forget_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v, v} (forget : TopCat.{max u v} ⥤ _) where
  preservesColimitsOfShape :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
          (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget)) }
instance forget_preservesColimits : PreservesColimits (forget : TopCat.{u} ⥤ Type u) :=
  TopCat.forget_preservesColimitsOfSize.{u, u}
def isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext; aesop⟩
  Limits.IsTerminal.ofUnique _
def terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit
def isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨⟨fun x => x.elim, by continuity⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _
def initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPEmpty
end TopCat