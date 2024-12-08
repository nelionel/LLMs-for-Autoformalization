import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.LocallyConstant.Basic
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike
universe v u
open CategoryTheory Topology CompHausLike
abbrev Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)
namespace Profinite
instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] :  HasProp (fun Y ↦ TotallyDisconnectedSpace Y) X :=
  ⟨(inferInstance : TotallyDisconnectedSpace X)⟩
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : Profinite :=
  CompHausLike.of _ X
instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩
instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.prop
instance {X : Profinite} : TotallyDisconnectedSpace ((forget Profinite).obj X) := by
  change TotallyDisconnectedSpace X
  exact inferInstance
end Profinite
abbrev profiniteToCompHaus : Profinite ⥤ CompHaus :=
  compHausLikeToCompHaus _
instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.prop
abbrev Profinite.toTopCat : Profinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _
section Profinite
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toTop := TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := f.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩
  invFun g :=
    { toFun := Continuous.connectedComponentsLift g.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.2 }
  left_inv _ := ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  right_inv _ := ContinuousMap.ext fun _ => rfl
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl
theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥
section DiscreteTopology
attribute [local instance] FintypeCat.botTopology
theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩
attribute [local instance] FintypeCat.discreteTopology
@[simps map_apply]
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ⟨f, by continuity⟩
attribute [nolint simpNF] FintypeCat.toProfinite_map_apply
def FintypeCat.toProfiniteFullyFaithful : toProfinite.FullyFaithful where
  preimage f := (f : _ → _)
  map_preimage _ := rfl
  preimage_map _ := rfl
instance : FintypeCat.toProfinite.Faithful := FintypeCat.toProfiniteFullyFaithful.faithful
instance : FintypeCat.toProfinite.Full := FintypeCat.toProfiniteFullyFaithful.full
instance (X : FintypeCat) : Fintype (FintypeCat.toProfinite.obj X) := inferInstanceAs (Fintype X)
instance (X : FintypeCat) : Fintype (Profinite.of X) := inferInstanceAs (Fintype X)
end DiscreteTopology
end Profinite
namespace Profinite
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
      (profiniteToCompHaus.mapCone S)
  uniq S _ h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _ h
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  adj := Profinite.toProfiniteAdjToCompHaus
noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop
noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _
instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat
instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus
instance forget_preservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)
theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · 
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [g, LocallyConstant.ofIsClopen]
        erw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp only [U, C, Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map
def pi {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)
end Profinite