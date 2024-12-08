import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Stonean.Basic
universe w u
open CategoryTheory Limits CompHausLike Topology
attribute [local instance] ConcreteCategory.instFunLike
namespace Stonean
instance : HasExplicitFiniteCoproducts.{w, u} (fun Y ↦ ExtremallyDisconnected Y) where
  hasProp _ := { hasProp := show ExtremallyDisconnected (Σ (_a : _), _) from inferInstance}
variable {X Y Z : Stonean} {f : X ⟶ Z} (i : Y ⟶ Z) (hi : IsOpenEmbedding f)
include hi
lemma extremallyDisconnected_preimage : ExtremallyDisconnected (i ⁻¹' (Set.range f)) where
  open_closure U hU := by
    have h : IsClopen (i ⁻¹' (Set.range f)) :=
      ⟨IsClosed.preimage i.continuous (isCompact_range f.continuous).isClosed,
        IsOpen.preimage i.continuous hi.isOpen_range⟩
    rw [← (closure U).preimage_image_eq Subtype.coe_injective,
      ← h.1.isClosedEmbedding_subtypeVal.closure_image_eq U]
    exact isOpen_induced (ExtremallyDisconnected.open_closure _
      (h.2.isOpenEmbedding_subtypeVal.isOpenMap U hU))
lemma extremallyDisconnected_pullback : ExtremallyDisconnected {xy : X × Y | f xy.1 = i xy.2} :=
  have := extremallyDisconnected_preimage i hi
  let e := (TopCat.pullbackHomeoPreimage i i.2 f hi.isEmbedding).symm
  let e' : {xy : X × Y | f xy.1 = i xy.2} ≃ₜ {xy : Y × X | i xy.1 = f xy.2} := by
    exact TopCat.homeoOfIso
      ((TopCat.pullbackIsoProdSubtype f i).symm ≪≫ pullbackSymmetry _ _ ≪≫
        (TopCat.pullbackIsoProdSubtype i f))
  extremallyDisconnected_of_homeo (e.trans e'.symm)
instance : HasExplicitPullbacksOfInclusions (fun (Y : TopCat.{u}) ↦ ExtremallyDisconnected Y) := by
  apply CompHausLike.hasPullbacksOfInclusions
  intro _ _ _ _ _ hi
  exact ⟨extremallyDisconnected_pullback _ hi⟩
example : FinitaryExtensive Stonean.{u} := inferInstance
noncomputable example : PreservesFiniteCoproducts Stonean.toCompHaus := inferInstance
noncomputable example : PreservesFiniteCoproducts Stonean.toProfinite := inferInstance
end Stonean