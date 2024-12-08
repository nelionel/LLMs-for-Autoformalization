import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
universe u
open CategoryTheory
open scoped Topology
attribute [local instance] ConcreteCategory.instFunLike
abbrev Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)
namespace CompHaus
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  let A' : CompHaus := CompHaus.of A
  let B' : CompHaus := CompHaus.of B
  let f' : X ⟶ B' := ⟨f, hf⟩
  let g' : A' ⟶ B' := ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h, hh⟩ := Projective.factors f' g'
  refine ⟨h, h.2, ?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh
@[simps!]
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  toTop := X.toTop
  prop := inferInstance
end CompHaus
namespace Stonean
abbrev toCompHaus : Stonean.{u} ⥤ CompHaus.{u} :=
  compHausLikeToCompHaus _
abbrev fullyFaithfulToCompHaus : toCompHaus.FullyFaithful  :=
  CompHausLike.fullyFaithfulToCompHausLike _
open CompHausLike
instance (X : Type*) [TopologicalSpace X]
    [ExtremallyDisconnected X] : HasProp (fun Y ↦ ExtremallyDisconnected Y) X :=
  ⟨(inferInstance : ExtremallyDisconnected X)⟩
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean := CompHausLike.of _ X
instance (X : Stonean.{u}) : ExtremallyDisconnected X := X.prop
abbrev toProfinite : Stonean.{u} ⥤ Profinite.{u} :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)
instance (X : Stonean.{u}) : ExtremallyDisconnected ((forget _).obj X) := X.prop
instance (X : Stonean.{u}) : TotallyDisconnectedSpace ((forget _).obj X) :=
  show TotallyDisconnectedSpace X from inferInstance
def mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] : Stonean where
  toTop := (CompHaus.of X).toTop
  prop := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)
lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  refine ⟨?_, ConcreteCategory.epi_of_surjective _⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.continuous).isClosed
  let U := Cᶜ
  have hUy : U ∈ 𝓝 y := by
    simp only [C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) :=
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext 
    change 1 = ite _ _ _ 
    rw [if_neg]
    refine mt (hVU ·) ?_ 
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H 
  rw [if_pos hyV] at H
  exact one_ne_zero H
instance instProjectiveCompHausCompHaus (X : Stonean) : Projective (toCompHaus.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toProfinite.obj X) := X.prop
    have hf : Function.Surjective f := by rwa [← Profinite.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _
instance (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.toTop := X.prop
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _
end Stonean
namespace CompHaus
noncomputable
def presentation (X : CompHaus) : Stonean where
  toTop := (projectivePresentation X).p.1
  prop := by
    refine CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => ?_)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => ?_)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl
noncomputable
def presentation.π (X : CompHaus) : Stonean.toCompHaus.obj X.presentation ⟶ X :=
  (projectivePresentation X).f
noncomputable
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi
abbrev _root_.Stonean.compHaus (X : Stonean) := Stonean.toCompHaus.obj X
noncomputable
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f
@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]
lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    show Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus
end CompHaus
namespace Profinite
noncomputable
def presentation (X : Profinite) : Stonean where
  toTop := (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop
noncomputable
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  (profiniteToCompHaus.obj X).projectivePresentation.f
noncomputable
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this
noncomputable
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := Projective.factorThru e f
@[simp, reassoc]
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := by simp [lift]
lemma projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X) :
    Projective X := by
  show Projective (Stonean.toProfinite.obj ⟨X.toTop, inferInstance⟩)
  exact inferInstance
end Profinite