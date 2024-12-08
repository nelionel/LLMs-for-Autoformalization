import Mathlib.Topology.Category.LightProfinite.Basic
noncomputable section
open CategoryTheory Limits CompHausLike
attribute [local instance] ConcreteCategory.instFunLike
namespace LightProfinite
universe u
variable (S : LightProfinite.{u})
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc
def asLimitCone : Cone S.diagram where
  pt := S
  π := {
    app := fun n ↦ (lightToProfiniteFullyFaithful.preimageIso <|
      (Cones.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit <|
  Cones.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cones.forget _).mapIso S.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩
abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩
lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [toCompHausLike_obj, Functor.comp_obj, toCompHausLike_map, coe_of]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _
lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _
abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩
abbrev transitionMap (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩
abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩
lemma proj_comp_transitionMap (n : ℕ) :
    S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op
lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE h).op
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl
lemma surjective_transitionMap (n : ℕ) : Function.Surjective (S.transitionMap n) := by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n
lemma surjective_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (S.transitionMapLE h) := by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n
end LightProfinite