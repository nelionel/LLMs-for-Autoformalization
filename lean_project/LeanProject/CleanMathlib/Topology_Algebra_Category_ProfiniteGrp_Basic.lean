import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Topology.Algebra.ClosedSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.Profinite.Basic
universe u v
open CategoryTheory Topology
@[pp_with_univ]
structure ProfiniteGrp where
  toProfinite : Profinite
  [group : Group toProfinite]
  [topologicalGroup : TopologicalGroup toProfinite]
@[pp_with_univ]
structure ProfiniteAddGrp where
  toProfinite : Profinite
  [addGroup : AddGroup toProfinite]
  [topologicalAddGroup : TopologicalAddGroup toProfinite]
attribute [to_additive] ProfiniteGrp
namespace ProfiniteGrp
@[to_additive]
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite
attribute [instance] group topologicalGroup
    ProfiniteAddGrp.addGroup ProfiniteAddGrp.topologicalAddGroup
@[to_additive]
instance : Category ProfiniteGrp where
  Hom A B := ContinuousMonoidHom A B
  id A := ContinuousMonoidHom.id A
  comp f g := ContinuousMonoidHom.comp g f
@[to_additive]
instance (G H : ProfiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs <| FunLike (ContinuousMonoidHom G H) G H
@[to_additive]
instance (G H : ProfiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs <| MonoidHomClass (ContinuousMonoidHom G H) G H
@[to_additive]
instance (G H : ProfiniteGrp) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs <| ContinuousMapClass (ContinuousMonoidHom G H) G H
@[to_additive]
instance : ConcreteCategory ProfiniteGrp where
  forget :=
  { obj := fun G => G
    map := fun f => f }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        exact DFunLike.ext _ _ <| fun x => congr_fun h x }
@[to_additive "Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
compact and totally disconnected topological additive group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that {0}
is a closed set, thus implying Hausdorff in a topological additive group.)"]
def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›
@[to_additive (attr := simp)]
theorem coe_of (X : ProfiniteGrp) : (of X : Type _) = X :=
  rfl
@[to_additive (attr := simp)]
theorem coe_id (X : ProfiniteGrp) : (𝟙 ((forget ProfiniteGrp).obj X)) = id :=
  rfl
@[to_additive (attr := simp)]
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget ProfiniteGrp).map f ≫ (forget ProfiniteGrp).map g) = g ∘ f :=
  rfl
@[to_additive "Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
profinite topological additive group."]
abbrev ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] :
    ProfiniteGrp := of G
@[to_additive "The pi-type of profinite additive groups is a
profinite additive group."]
def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype
@[to_additive "A `FiniteAddGrp` when given the discrete topology can be considered as a
profinite additive group."]
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G
@[to_additive]
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f => ⟨f, by continuity⟩ }
@[to_additive]
instance : HasForget₂ ProfiniteGrp Grp where
  forget₂ := {
    obj := fun P => ⟨P, P.group⟩
    map := fun f => f.toMonoidHom
  }
def ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G)  : ProfiniteGrp :=
  letI : CompactSpace H := inferInstance
  of H.1
def profiniteGrpToProfinite : ProfiniteGrp ⥤ Profinite where
  obj G := G.toProfinite
  map f := ⟨f, by continuity⟩
instance : profiniteGrpToProfinite.Faithful := {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext_iff.mpr (congrFun (congrArg ContinuousMap.toFun h)) }
end ProfiniteGrp
section Limits
namespace ProfiniteGrp
section
variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})
def limitConePtAux : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]
instance : Group (Profinite.limitCone (F ⋙ profiniteGrpToProfinite.{max v u})).pt :=
  inferInstanceAs (Group (limitConePtAux F))
instance : TopologicalGroup (Profinite.limitCone (F ⋙ profiniteGrpToProfinite.{max v u})).pt :=
  inferInstanceAs (TopologicalGroup (limitConePtAux F))
abbrev limitCone : Limits.Cone F where
  pt := ofProfinite (Profinite.limitCone (F ⋙ profiniteGrpToProfinite.{max v u})).pt
  π :=
  { app := fun j => {
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a => a) }
    naturality := fun i j f => by
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm }
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := {
    ((Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)).lift
      (profiniteGrpToProfinite.mapCone cone)) with
    map_one' := Subtype.ext (funext fun j ↦ map_one (cone.π.app j))
    map_mul' := fun _ _ ↦ Subtype.ext (funext fun j ↦ map_mul (cone.π.app j) _ _) }
  uniq cone m h := by
    apply profiniteGrpToProfinite.map_injective
    simpa using (Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)).uniq
      (profiniteGrpToProfinite.mapCone cone) (profiniteGrpToProfinite.map m)
      (fun j ↦ congrArg profiniteGrpToProfinite.map (h j))
instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }
abbrev limit : ProfiniteGrp := (ProfiniteGrp.limitCone F).pt
end
instance : Limits.PreservesLimits profiniteGrpToProfinite.{u} where
  preservesLimitsOfShape := {
    preservesLimit := fun {F} ↦ CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)) }
end ProfiniteGrp
end Limits