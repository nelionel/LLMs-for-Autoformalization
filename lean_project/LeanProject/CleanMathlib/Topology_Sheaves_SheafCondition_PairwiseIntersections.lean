import Mathlib.CategoryTheory.Category.Pairwise
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
assert_not_exists OrderedCommMonoid
noncomputable section
universe w v u
open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}
namespace TopCat.Presheaf
section
def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))
def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (PreservesLimit (Pairwise.diagram U).op F)
end
namespace SheafCondition
variable {ι : Type w} (U : ι → Opens X)
open CategoryTheory.Pairwise
@[simp]
def pairwiseToOpensLeCoverObj : Pairwise ι → OpensLeCover U
  | single i => ⟨U i, ⟨i, le_rfl⟩⟩
  | Pairwise.pair i j => ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩
open CategoryTheory.Pairwise.Hom
def pairwiseToOpensLeCoverMap :
    ∀ {V W : Pairwise ι}, (V ⟶ W) → (pairwiseToOpensLeCoverObj U V ⟶ pairwiseToOpensLeCoverObj U W)
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => homOfLE inf_le_left
  | _, _, right _ _ => homOfLE inf_le_right
@[simps]
def pairwiseToOpensLeCover : Pairwise ι ⥤ OpensLeCover U where
  obj := pairwiseToOpensLeCoverObj U
  map {_ _} i := pairwiseToOpensLeCoverMap U i
instance (V : OpensLeCover U) : Nonempty (StructuredArrow V (pairwiseToOpensLeCover U)) :=
  ⟨@StructuredArrow.mk _ _ _ _ _ (single V.index) _ V.homToIndex⟩
instance : Functor.Final (pairwiseToOpensLeCover U) :=
  ⟨fun V =>
    isConnected_of_zigzag fun A B => by
      rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := pair i i'
                hom := (le_inf a.le b.le).hom }, _], ?_, rfl⟩
        exact
          List.Chain.cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := left i i' }⟩)
            (List.Chain.cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := right i i' }⟩)
              List.Chain.nil)
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := pair i' i
                hom := (le_inf (b.le.trans inf_le_left) a.le).hom },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := (b.le.trans inf_le_left).hom }, _], ?_, rfl⟩
        exact
          List.Chain.cons
            (Or.inr
              ⟨{  left := 𝟙 _
                  right := right i' i }⟩)
            (List.Chain.cons
              (Or.inl
                ⟨{  left := 𝟙 _
                    right := left i' i }⟩)
              (List.Chain.cons
                (Or.inr
                  ⟨{  left := 𝟙 _
                      right := left i' j' }⟩)
                List.Chain.nil))
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                hom := (a.le.trans inf_le_left).hom },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := (le_inf (a.le.trans inf_le_left) b.le).hom }, _], ?_, rfl⟩
        exact
          List.Chain.cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.Chain.cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.Chain.cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                List.Chain.nil))
      · refine
          ⟨[{   left := ⟨⟨⟩⟩
                right := single i
                hom := (a.le.trans inf_le_left).hom },
              { left := ⟨⟨⟩⟩
                right := pair i i'
                hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).hom },
              { left := ⟨⟨⟩⟩
                right := single i'
                hom := (b.le.trans inf_le_left).hom }, _], ?_, rfl⟩
        exact
          List.Chain.cons
            (Or.inl
              ⟨{  left := 𝟙 _
                  right := left i j }⟩)
            (List.Chain.cons
              (Or.inr
                ⟨{  left := 𝟙 _
                    right := left i i' }⟩)
              (List.Chain.cons
                (Or.inl
                  ⟨{  left := 𝟙 _
                      right := right i i' }⟩)
                (List.Chain.cons
                  (Or.inr
                    ⟨{  left := 𝟙 _
                        right := left i' j' }⟩)
                  List.Chain.nil)))⟩
def pairwiseDiagramIso :
    Pairwise.diagram U ≅ pairwiseToOpensLeCover U ⋙ fullSubcategoryInclusion _ where
  hom := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv := { app := by rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
def pairwiseCoconeIso :
    (Pairwise.cocone U).op ≅
      (Cones.postcomposeEquivalence (NatIso.op (pairwiseDiagramIso U : _) : _)).functor.obj
        ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op) :=
  Cones.ext (Iso.refl _) (by aesop_cat)
end SheafCondition
open SheafCondition
variable (F : Presheaf C X)
theorem isSheafOpensLeCover_iff_isSheafPairwiseIntersections :
    F.IsSheafOpensLeCover ↔ F.IsSheafPairwiseIntersections :=
  forall₂_congr fun _ U =>
    Equiv.nonempty_congr <|
      calc
        IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
            IsLimit ((F.mapCone (opensLeCoverCocone U).op).whisker (pairwiseToOpensLeCover U).op) :=
          (Functor.Initial.isLimitWhiskerEquiv (pairwiseToOpensLeCover U).op _).symm
        _ ≃ IsLimit (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op)) :=
          (IsLimit.equivIsoLimit F.mapConeWhisker.symm)
        _ ≃
            IsLimit
              ((Cones.postcomposeEquivalence _).functor.obj
                (F.mapCone ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          (IsLimit.postcomposeHomEquiv _ _).symm
        _ ≃
            IsLimit
              (F.mapCone
                ((Cones.postcomposeEquivalence _).functor.obj
                  ((opensLeCoverCocone U).op.whisker (pairwiseToOpensLeCover U).op))) :=
          (IsLimit.equivIsoLimit (Functor.mapConePostcomposeEquivalenceFunctor _).symm)
        _ ≃ IsLimit (F.mapCone (Pairwise.cocone U).op) :=
          IsLimit.equivIsoLimit ((Cones.functoriality _ _).mapIso (pairwiseCoconeIso U : _).symm)
theorem isSheaf_iff_isSheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections := by
  rw [isSheaf_iff_isSheafOpensLeCover,
    isSheafOpensLeCover_iff_isSheafPairwiseIntersections]
theorem isSheaf_iff_isSheafPreservesLimitPairwiseIntersections :
    F.IsSheaf ↔ F.IsSheafPreservesLimitPairwiseIntersections := by
  rw [isSheaf_iff_isSheafPairwiseIntersections]
  constructor
  · intro h ι U
    exact ⟨preservesLimit_of_preserves_limit_cone (Pairwise.coconeIsColimit U).op (h U).some⟩
  · intro h ι U
    haveI := (h U).some
    exact ⟨isLimitOfPreserves _ (Pairwise.coconeIsColimit U).op⟩
end TopCat.Presheaf
namespace TopCat.Sheaf
variable (F : X.Sheaf C) (U V : Opens X)
open CategoryTheory.Limits
def interUnionPullbackCone :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op)
      (F.1.map (homOfLE inf_le_right).op) :=
  PullbackCone.mk (F.1.map (homOfLE le_sup_left).op) (F.1.map (homOfLE le_sup_right).op) <| by
    rw [← F.1.map_comp, ← F.1.map_comp]
    congr 1
@[simp]
theorem interUnionPullbackCone_pt : (interUnionPullbackCone F U V).pt = F.1.obj (op <| U ⊔ V) :=
  rfl
@[simp]
theorem interUnionPullbackCone_fst :
    (interUnionPullbackCone F U V).fst = F.1.map (homOfLE le_sup_left).op :=
  rfl
@[simp]
theorem interUnionPullbackCone_snd :
    (interUnionPullbackCone F U V).snd = F.1.map (homOfLE le_sup_right).op :=
  rfl
variable
  (s :
    PullbackCone (F.1.map (homOfLE inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (homOfLE inf_le_right).op))
def interUnionPullbackConeLift : s.pt ⟶ F.1.obj (op (U ⊔ V)) := by
  let ι : ULift.{w} WalkingPair → Opens X := fun j => WalkingPair.casesOn j.down U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  refine
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.lift
        ⟨s.pt,
          { app := ?_
            naturality := ?_ }⟩ ≫
      F.1.map (eqToHom hι).op
  · rintro ((_ | _) | (_ | _))
    exacts [s.fst, s.snd, s.fst ≫ F.1.map (homOfLE inf_le_left).op,
      s.snd ≫ F.1.map (homOfLE inf_le_left).op]
  rintro ⟨i⟩ ⟨j⟩ f
  let g : j ⟶ i := f.unop
  have : f = g.op := rfl
  clear_value g
  subst this
  rcases i with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases j with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
  rcases g with ⟨⟩ <;>
  dsimp [Pairwise.diagram] <;>
  simp only [Category.id_comp, s.condition, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← cancel_mono (F.1.map (eqToHom <| inf_comm U V : U ⊓ V ⟶ _).op), Category.assoc,
    Category.assoc, ← F.1.map_comp, ← F.1.map_comp]
  exact s.condition.symm
theorem interUnionPullbackConeLift_left :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_left).op = s.fst := by
  erw [Category.assoc]
  simp_rw [← F.1.map_comp]
  exact
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _ <|
      op <| Pairwise.single <| ULift.up WalkingPair.left
theorem interUnionPullbackConeLift_right :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLE le_sup_right).op = s.snd := by
  erw [Category.assoc]
  simp_rw [← F.1.map_comp]
  exact
    (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 _).some.fac _ <|
      op <| Pairwise.single <| ULift.up WalkingPair.right
def isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V) := by
  let ι : ULift.{w} WalkingPair → Opens X := fun ⟨j⟩ => WalkingPair.casesOn j U V
  have hι : U ⊔ V = iSup ι := by
    ext
    rw [Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · rintro (h | h)
      exacts [⟨⟨WalkingPair.left⟩, h⟩, ⟨⟨WalkingPair.right⟩, h⟩]
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts [Or.inl h, Or.inr h]
  apply PullbackCone.isLimitAux'
  intro s
  use interUnionPullbackConeLift F U V s
  refine ⟨?_, ?_, ?_⟩
  · apply interUnionPullbackConeLift_left
  · apply interUnionPullbackConeLift_right
  · intro m h₁ h₂
    rw [← cancel_mono (F.1.map (eqToHom hι.symm).op)]
    apply (F.presheaf.isSheaf_iff_isSheafPairwiseIntersections.mp F.2 ι).some.hom_ext
    rintro ((_ | _) | (_ | _)) <;>
    rw [Category.assoc, Category.assoc]
    · erw [← F.1.map_comp]
      convert h₁
      apply interUnionPullbackConeLift_left
    · erw [← F.1.map_comp]
      convert h₂
      apply interUnionPullbackConeLift_right
    all_goals
      dsimp only [Functor.op, Pairwise.cocone_ι_app, Functor.mapCone_π_app, Cocone.op,
        Pairwise.coconeιApp, unop_op, op_comp, NatTrans.op]
      simp_rw [F.1.map_comp, ← Category.assoc]
      congr 1
      simp_rw [Category.assoc, ← F.1.map_comp]
    · convert h₁
      apply interUnionPullbackConeLift_left
    · convert h₂
      apply interUnionPullbackConeLift_right
def isProductOfDisjoint (h : U ⊓ V = ⊥) :
    IsLimit
      (BinaryFan.mk (F.1.map (homOfLE le_sup_left : _ ⟶ U ⊔ V).op)
        (F.1.map (homOfLE le_sup_right : _ ⟶ U ⊔ V).op)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)
end TopCat.Sheaf