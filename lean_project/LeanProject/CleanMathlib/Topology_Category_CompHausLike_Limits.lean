import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Category.CompHausLike.Basic
open CategoryTheory Limits Topology
namespace CompHausLike
universe w u
attribute [local instance] ConcreteCategory.instFunLike
section FiniteCoproducts
variable {P : TopCat.{max u w} → Prop} {α : Type w} [Finite α] (X : α → CompHausLike P)
abbrev HasExplicitFiniteCoproduct := HasProp P (Σ (a : α), X a)
variable [HasExplicitFiniteCoproduct X]
def finiteCoproduct : CompHausLike P := CompHausLike.of P (Σ (a : α), X a)
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x ↦ ⟨a, x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a ↦ X a)
def finiteCoproduct.desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a, x⟩ ↦ e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous
@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl
lemma finiteCoproduct.hom_ext {B : CompHausLike P} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q ↦ q x) at h
  exact h
abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X) :=
  mkCofanColimit _
    (fun s ↦ desc _ fun a ↦ s.inj a)
    (fun _ _ ↦ ι_desc _ _ _)
    fun _ _ hm ↦ finiteCoproduct.hom_ext _ _ _ fun a ↦
      (DFunLike.ext _ _ fun t ↦ congrFun (congrArg DFunLike.coe (hm a)) t)
lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2
lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩
lemma finiteCoproduct.ι_desc_apply {B : CompHausLike P} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  change (ι X a ≫ desc X π) _ = _
  simp only [ι_desc]
instance : HasCoproduct X where
  exists_colimit := ⟨finiteCoproduct.cofan X, finiteCoproduct.isColimit X⟩
variable (P) in
class HasExplicitFiniteCoproducts : Prop where
  hasProp {α : Type w} [Finite α] (X : α → CompHausLike.{max u w} P) : HasExplicitFiniteCoproduct X
attribute [nolint checkUnivs] HasExplicitFiniteCoproducts
attribute [instance] HasExplicitFiniteCoproducts.hasProp
instance [HasExplicitFiniteCoproducts.{w} P] (α : Type w) [Finite α] :
    HasColimitsOfShape (Discrete α) (CompHausLike P) where
  has_colimit _ := hasColimitOfIso Discrete.natIsoFunctor
instance [HasExplicitFiniteCoproducts.{w} P] : HasFiniteCoproducts (CompHausLike.{max u w} P) where
  out n := by
    let α := ULift.{w} (Fin n)
    let e : Discrete α ≌ Discrete (Fin n) := Discrete.equivalence Equiv.ulift
    exact hasColimitsOfShape_of_equivalence e
variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{0} P]
example : HasFiniteCoproducts (CompHausLike.{u} P) := inferInstance
lemma finiteCoproduct.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (finiteCoproduct.ι X a) :=
  .sigmaMk (σ := fun a ↦ X a)
@[deprecated (since := "2024-10-18")]
alias finiteCoproduct.openEmbedding_ι := finiteCoproduct.isOpenEmbedding_ι
lemma Sigma.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (Sigma.ι X a) := by
  refine IsOpenEmbedding.of_comp _ (homeoOfIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (finiteCoproduct.isColimit X))).isOpenEmbedding ?_
  convert finiteCoproduct.isOpenEmbedding_ι X a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp
@[deprecated (since := "2024-10-18")]
alias Sigma.openEmbedding_ι := Sigma.isOpenEmbedding_ι
instance (P) [HasExplicitFiniteCoproducts.{0} P] :
    PreservesFiniteCoproducts (compHausLikeToTop P) := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) (compHausLikeToTop P) from
    preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm
  apply preservesColimit_of_preserves_colimit_cocone (CompHausLike.finiteCoproduct.isColimit _)
  exact TopCat.sigmaCofanIsColimit _
noncomputable instance {P' : TopCat.{u} → Prop}
    (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesFiniteCoproducts (toCompHausLike h) := by
  have : PreservesFiniteCoproducts (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesFiniteCoproducts (compHausLikeToTop _))
  exact preservesFiniteCoproducts_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')
end FiniteCoproducts
section Pullbacks
variable {P : TopCat.{u} → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B)
abbrev HasExplicitPullback := HasProp P { xy : X × Y | f xy.fst = g xy.snd }
variable [HasExplicitPullback f g] 
def pullback : CompHausLike P :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.continuous.comp continuous_fst)
      (g.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x, _⟩, _⟩ ↦ x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_,y⟩,_⟩ ↦ y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val
@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_,h⟩; exact h
def pullback.lift {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z ↦ ⟨⟨a z, b z⟩, by apply_fun (fun q ↦ q z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩
@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl
@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl
lemma pullback.hom_ext {Z : CompHausLike P} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (fun q ↦ q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd
@[simps! pt π]
def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s ↦ pullback.lift f g s.fst s.snd s.condition)
    (fun _ ↦ pullback.lift_fst _ _ _ _ _)
    (fun _ ↦ pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm ↦ pullback.hom_ext _ _ _ _ (hm .left) (hm .right))
instance : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩
noncomputable instance : CreatesLimit (cospan f g) (compHausLikeToTop P) := by
  refine createsLimitOfFullyFaithfulOfIso (pullback f g)
    (((TopCat.pullbackConeIsLimit f g).conePointUniqueUpToIso
        (limit.isLimit _)) ≪≫ Limits.lim.mapIso (?_ ≪≫ (diagramIsoCospan _).symm))
  exact Iso.refl _
noncomputable instance : PreservesLimit (cospan f g) (compHausLikeToTop P) :=
  preservesLimit_of_createsLimit_and_hasLimit _ _
noncomputable instance {P' : TopCat → Prop}
    (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesLimit (cospan f g) (toCompHausLike h) := by
  have : PreservesLimit (cospan f g) (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesLimit _ (compHausLikeToTop _))
  exact preservesLimit_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')
variable (P) in
class HasExplicitPullbacks : Prop where
  hasProp {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) : HasExplicitPullback f g
attribute [instance] HasExplicitPullbacks.hasProp
instance [HasExplicitPullbacks P] : HasPullbacks (CompHausLike P) where
  has_limit F := hasLimitOfIso (diagramIsoCospan F).symm
variable (P) in
class HasExplicitPullbacksOfInclusions [HasExplicitFiniteCoproducts.{0} P] : Prop where
  hasProp : ∀ {X Y Z : CompHausLike P} (f : Z ⟶ X ⨿ Y), HasExplicitPullback coprod.inl f
attribute [instance] HasExplicitPullbacksOfInclusions.hasProp
instance [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P] :
    HasExplicitPullbacksOfInclusions P where
  hasProp _ := inferInstance
end Pullbacks
section FiniteCoproducts
variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{0} P]
instance [HasExplicitPullbacksOfInclusions P] : HasPullbacksOfInclusions (CompHausLike P) where
  hasPullbackInl _ := inferInstance
theorem hasPullbacksOfInclusions
    (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
      (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
    HasExplicitPullbacksOfInclusions P :=
  { hasProp := by
      intro _ _ _ f
      apply hP'
      exact Sigma.isOpenEmbedding_ι _ _ }
noncomputable instance [HasExplicitPullbacksOfInclusions P] :
    PreservesPullbacksOfInclusions (compHausLikeToTop P) :=
  { preservesPullbackInl := by
      intros X Y Z f
      infer_instance }
instance [HasExplicitPullbacksOfInclusions P] : FinitaryExtensive (CompHausLike P) :=
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)
theorem finitaryExtensive (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
    (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
      FinitaryExtensive (CompHausLike P) :=
  have := hasPullbacksOfInclusions hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)
end FiniteCoproducts
section Terminal
variable {P : TopCat.{u} → Prop}
def isTerminalPUnit [HasProp P PUnit.{u+1}] :
    IsTerminal (CompHausLike.of P PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1}) := fun _ ↦
    ⟨⟨⟨fun _ ↦ PUnit.unit, continuous_const⟩⟩, fun _ ↦ rfl⟩
  Limits.IsTerminal.ofUnique _
end Terminal
end CompHausLike