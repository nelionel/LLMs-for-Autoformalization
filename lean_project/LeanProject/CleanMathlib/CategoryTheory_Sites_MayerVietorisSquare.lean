import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Square
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Sheafification
universe v v' u u'
namespace CategoryTheory
open Limits Opposite
variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
lemma Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff
    [HasWeakSheafify J (Type v)]
    (F : Sheaf J (Type v)) (sq : Square C) :
    (sq.op.map ((yoneda ⋙ presheafToSheaf J _).op ⋙ yoneda.obj F)).IsPullback ↔
      (sq.op.map F.val).IsPullback := by
  refine Square.IsPullback.iff_of_equiv _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv) ?_ ?_ ?_ ?_
  all_goals
    ext x
    dsimp
    rw [yonedaEquiv_naturality]
    erw [Adjunction.homEquiv_naturality_left]
    rfl
namespace GrothendieckTopology
variable (J)
structure MayerVietorisSquare [HasWeakSheafify J (Type v)] extends Square C where
  mono_f₁₃ : Mono toSquare.f₁₃ := by infer_instance
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout
namespace MayerVietorisSquare
attribute [instance] mono_f₁₃
variable {J}
section
variable [HasWeakSheafify J (Type v)]
@[simps toSquare]
noncomputable def mk' (sq : Square C) [Mono sq.f₁₃]
    (H : ∀ (F : Sheaf J (Type v)), (sq.op.map F.val).IsPullback) :
    J.MayerVietorisSquare where
  toSquare := sq
  isPushout := by
    rw [Square.isPushout_iff_op_map_yoneda_isPullback]
    intro F
    exact (F.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff sq).2 (H F)
@[simps! toSquare]
noncomputable def mk_of_isPullback (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h₁ : sq.IsPullback) (h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄) :
    J.MayerVietorisSquare :=
  have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F ↦ by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ F.2.amalgamateOfArrows _ h₂
        (fun j ↦ WalkingPair.casesOn j s.fst s.snd)
        (fun W ↦ by
          rintro (_|_) (_|_) a b fac
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
            rfl
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac
            simpa using s.condition =≫ F.val.map φ.op
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac.symm
            simpa using s.condition.symm =≫ F.val.map φ.op
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₃₄] using fac
            rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
    · apply F.2.hom_ext_ofArrows _ h₂
      rintro (_|_)
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
        exact hm₁
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
        exact hm₂)
variable (S : J.MayerVietorisSquare)
lemma isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrp.{v}] :
    (S.map (yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.free ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrp.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrp.free)).app
        (S.map yoneda))
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  (S.toSquare.op.map P).IsPullback
lemma sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) :
    S.SheafCondition P ↔ ∀ (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj X) :=
  Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)
abbrev toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    P.obj (op S.X₄) → Types.PullbackObj (P.map S.f₁₂.op) (P.map S.f₁₃.op) :=
  (S.toSquare.op.map P).pullbackCone.toPullbackObj
lemma sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P) := by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h ↦ this h.isLimit, fun h ↦ Square.IsPullback.mk _ (this.symm h)⟩
namespace SheafCondition
variable {S}
variable {P : Cᵒᵖ ⥤ Type v'} (h : S.SheafCondition P)
include h
lemma bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P) := by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]
lemma ext {x y : P.obj (op S.X₄)}
    (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y)
    (h₂ : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y :=
  h.bijective_toPullbackObj.injective (by ext <;> assumption)
variable (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
  (huv : P.map S.f₁₂.op u = P.map S.f₁₃.op v)
noncomputable def glue : P.obj (op S.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩
@[simp]
lemma map_f₂₄_op_glue : P.map S.f₂₄.op (h.glue u v huv) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _
@[simp]
lemma map_f₃₄_op_glue : P.map S.f₃₄.op (h.glue u v huv) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _
end SheafCondition
lemma sheafCondition_of_sheaf {A : Type u'} [Category.{v} A]
    (F : Sheaf J A) : S.SheafCondition F.val := by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact (Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff _ S.toSquare).1
    (S.isPushout.op.map
      (yoneda.obj ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.cond X.unop)⟩))
end
variable [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrp.{v}]
  (S : J.MayerVietorisSquare)
@[simps]
noncomputable def shortComplex :
    ShortComplex (Sheaf J AddCommGrp.{v}) where
  X₁ := (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ AddCommGrp.free)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ AddCommGrp.free) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ AddCommGrp.free)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ AddCommGrp.free)
  f :=
    biprod.lift
      ((presheafToSheaf J _).map (whiskerRight (yoneda.map S.f₁₂) _))
      (-(presheafToSheaf J _).map (whiskerRight (yoneda.map S.f₁₃) _))
  g :=
    biprod.desc
      ((presheafToSheaf J _).map (whiskerRight (yoneda.map S.f₂₄) _))
      ((presheafToSheaf J _).map (whiskerRight (yoneda.map S.f₃₄) _))
  zero := (S.map (yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.free ⋙
      presheafToSheaf J _)).cokernelCofork.condition
instance : Mono S.shortComplex.f := by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd
instance : Epi S.shortComplex.g :=
  (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2
lemma shortComplex_exact : S.shortComplex.Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork
lemma shortComplex_shortExact : S.shortComplex.ShortExact where
  exact := S.shortComplex_exact
end MayerVietorisSquare
end GrothendieckTopology
end CategoryTheory