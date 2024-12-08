import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.Flat.Equalizer
noncomputable section
universe v u
open TensorProduct CategoryTheory Limits
variable {R S : CommRingCat.{u}}
namespace CommRingCat.Under
section Algebra
variable [Algebra R S]
section Pi
variable {ι : Type u} (P : ι → Under R)
def piFan : Fan P :=
  Fan.mk (Under.mk <| ofHom <| Pi.ringHom (fun i ↦ (P i).hom))
    (fun i ↦ Under.homMk (Pi.evalRingHom _ i))
def piFanIsLimit : IsLimit (piFan P) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeFanMkEquiv (Under.forget R) P _).symm <|
      CommRingCat.piFanIsLimit (fun i ↦ (P i).right)
variable (S) in
def tensorProductFan : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| S ⊗[R] ∀ i, (P i).right)
    (fun i ↦ AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j ↦ (P j).right) i))
variable (S) in
def tensorProductFan' : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| ∀ i, S ⊗[R] (P i).right)
    (fun i ↦ AlgHom.toUnder <| Pi.evalAlgHom S _ i)
def tensorProductFanIso [Fintype ι] [DecidableEq ι] :
    tensorProductFan S P ≅ tensorProductFan' S P :=
  Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder <| fun i ↦ by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [AlgHom.toUnder_right, map_zero, Under.comp_right, comp_apply,
        AlgEquiv.toUnder_hom_right_apply, Pi.evalAlgHom_apply, Pi.zero_apply]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all
open Classical in
def tensorProductFanIsLimit [Finite ι] : IsLimit (tensorProductFan S P) :=
  letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)
def piFanTensorProductIsLimit [Finite ι] : IsLimit ((tensorProd R S).mapCone (Under.piFan P)) :=
  (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm <| tensorProductFanIsLimit P
instance (J : Type u) [Finite J] (f : J → Under R) :
    PreservesLimit (Discrete.functor f) (tensorProd R S) :=
  let c : Fan _ := Under.piFan f
  have hc : IsLimit c := Under.piFanIsLimit f
  preservesLimit_of_preserves_limit_cone hc (piFanTensorProductIsLimit f)
instance (J : Type) [Finite J] :
    PreservesLimitsOfShape (Discrete J) (tensorProd R S) :=
  let J' : Type u := ULift.{u} J
  have : PreservesLimitsOfShape (Discrete J') (tensorProd R S) :=
    preservesLimitsOfShape_of_discrete (tensorProd R S)
  let e : Discrete J' ≌ Discrete J := Discrete.equivalence Equiv.ulift
  preservesLimitsOfShape_of_equiv e (R.tensorProd S)
instance : PreservesFiniteProducts (tensorProd R S) where
  preserves J := { }
end Pi
section Equalizer
lemma equalizer_comp {A B : Under R} (f g : A ⟶ B) :
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f =
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ g := by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property
def equalizerFork {A B : Under R} (f g : A ⟶ B) :
    Fork f g :=
  Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])
@[simp]
lemma equalizerFork_ι {A B : Under R} (f g : A ⟶ B) :
    (Under.equalizerFork f g).ι = (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder := rfl
def equalizerFork' {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) :
    Fork f.toUnder g.toUnder :=
  Fork.ofι ((AlgHom.equalizer f g).val.toUnder) <| by ext a; exact a.property
@[simp]
lemma equalizerFork'_ι {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) :
    (Under.equalizerFork' f g).ι = (AlgHom.equalizer f g).val.toUnder := rfl
def equalizerForkIsLimit {A B : Under R} (f g : A ⟶ B) :
    IsLimit (Under.equalizerFork f g) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeForkEquiv (Under.forget R) (equalizer_comp f g)).invFun <|
      CommRingCat.equalizerForkIsLimit f.right g.right
def equalizerFork'IsLimit {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f g : A →ₐ[R] B) :
    IsLimit (Under.equalizerFork' f g) :=
  Under.equalizerForkIsLimit f.toUnder g.toUnder
def tensorProdEqualizer {A B : Under R} (f g : A ⟶ B) :
    Fork ((tensorProd R S).map f) ((tensorProd R S).map g) :=
  Fork.ofι
    ((tensorProd R S).map ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)) <| by
    rw [← Functor.map_comp, equalizer_comp, Functor.map_comp]
@[simp]
lemma tensorProdEqualizer_ι {A B : Under R} (f g : A ⟶ B) :
    (tensorProdEqualizer f g).ι = (tensorProd R S).map
      ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder) :=
  rfl
def equalizerForkTensorProdIso [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    tensorProdEqualizer f g ≅ Under.equalizerFork'
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f))
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom g)) :=
  Fork.ext (AlgHom.tensorEqualizerEquiv S S (toAlgHom f) (toAlgHom g)).toUnder <| by
    ext
    apply AlgHom.coe_tensorEqualizer
def tensorProdMapEqualizerForkIsLimit [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    IsLimit ((tensorProd R S).mapCone <| Under.equalizerFork f g) :=
  (isLimitMapConeForkEquiv (tensorProd R S) _).symm <|
    (IsLimit.equivIsoLimit (equalizerForkTensorProdIso f g).symm) <|
    Under.equalizerFork'IsLimit _ _
instance [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    PreservesLimit (parallelPair f g) (tensorProd R S) :=
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let hc' : IsLimit ((tensorProd R S).mapCone c) :=
    tensorProdMapEqualizerForkIsLimit f g
  preservesLimit_of_preserves_limit_cone hc hc'
instance [Module.Flat R S] : PreservesLimitsOfShape WalkingParallelPair (tensorProd R S) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm
instance [Module.Flat R S] : PreservesFiniteLimits (tensorProd R S) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (tensorProd R S)
end Equalizer
end Algebra
variable (f : R ⟶ S)
instance : PreservesFiniteProducts (Under.pushout f) where
  preserves _ :=
    letI : Algebra R S := RingHom.toAlgebra f
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)
lemma preservesFiniteLimits_of_flat (hf : RingHom.Flat f) :
    PreservesFiniteLimits (Under.pushout f) where
  preservesFiniteLimits _ :=
    letI : Algebra R S := RingHom.toAlgebra f
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)
end CommRingCat.Under