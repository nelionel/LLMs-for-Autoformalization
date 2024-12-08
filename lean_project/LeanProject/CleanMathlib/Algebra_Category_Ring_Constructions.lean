import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.RingTheory.TensorProduct.Basic
suppress_compilation
universe u u'
open CategoryTheory Limits TensorProduct
namespace CommRingCat
section Pushout
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
def pushoutCocone : Limits.PushoutCocone
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) := by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A ⊗[R] B)
  · exact Algebra.TensorProduct.includeLeftRingHom (A := A)
  · exact Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm
@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone R A B).inl = Algebra.TensorProduct.includeLeftRingHom (A := A) :=
  rfl
@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone R A B).inr = Algebra.TensorProduct.includeRight.toRingHom (A := B) :=
  rfl
@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone R A B).pt = CommRingCat.of (A ⊗[R] B) :=
  rfl
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone R A B) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.comp (algebraMap R A))
    let f' : A →ₐ[R] s.pt :=
      { s.inl with
        commutes' := fun r => rfl }
    let g' : B →ₐ[R] s.pt :=
      { s.inr with
        commutes' := DFunLike.congr_fun ((s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
              (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm) }
    letI : Algebra R (pushoutCocone R A B).pt := show Algebra R (A ⊗[R] B) by infer_instance
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply (A := A) _ _ x
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply (B := B) _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.pt :=
      { h with
        commutes' := fun r => by
          change h (algebraMap R A r ⊗ₜ[R] 1) = s.inl (algebraMap R A r)
          rw [← eq1]
          simp only [pushoutCocone_pt, coe_of, AlgHom.toRingHom_eq_coe]
          rfl }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [f', g', ← eq1, pushoutCocone_pt, ← eq2, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_mk]
    change _ = h (a ⊗ₜ 1) * h (1 ⊗ₜ b)
    rw [← h.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
lemma isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩
end Pushout
section Terminal
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) := by
  refine IsTerminal.ofUnique (h := fun X => ⟨⟨⟨⟨1, rfl⟩, fun _ _ => rfl⟩, ?_, ?_⟩, ?_⟩)
  · rfl
  · intros; simp only [coe_of, Pi.one_apply, self_eq_add_right]; ext
  · intros f; ext; rfl
instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨⟨⟨1, rfl, fun _ _ => rfl⟩, by ext; rfl, ?_⟩⟩
  ext x
  have e : (0 : X) = 1 := by
    rw [← f.map_one, ← f.map_zero]
    congr
  replace e : 0 * x = 1 * x := congr_arg (· * x) e
  rw [one_mul, zero_mul, ← f.map_zero] at e
  exact e
theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)
def zIsInitial : IsInitial (CommRingCat.of ℤ) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨Int.castRingHom R⟩, fun a => a.ext_int _⟩)
def isInitial : IsInitial (CommRingCat.of (ULift.{u} ℤ)) :=
  IsInitial.ofUnique (h := fun R ↦ ⟨⟨(Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ ↦ by
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0, u} (α := ℤ)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int⟩)
end Terminal
section Product
variable (A B : CommRingCat.{u})
@[simps! pt]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift c := RingHom.prod (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩)
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right,
      FunctorToTypes.map_comp_apply, forget_map, coe_of, RingHom.prod_apply] <;>
    rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 := congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 := congr_hom (h ⟨WalkingPair.right⟩) x
    dsimp at eq1 eq2
    erw [← eq1, ← eq2]
    rfl
end Product
section Pi
variable {ι : Type u} (R : ι → CommRingCat.{u})
@[simps! pt]
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (Pi.evalRingHom _)
def piFanIsLimit : IsLimit (piFan R) where
  lift s := Pi.ringHom fun i ↦ s.π.1 ⟨i⟩
  fac s i := by rfl
  uniq _ _ h := DFunLike.ext _ _ fun x ↦ funext fun i ↦ DFunLike.congr_fun (h ⟨i⟩) x
def piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) → R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩
def _root_.RingEquiv.piEquivPi (R : ι → Type u) [∀ i, CommRing (R i)] :
    (∏ᶜ (fun i : ι ↦ CommRingCat.of (R i)) : CommRingCat.{u}) ≃+* ((i : ι) → R i) :=
  (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv
end Pi
section Equalizer
variable {A B : CommRingCat.{u}} (f g : A ⟶ B)
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f g).subtype) <| by
      ext ⟨x, e⟩
      simpa using e
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  haveI : SubsemiringClass (Subring A) ((parallelPair f g).obj WalkingParallelPair.zero) :=
    show SubsemiringClass (Subring A) A by infer_instance
  use s.ι.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x : _)
  constructor
  · ext
    rfl
  · intro m hm
    exact RingHom.ext fun x => Subtype.ext <| ConcreteCategory.congr_hom hm x
instance : IsLocalHom (equalizerFork f g).ι := by
  constructor
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  have : y ∈ RingHom.eqLocus f g := by
    apply (f.isUnit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one]
  rw [isUnit_iff_exists_inv]
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩
@[instance]
theorem equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero) := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  rw [← IsIso.comp_inv_eq] at this
  rw [← this]
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalHom ((lim.map _ ≫ _ ≫ (equalizerFork _ _).ι) ≫ _)
  infer_instance
@[deprecated (since := "2024-10-10")]
alias equalizer_ι_isLocalRingHom := equalizer_ι_isLocalHom
open CategoryTheory.Limits.WalkingParallelPair Opposite
open CategoryTheory.Limits.WalkingParallelPairHom
instance equalizer_ι_is_local_ring_hom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F (Opposite.op WalkingParallelPair.one)) := by
  have : _ = limit.π F (walkingParallelPairOpEquiv.functor.obj _) :=
    (limit.isoLimitCone_inv_π
        ⟨_, IsLimit.whiskerEquivalence (limit.isLimit F) walkingParallelPairOpEquiv⟩
        WalkingParallelPair.zero : _)
  erw [← this]
  infer_instance
end Equalizer
section Pullback
def pullbackCone {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))).subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)
def pullbackConeIsLimit {A B C : CommRingCat.{u}} (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    apply (s.fst.prod s.snd).codRestrict
    intro x
    exact congr_arg (fun f : s.pt →+* C => f x) s.condition
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    refine RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) e₁ : _)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) e₂ : _)
    rw [← eq1, ← eq2]
    rfl
end Pullback
end CommRingCat