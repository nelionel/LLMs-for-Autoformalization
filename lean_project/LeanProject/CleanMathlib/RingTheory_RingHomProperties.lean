import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IsTensorProduct
universe u
open CategoryTheory Opposite CategoryTheory.Limits
namespace RingHom
variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)
section RespectsIso
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : S →+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)
variable {P}
theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun H => by
    convert hP.2 (f ≫ g) (asIso f).symm.commRingCatIsoToRingEquiv H
    exact (IsIso.inv_hom_id_assoc _ _).symm, hP.2 g (asIso f).commRingCatIsoToRingEquiv⟩
theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun H => by
    convert hP.1 (f ≫ g) (asIso g).symm.commRingCatIsoToRingEquiv H
    change f = f ≫ g ≫ inv g
    simp, hP.1 f (asIso g).commRingCatIsoToRingEquiv⟩
theorem RespectsIso.is_localization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type u}
    (R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R →+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom _)).symm.trans ?_
  refine (hP.cancel_right_isIso (CommRingCat.ofHom _) e₂.toCommRingCatIso.hom).symm.trans ?_
  rw [← eq_iff_iff]
  congr 1
  let e := (e₂ : Localization.Away (f r) →+* S').comp
      (((IsLocalization.map (Localization.Away (f r)) f
            (by rintro x ⟨n, rfl⟩; use n; simp : Submonoid.powers r ≤ Submonoid.comap f
                (Submonoid.powers (f r)))) : Localization.Away r →+* Localization.Away (f r)).comp
                (e₁ : R' →+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]
end RespectsIso
section StableUnderComposition
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    ∀ (f : R →+* S) (g : S →+* T) (_ : P f) (_ : P g), P (g.comp f)
variable {P}
theorem StableUnderComposition.respectsIso (hP : RingHom.StableUnderComposition @P)
    (hP' : ∀ {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S), P e.toRingHom) :
    RingHom.RespectsIso @P := by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]
end StableUnderComposition
section IsStableUnderBaseChange
def IsStableUnderBaseChange : Prop :=
  ∀ (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
        ∀ [Algebra.IsPushout R S R' S'], P (algebraMap R S) → P (algebraMap R' S')
theorem IsStableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ :
      ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
        ∀ [Algebra R S] [Algebra R T],
          P (algebraMap R T) →
            P (Algebra.TensorProduct.includeLeftRingHom : S →+* TensorProduct R S T)) :
    IsStableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
      (IsScalarTower.toAlgHom R S S')
  have : ∀ x, e x = f' x := by
    intro x
    change e.toLinearMap.restrictScalars R x = f'.toLinearMap x
    congr 1
    apply TensorProduct.ext'
    intro x y
    simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  convert h₁.1 (_ : R' →+* TensorProduct R R' S) (_ : TensorProduct R R' S ≃+* S')
      (h₂ H : P (_ : R' →+* TensorProduct R R' S))
  swap
  · refine { e with map_mul' := fun x y => ?_ }
    change e (x * y) = e x * e y
    simp_rw [this]
    exact map_mul f' _ _
  · ext x
    change _ = e (x ⊗ₜ[R] 1)
    rw [h.symm.1.equiv_tmul, Algebra.smul_def, AlgHom.toLinearMap_apply, map_one, mul_one]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
theorem IsStableUnderBaseChange.pushout_inl (hP : RingHom.IsStableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g) :
    P (pushout.inl _ _ : S ⟶ pushout f g) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left,
    hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (TensorProduct R S T)
  exact H
end IsStableUnderBaseChange
section ToMorphismProperty
def toMorphismProperty : MorphismProperty CommRingCat := fun _ _ f ↦ P f
variable {P}
lemma toMorphismProperty_respectsIso_iff :
    RespectsIso P ↔ (toMorphismProperty P).RespectsIso := by
  refine ⟨fun h ↦ MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.RespectsIso.postcomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f) hf
  · intro X Y Z _ _ _ f e
    exact MorphismProperty.RespectsIso.precomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f)
end ToMorphismProperty
end RingHom