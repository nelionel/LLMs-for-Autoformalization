import Mathlib.Algebra.Homology.Embedding.Basic
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
open CategoryTheory Limits ZeroObject
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
namespace HomologicalComplex
section
variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (e : c.Embedding c')
class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : ∀ i, e.f i ≠ i') : IsZero (K.X i')
lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'
include e' in
variable {K L} in
lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)
class IsSupported : Prop where
  exactAt (i' : ι') (hi' : ∀ i, e.f i ≠ i') : K.ExactAt i'
lemma exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    K.ExactAt i' :=
  IsSupported.exactAt i' hi'
include e' in
variable {K L} in
lemma isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' :=
    (K.exactAt_of_isSupported e i' hi').of_iso e'
instance [K.IsStrictlySupported e] : K.IsSupported e where
  exactAt i' hi' := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')
structure IsStrictlySupportedOutside : Prop where
  isZero (i : ι) : IsZero (K.X (e.f i))
structure IsSupportedOutside : Prop where
  exactAt (i : ι) : K.ExactAt (e.f i)
variable {K e} in
lemma IsStrictlySupportedOutside.isSupportedOutside (h : K.IsStrictlySupportedOutside e) :
    K.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)
instance [HasZeroObject C] : (0 : HomologicalComplex C c').IsStrictlySupported e where
  isZero i _ := (eval _ _ i).map_isZero (Limits.isZero_zero _)
lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)
instance [K.IsStrictlySupported e] : K.op.IsStrictlySupported e.op where
  isZero j hj' := (K.isZero_X_of_isStrictlySupported e j hj').op
end
section
variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (K : HomologicalComplex C c') (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')
instance map_isStrictlySupported [K.IsStrictlySupported e] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e where
  isZero i' hi' := by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id, (K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0, F.map_zero]
end
end HomologicalComplex