import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
noncomputable section
namespace NumberField
open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion DedekindDomain IsDedekindDomain
open scoped Classical
variable (K : Type*) [Field K]
def InfiniteAdeleRing := (v : InfinitePlace K) → v.completion
namespace InfiniteAdeleRing
instance : CommRing (InfiniteAdeleRing K) := Pi.commRing
instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩
instance [NumberField K] : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w
instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace
instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing
instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _
@[simp]
theorem algebraMap_apply (x : K) (v : InfinitePlace K) :
    algebraMap K (InfiniteAdeleRing K) x v = x := rfl
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite
abbrev ringEquiv_mixedSpace :
    InfiniteAdeleRing K ≃+* mixedEmbedding.mixedSpace K :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquiv_real_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquiv_complex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))
@[simp]
theorem ringEquiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbedding_of_isReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K _ x) := by
  ext v <;> simp only [ringEquiv_mixedSpace_apply, algebraMap_apply,
    ringEquiv_real_of_isReal, ringEquiv_complex_of_isComplex, extensionEmbedding,
    extensionEmbedding_of_isReal, extensionEmbedding_of_comp, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.isUniformInducing_of_comp <| v.1.norm_embedding_of_isReal v.2).uniformContinuous x]
    exact mixedEmbedding.mixedEmbedding_apply_ofIsReal _ _ _
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.isUniformInducing_of_comp <| v.1.norm_embedding_eq).uniformContinuous x]
    exact mixedEmbedding.mixedEmbedding_apply_ofIsComplex _ _ _
end InfiniteAdeleRing
variable [NumberField K]
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K
namespace AdeleRing
instance : CommRing (AdeleRing K) := Prod.instCommRing
instance : Inhabited (AdeleRing K) := ⟨0⟩
instance : TopologicalSpace (AdeleRing K) := instTopologicalSpaceProd
instance : TopologicalRing (AdeleRing K) := instTopologicalRingProd
instance : Algebra K (AdeleRing K) := Prod.algebra _ _ _
@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K (AdeleRing K) x).1 v = x := rfl
@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (AdeleRing K) x).2 v = x := rfl
theorem algebraMap_injective : Function.Injective (algebraMap K (AdeleRing K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1
abbrev principalSubgroup : AddSubgroup (AdeleRing K) := (algebraMap K _).range.toAddSubgroup
end AdeleRing
end NumberField