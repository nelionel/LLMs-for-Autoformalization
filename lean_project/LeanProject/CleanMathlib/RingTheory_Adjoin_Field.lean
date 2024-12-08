import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
noncomputable section
open Polynomial
section Embeddings
variable (F : Type*) [Field F]
open AdjoinRoot in
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type*} [CommRing R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm <| AlgEquiv.ofBijective (Minpoly.toAdjoin F x) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun P₁ hP₁ ↦ ?_, Minpoly.toAdjoin.surjective F x⟩
    obtain ⟨P, rfl⟩ := mk_surjective P₁
    refine AdjoinRoot.mk_eq_zero.mpr (minpoly.dvd F x ?_)
    rwa [Minpoly.toAdjoin_apply', liftHom_mk, ← Subalgebra.coe_eq_zero, aeval_subalgebra_coe] at hP₁
noncomputable def Algebra.adjoin.liftSingleton {S T : Type*}
    [CommRing S] [CommRing T] [Algebra F S] [Algebra F T]
    (x : S) (y : T) (h : aeval y (minpoly F x) = 0) :
    Algebra.adjoin F {x} →ₐ[F] T :=
  (AdjoinRoot.liftHom _ y h).comp (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F x).toAlgHom
open Finset
theorem Polynomial.lift_of_splits {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] (s : Finset K) : (∀ x ∈ s, IsIntegral F x ∧
      Splits (algebraMap F L) (minpoly F x)) → Nonempty (Algebra.adjoin F (s : Set K) →ₐ[F] L) := by
  classical
    refine Finset.induction_on s (fun _ ↦ ?_) fun a s _ ih H ↦ ?_
    · rw [coe_empty, Algebra.adjoin_empty]
      exact ⟨(Algebra.ofId F L).comp (Algebra.botEquiv F K)⟩
    rw [forall_mem_insert] at H
    rcases H with ⟨⟨H1, H2⟩, H3⟩
    cases' ih H3 with f
    choose H3 _ using H3
    rw [coe_insert, Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin]
    set Ks := Algebra.adjoin F (s : Set K)
    haveI : FiniteDimensional F Ks := ((Submodule.fg_iff_finiteDimensional _).1
      (fg_adjoin_of_finite s.finite_toSet H3)).of_subalgebra_toSubmodule
    letI := fieldOfFiniteDimensional F Ks
    letI := (f : Ks →+* L).toAlgebra
    have H5 : IsIntegral Ks a := H1.tower_top
    have H6 : (minpoly Ks a).Splits (algebraMap Ks L) := by
      refine splits_of_splits_of_dvd _ ((minpoly.monic H1).map (algebraMap F Ks)).ne_zero
        ((splits_map_iff _ _).2 ?_) (minpoly.dvd _ _ ?_)
      · rw [← IsScalarTower.algebraMap_eq]
        exact H2
      · rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨y, hy⟩ := Polynomial.exists_root_of_splits _ H6 (minpoly.degree_pos H5).ne'
    exact ⟨Subalgebra.ofRestrictScalars F _ <| Algebra.adjoin.liftSingleton Ks a y hy⟩
end Embeddings
variable {R K L M : Type*} [CommRing R] [Field K] [Field L] [CommRing M] [Algebra R K]
  [Algebra R M] {x : L}
section
variable [Algebra R L]
theorem IsIntegral.mem_range_algHom_of_minpoly_splits
    (int : IsIntegral R x) (h : Splits (algebraMap R K) (minpoly R x))(f : K →ₐ[R] L) :
    x ∈ f.range :=
  show x ∈ Set.range f from Set.image_subset_range _ ((minpoly R x).rootSet K) <| by
    rw [image_rootSet h f, mem_rootSet']
    exact ⟨((minpoly.monic int).map _).ne_zero, minpoly.aeval R x⟩
theorem IsIntegral.mem_range_algebraMap_of_minpoly_splits [Algebra K L] [IsScalarTower R K L]
    (int : IsIntegral R x) (h : Splits (algebraMap R K) (minpoly R x)) :
    x ∈ (algebraMap K L).range :=
  int.mem_range_algHom_of_minpoly_splits h (IsScalarTower.toAlgHom R K L)
theorem minpoly_neg_splits [Algebra K L] {x : L} (g : (minpoly K x).Splits (algebraMap K L)) :
    (minpoly K (-x)).Splits (algebraMap K L) := by
  rw [minpoly.neg]
  apply splits_mul _ _ g.comp_neg_X
  simpa only [map_pow, map_neg, map_one] using
    splits_C (algebraMap K L) ((-1) ^ (minpoly K x).natDegree)
theorem minpoly_add_algebraMap_splits [Algebra K L] {x : L} (r : K)
    (g : (minpoly K x).Splits (algebraMap K L)) :
    (minpoly K (x + algebraMap K L r)).Splits (algebraMap K L) := by
  simpa [minpoly.add_algebraMap] using g.comp_X_sub_C r
theorem minpoly_sub_algebraMap_splits [Algebra K L] {x : L} (r : K)
    (g : (minpoly K x).Splits (algebraMap K L)) :
    (minpoly K (x - algebraMap K L r)).Splits (algebraMap K L) := by
  simpa only [sub_eq_add_neg, map_neg] using minpoly_add_algebraMap_splits (-r) g
theorem minpoly_algebraMap_add_splits [Algebra K L] {x : L} (r : K)
    (g : (minpoly K x).Splits (algebraMap K L)) :
    (minpoly K (algebraMap K L r + x)).Splits (algebraMap K L) := by
  simpa only [add_comm] using minpoly_add_algebraMap_splits r g
theorem minpoly_algebraMap_sub_splits [Algebra K L] {x : L} (r : K)
    (g : (minpoly K x).Splits (algebraMap K L)) :
    (minpoly K (algebraMap K L r - x)).Splits (algebraMap K L) := by
  simpa only [neg_sub] using minpoly_neg_splits (minpoly_sub_algebraMap_splits r g)
end
variable [Algebra K M] [IsScalarTower R K M] {x : M}
theorem IsIntegral.minpoly_splits_tower_top' (int : IsIntegral R x) {f : K →+* L}
    (h : Splits (f.comp <| algebraMap R K) (minpoly R x)) :
    Splits f (minpoly K x) :=
  splits_of_splits_of_dvd _ ((minpoly.monic int).map _).ne_zero
    ((splits_map_iff _ _).mpr h) (minpoly.dvd_map_of_isScalarTower R _ x)
theorem IsIntegral.minpoly_splits_tower_top [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (int : IsIntegral R x) (h : Splits (algebraMap R L) (minpoly R x)) :
    Splits (algebraMap K L) (minpoly K x) := by
  rw [IsScalarTower.algebraMap_eq R K L] at h
  exact int.minpoly_splits_tower_top' h
lemma Subalgebra.adjoin_rank_le {F : Type*} (E : Type*) {K : Type*}
    [CommRing F] [StrongRankCondition F] [CommRing E] [StrongRankCondition E] [Ring K]
    [SMul F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (L : Subalgebra F K) [Module.Free F L] :
    Module.rank E (Algebra.adjoin E (L : Set K)) ≤ Module.rank F L := by
  rw [← rank_toSubmodule, Module.Free.rank_eq_card_chooseBasisIndex F L,
    L.adjoin_eq_span_basis E (Module.Free.chooseBasis F L)]
  exact rank_span_le _ |>.trans Cardinal.mk_range_le