import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.SetTheory.Cardinal.Basic
noncomputable section
universe w w' u u' v v'
variable {R : Type u} {R' : Type u'} {M M₁ : Type v} {M' : Type v'}
open Cardinal Submodule Function Set
section Module
section
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (R M)
@[stacks 09G3 "first part"]
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndependent R ((↑) : s → M) }, (#ι.1)
theorem rank_le_card : Module.rank R M ≤ #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)
lemma nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndependent R ((↑) : s → M)} :=
  ⟨⟨∅, linearIndependent_empty _ _⟩⟩
end
namespace LinearIndependent
variable [Ring R] [AddCommGroup M] [Module R M]
variable [Nontrivial R]
theorem cardinal_lift_le_rank {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup (bddAbove_range _) ⟨_, hv.coe_range⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩
lemma aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : ℵ₀ ≤ Module.rank R M :=
  aleph0_le_lift.mp <| (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank
theorem cardinal_le_rank {ι : Type v} {v : ι → M}
    (hv : LinearIndependent R v) : #ι ≤ Module.rank R M := by
  simpa using hv.cardinal_lift_le_rank
theorem cardinal_le_rank' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) : #s ≤ Module.rank R M :=
  hs.cardinal_le_rank
end LinearIndependent
section SurjectiveInjective
section Module
variable [Ring R] [AddCommGroup M] [Module R M] [Ring R']
section
variable [AddCommGroup M'] [Module R' M']
theorem lift_rank_le_of_injective_injective (i : R' → R) (j : M →+ M')
    (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup (bddAbove_range _)]
  exact ciSup_mono' (bddAbove_range _) fun ⟨s, h⟩ ↦ ⟨⟨j '' s,
    (h.map_of_injective_injective i j hi (fun _ _ ↦ hj <| by rwa [j.map_zero]) hc).image⟩,
      lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩
theorem lift_rank_le_of_surjective_injective (i : ZeroHom R R') (j : M →+ M')
    (hi : Surjective i) (hj : Injective j) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injective i' j (fun _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', i.map_zero] at h
  rw [hc (i' r) m, hi']
theorem lift_rank_eq_of_equiv_equiv (i : ZeroHom R R') (j : M ≃+ M')
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) = lift.{v} (Module.rank R' M') :=
  (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm <|
    lift_rank_le_of_injective_injective i j.symm (fun _ _ ↦ hi.1 <| by rwa [i.map_zero])
      j.symm.injective fun _ _ ↦ j.symm_apply_eq.2 <| by erw [hc, j.apply_symm_apply]
end
section
variable [AddCommGroup M₁] [Module R' M₁]
theorem rank_le_of_injective_injective (i : R' → R) (j : M →+ M₁)
    (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc
theorem rank_le_of_surjective_injective (i : ZeroHom R R') (j : M →+ M₁)
    (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc
theorem rank_eq_of_equiv_equiv (i : ZeroHom R R') (j : M ≃+ M₁)
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M = Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc
end
end Module
namespace Algebra
variable {R : Type w} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
  {R' : Type w'} {S' : Type v'} [CommRing R'] [Ring S'] [Algebra R' S']
theorem lift_rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_injective_injective i j
    (fun _ _ ↦ hi <| by rwa [i.map_zero]) hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]
theorem lift_rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, ZeroHom.coe_coe, this]
theorem lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) = lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, ZeroHom.coe_coe, this]
variable {S' : Type v} [Ring S'] [Algebra R' S']
theorem rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc
theorem rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc
theorem rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    Module.rank R S = Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc
end Algebra
end SurjectiveInjective
variable [Ring R] [AddCommGroup M] [Module R M]
  [Ring R']
  [AddCommGroup M'] [AddCommGroup M₁]
  [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]
section
theorem LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') :=
  lift_rank_le_of_injective_injective (RingHom.id R) f (fun _ h ↦ h) i f.map_smul
theorem LinearMap.rank_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) :
    Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)
theorem lift_rank_range_le (f : M →ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup (Cardinal.bddAbove_range _)]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup (Cardinal.bddAbove_range _) ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestrict
    convert li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge
theorem rank_range_le (f : M →ₗ[R] M₁) : Module.rank R (LinearMap.range f) ≤ Module.rank R M := by
  simpa using lift_rank_range_le f
theorem lift_rank_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h
theorem rank_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) ≤ Module.rank R p := by simpa using lift_rank_map_le f p
lemma Submodule.rank_mono {s t : Submodule R M} (h : s ≤ t) : Module.rank R s ≤ Module.rank R t :=
  (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
    Subtype.eq <| show x = y from Subtype.ext_iff_val.1 eq
@[deprecated (since := "2024-09-30")] alias rank_le_of_submodule := Submodule.rank_mono
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq
theorem lift_rank_range_of_injective (f : M →ₗ[R] M') (h : Injective f) :
    lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M) :=
  (LinearEquiv.ofInjective f h).lift_rank_eq.symm
theorem rank_range_of_injective (f : M →ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm
theorem LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) :
    lift.{v} (Module.rank R (p.map (f : M →ₗ[R] M'))) = lift.{v'} (Module.rank R p) :=
  (f.submoduleMap p).lift_rank_eq.symm
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm
variable (R M)
@[simp]
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M :=
  (LinearEquiv.ofTop ⊤ rfl).rank_eq
variable {R M}
theorem rank_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h, rank_top]
theorem Submodule.rank_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← rank_top R M]
  exact rank_mono le_top
@[deprecated (since := "2024-10-02")] alias rank_submodule_le := Submodule.rank_le
theorem LinearMap.lift_rank_le_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    lift.{v} (Module.rank R M') ≤ lift.{v'} (Module.rank R M) := by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le
theorem LinearMap.rank_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ ≤ Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le
@[nontriviality, simp]
theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1 := by
  haveI := Module.subsingleton R M
  have : Nonempty { s : Set M // LinearIndependent R ((↑) : s → M) } :=
    ⟨⟨∅, linearIndependent_empty _ _⟩⟩
  rw [Module.rank_def, ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · rintro ⟨s, hs⟩
    rw [Cardinal.mk_le_one_iff_set_subsingleton]
    apply subsingleton_of_subsingleton
  intro w hw
  refine ⟨⟨{0}, ?_⟩, ?_⟩
  · rw [linearIndependent_iff']
    subsingleton
  · exact hw.trans_eq (Cardinal.mk_singleton _).symm
lemma rank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (L L' : Submodule R M) {s : S} (hr : IsSMulRegular M s)
    (h : ∀ x ∈ L, s • x ∈ L') :
    Module.rank R L ≤ Module.rank R L' :=
  ((Algebra.lsmul S R M s).restrict h).rank_le_of_injective <|
    fun _ _ h ↦ by simpa using hr (Subtype.ext_iff.mp h)
@[deprecated (since := "2024-11-21")]
alias rank_le_of_smul_regular := rank_le_of_isSMulRegular
end
end Module