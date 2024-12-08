import Mathlib.Algebra.Algebra.Quasispectrum
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Topology.UniformSpace.CompactConvergence
local notation "σₙ" => quasispectrum
open Topology
open scoped ContinuousMapZero
class NonUnitalContinuousFunctionalCalculus (R : Type*) {A : Type*} (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : ∀ a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    IsClosedEmbedding φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)
scoped[NonUnitalContinuousFunctionalCalculus]
attribute [instance] NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum
class UniqueNonUnitalContinuousFunctionalCalculus (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Zero s] (h0 : (0 : s) = (0 : R))
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (⟨.restrict s <| .id R, h0⟩) = ψ (⟨.restrict s <| .id R, h0⟩)) :
    φ = ψ
  compactSpace_quasispectrum (a : A) : CompactSpace (σₙ R a)
section Main
variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [instCFCₙ : NonUnitalContinuousFunctionalCalculus R p]
include instCFCₙ in
lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) :
    IsCompact (σₙ R a) :=
  isCompact_iff_compactSpace.mpr inferInstance
lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (a : A) (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = ψ ⟨.restrict (σₙ R a) <| .id R, rfl⟩) :
    φ = ψ :=
  have := UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := R) a
  UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id _ (by simp) φ ψ hφ hψ h
section cfcₙHom
variable {a : A} (ha : p a)
noncomputable def cfcₙHom : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose
lemma cfcₙHom_isClosedEmbedding :
    IsClosedEmbedding <| (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1
@[deprecated (since := "2024-10-20")]
alias cfcₙHom_closedEmbedding := cfcₙHom_isClosedEmbedding
@[fun_prop]
lemma cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  cfcₙHom_isClosedEmbedding ha |>.continuous
lemma cfcₙHom_id :
    cfcₙHom ha ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1
lemma cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀) :
    σₙ R (cfcₙHom ha f) = Set.range f :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1 f
lemma cfcₙHom_predicate (f : C(σₙ R a, R)₀) :
    p (cfcₙHom ha f) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2 f
lemma cfcₙHom_eq_of_continuous_of_map_id [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = a) : cfcₙHom ha = φ :=
  (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_isClosedEmbedding ha).continuous hφ₁ <| by
    rw [cfcₙHom_id ha, hφ₂]
theorem cfcₙHom_comp [UniqueNonUnitalContinuousFunctionalCalculus R A] (f : C(σₙ R a, R)₀)
    (f' : C(σₙ R a, σₙ R (cfcₙHom ha f))₀)
    (hff' : ∀ x, f x = f' x) (g : C(σₙ R (cfcₙHom ha f), R)₀) :
    cfcₙHom ha (g.comp f') = cfcₙHom (cfcₙHom_predicate ha f) g := by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_star' := fun _ ↦ rfl }
  let φ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] A := (cfcₙHom ha).comp ψ
  suffices cfcₙHom (cfcₙHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcₙHom_eq_of_continuous_of_map_id (cfcₙHom_predicate ha f) φ ?_ ?_
  · refine (cfcₙHom_isClosedEmbedding ha).continuous.comp <| continuous_induced_rng.mpr ?_
    exact f'.toContinuousMap.continuous_precomp.comp continuous_induced_dom
  · simp only [φ, ψ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_mk',
      NonUnitalAlgHom.coe_mk]
    congr
    ext x
    simp [hff']
end cfcₙHom
section cfcₙL
@[simps apply]
noncomputable def cfcₙL {a : A} (ha : p a) : C(σₙ R a, R)₀ →L[R] A :=
  { cfcₙHom ha with
    toFun := cfcₙHom ha
    map_smul' := map_smul _
    cont := (cfcₙHom_isClosedEmbedding ha).continuous }
end cfcₙL
section CFCn
open Classical in
noncomputable irreducible_def cfcₙ (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.restrict⟩, h.2.2⟩
    else 0
variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
variable (ha : p a := by cfc_tac)
lemma cfcₙ_apply : cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.restrict⟩, hf0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, hf0⟩]
lemma cfcₙ_apply_pi {ι : Type*} (f : ι → R → R) (a : A) (ha := by cfc_tac)
    (hf : ∀ i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i, f i 0 = 0 := by cfc_zero_tac) :
    (fun i => cfcₙ (f i) a) = (fun i => cfcₙHom (a := a) ha ⟨⟨_, (hf i).restrict⟩, hf0 i⟩) := by
  ext i
  simp only [cfcₙ_apply (f i) a (hf i) (hf0 i)]
lemma cfcₙ_apply_of_not_and_and {f : R → R} (a : A)
    (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg ha]
lemma cfcₙ_apply_of_not_predicate {f : R → R} (a : A) (ha : ¬ p a) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_left _ ha)]
lemma cfcₙ_apply_of_not_continuousOn {f : R → R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]
lemma cfcₙ_apply_of_not_map_zero {f : R → R} (a : A) (hf : ¬ f 0 = 0) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]
lemma cfcₙHom_eq_cfcₙ_extend {a : A} (g : R → R) (ha : p a) (f : C(σₙ R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f g) a := by
  have h : f = (σₙ R a).restrict (Function.extend Subtype.val f g) := by
    ext; simp [Subtype.val_injective.extend_apply]
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
    continuousOn_iff_continuous_restrict.mpr <| h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← quasispectrum.coe_zero (R := R) a, Subtype.val_injective.extend_apply]
    exact map_zero f
  rw [cfcₙ_apply ..]
  congr!
lemma cfcₙ_cases (P : A → Prop) (a : A) (f : R → R) (h₀ : P 0)
    (haf : ∀ (hf : ContinuousOn f (σₙ R a)) h0 ha, P (cfcₙHom ha ⟨⟨_, hf.restrict⟩, h0⟩)) :
    P (cfcₙ f a) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_of_not_predicate _ h]
lemma cfcₙ_commute_cfcₙ (f g : R → R) (a : A) : Commute (cfcₙ f a) (cfcₙ g a) := by
  refine cfcₙ_cases (fun x ↦ Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha ↦ ?_
  refine cfcₙ_cases (fun x ↦ Commute _ x) a g (by simp) fun hg hg0 _ ↦ ?_
  exact Commute.all _ _ |>.map _
variable (R) in
include ha in
lemma cfcₙ_id : cfcₙ (id : R → R) a = a :=
  cfcₙ_apply (id : R → R) a ▸ cfcₙHom_id (p := p) ha
variable (R) in
include ha in
lemma cfcₙ_id' : cfcₙ (fun x : R ↦ x) a = a := cfcₙ_id R a
include ha hf hf0 in
lemma cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' σₙ R a := by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]
variable (R) in
include R in
lemma cfcₙ_predicate_zero : p 0 :=
  NonUnitalContinuousFunctionalCalculus.predicate_zero (R := R)
lemma cfcₙ_predicate (f : R → R) (a : A) : p (cfcₙ f a) :=
  cfcₙ_cases p a f (cfcₙ_predicate_zero R) fun _ _ _ ↦ cfcₙHom_predicate ..
lemma cfcₙ_congr {f g : R → R} {a : A} (hfg : (σₙ R a).EqOn f g) :
    cfcₙ f a = cfcₙ g a := by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply f a (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2) h.1,
      cfcₙ_apply g a h.2.1 h.2.2 h.1]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf ↦ h0 (hfg (quasispectrum.zero_mem R a) ▸ hf)
lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R → R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a] at h
  have := (cfcₙHom_isClosedEmbedding (show p a from ha) (R := R)).injective h
  intro x hx
  congrm($(this) ⟨x, hx⟩)
lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R → R} {a : A} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfcₙ g a ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩
variable (R)
@[simp]
lemma cfcₙ_zero : cfcₙ (0 : R → R) a = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R → R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]
@[simp]
lemma cfcₙ_const_zero : cfcₙ (fun _ : R ↦ 0) a = 0 := cfcₙ_zero R a
variable {R}
include hf hf0 hg hg0 in
lemma cfcₙ_mul : cfcₙ (fun x ↦ f x * g x) a = cfcₙ f a * cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
include hf hf0 hg hg0 in
lemma cfcₙ_add : cfcₙ (fun x ↦ f x + g x) a = cfcₙ f a + cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
open Finset in
lemma cfcₙ_sum {ι : Type*} (f : ι → R → R) (a : A) (s : Finset ι)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i ∈ s, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i in s, f i) a = ∑ i in s, cfcₙ (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i ∈ s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (σₙ R a) := by
      rw [sum_coe_sort s, hsum]
      exact continuousOn_finset_sum s fun i hi => hf i hi
    rw [← sum_coe_sort s, ← sum_coe_sort s]
    rw [cfcₙ_apply_pi _ a _ (fun ⟨i, hi⟩ => hf i hi), ← map_sum, cfcₙ_apply _ a hf']
    congr 1
    ext
    simp
  · simp [cfcₙ_apply_of_not_predicate a ha]
open Finset in
lemma cfcₙ_sum_univ {ι : Type*} [Fintype ι] (f : ι → R → R) (a : A)
    (hf : ∀ i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i, f i) a = ∑ i, cfcₙ (f i) a :=
  cfcₙ_sum f a _ (fun i _ ↦ hf i) (fun i _ ↦ hf0 i)
lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ s • f x) a = s • cfcₙ f a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
lemma cfcₙ_const_mul (r : R) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ r * f x) a = r • cfcₙ f a :=
  cfcₙ_smul r f a
lemma cfcₙ_star : cfcₙ (fun x ↦ star (f x)) a = star (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_star, cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, star_zero]
      exact fun hf0 ↦ h0 <| by simpa using congr(star $(hf0))
lemma cfcₙ_smul_id {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfcₙ (s • · : R → R) a = s • a := by
  rw [cfcₙ_smul s _ a, cfcₙ_id' R a]
lemma cfcₙ_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfcₙ (r * ·) a = r • a :=
  cfcₙ_smul_id r a
include ha in
lemma cfcₙ_star_id : cfcₙ (star · : R → R) a = star a := by
  rw [cfcₙ_star _ a, cfcₙ_id' R a]
section Comp
variable [UniqueNonUnitalContinuousFunctionalCalculus R A]
lemma cfcₙ_comp (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g ∘ f) a = cfcₙ g (cfcₙ f a) := by
  have := hg.comp hf <| (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.restrict, hf0⟩) = f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply .., cfcₙ_apply f a,
    cfcₙ_apply _ _ (by convert hg) (ha := cfcₙHom_predicate (show p a from ha) _),
    ← cfcₙHom_comp _ _]
  swap
  · exact ⟨.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp, Subtype.ext hf0⟩
  · congr
  · exact fun _ ↦ rfl
lemma cfcₙ_comp' (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g <| f ·) a = cfcₙ g (cfcₙ f a) :=
  cfcₙ_comp g f a
lemma cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f ((s • ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| s • ·) a = cfcₙ f (s • a) := by
  rw [cfcₙ_comp' f (s • ·) a, cfcₙ_smul_id s a]
lemma cfcₙ_comp_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| r * ·) a = cfcₙ f (r • a) := by
  rw [cfcₙ_comp' f (r * ·) a, cfcₙ_const_mul_id r a]
lemma cfcₙ_comp_star (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| star ·) a = cfcₙ f (star a) := by
  rw [cfcₙ_comp' f star a, cfcₙ_star_id a]
end Comp
lemma CFC.eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R ↦ 0) fun x ↦ by simp_all
include instCFCₙ in
lemma CFC.quasispectrum_zero_eq : σₙ R (0 : A) = {0} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨quasispectrum.zero_mem R 0, fun x hx ↦ ?_⟩
  rw [← cfcₙ_zero R (0 : A),
    cfcₙ_map_quasispectrum _ _ (by cfc_cont_tac) (by cfc_zero_tac) (cfcₙ_predicate_zero R)] at hx
  simp_all
@[simp] lemma cfcₙ_apply_zero {f : R → R} : cfcₙ f (0 : A) = 0 := by
  by_cases hf0 : f 0 = 0
  · nth_rw 2 [← cfcₙ_zero R 0]
    apply cfcₙ_congr
    simpa [CFC.quasispectrum_zero_eq]
  · exact cfcₙ_apply_of_not_map_zero _ hf0
@[simp]
instance IsStarNormal.cfcₙ_map (f : R → R) (a : A) : IsStarNormal (cfcₙ f a) where
  star_comm_self := by
    refine cfcₙ_cases (fun x ↦ Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ ↦ ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a, ← cfcₙ_star, ← cfcₙ_mul .., ← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _
@[simp]
protected lemma IsSelfAdjoint.cfcₙ
    [NonUnitalContinuousFunctionalCalculus R (IsSelfAdjoint : A → Prop)] {f : R → R} {a : A} :
    IsSelfAdjoint (cfcₙ f a) :=
  cfcₙ_predicate _ _
@[simp]
lemma cfcₙ_nonneg_of_predicate [PartialOrder A]
    [NonUnitalContinuousFunctionalCalculus R (fun (a : A) => 0 ≤ a)] {f : R → R} {a : A} :
    0 ≤ cfcₙ f a :=
  cfcₙ_predicate _ _
end CFCn
end Main
section Neg
variable {R A : Type*} {p : A → Prop} [CommRing R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [NonUnitalRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]
variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
include hf hf0 hg hg0 in
lemma cfcₙ_sub : cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
lemma cfcₙ_neg : cfcₙ (fun x ↦ - (f x)) a = - (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_neg, cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, neg_zero]
      exact (h0 <| neg_eq_zero.mp ·)
lemma cfcₙ_neg_id (ha : p a := by cfc_tac) :
    cfcₙ (- · : R → R) a = -a := by
  rw [cfcₙ_neg .., cfcₙ_id' R a]
variable [UniqueNonUnitalContinuousFunctionalCalculus R A]
lemma cfcₙ_comp_neg (hf : ContinuousOn f ((- ·) '' (σₙ R a)) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| - ·) a = cfcₙ f (-a) := by
  rw [cfcₙ_comp' .., cfcₙ_neg_id _]
end Neg
section Order
section Semiring
variable {R A : Type*} {p : A → Prop} [OrderedCommSemiring R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [∀ (α) [Zero α] [TopologicalSpace α], StarOrderedRing C(α, R)₀]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]
lemma cfcₙHom_mono {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f ≤ g) :
    cfcₙHom ha f ≤ cfcₙHom ha g :=
  OrderHomClass.mono (cfcₙHom ha) hfg
lemma cfcₙHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(σₙ R a, R)₀} :
    0 ≤ cfcₙHom ha f ↔ 0 ≤ f := by
  constructor
  · exact fun hf x ↦
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)
lemma cfcₙ_mono {f g : R → R} {a : A} (h : ∀ x ∈ σₙ R a, f x ≤ g x)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ≤ cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x ↦ h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]
lemma cfcₙ_nonneg_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    0 ≤ cfcₙ f a ↔ ∀ x ∈ σₙ R a, 0 ≤ f x := by
  rw [cfcₙ_apply .., cfcₙHom_nonneg_iff, ContinuousMapZero.le_def]
  simp only [ContinuousMapZero.coe_mk, ContinuousMap.coe_mk, Set.restrict_apply, Subtype.forall]
  congr!
lemma StarOrderedRing.nonneg_iff_quasispectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 ≤ a ↔ ∀ x ∈ quasispectrum R a, 0 ≤ x := by
  have := cfcₙ_nonneg_iff (id : R → R) a (by fun_prop)
  simpa [cfcₙ_id _ a ha] using this
lemma cfcₙ_nonneg {f : R → R} {a : A} (h : ∀ x ∈ σₙ R a, 0 ≤ f x) :
    0 ≤ cfcₙ f a := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]
lemma cfcₙ_nonpos (f : R → R) (a : A) (h : ∀ x ∈ σₙ R a, f x ≤ 0) :
    cfcₙ f a ≤ 0 := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]
end Semiring
section Ring
variable {R A : Type*} {p : A → Prop} [OrderedCommRing R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [TopologicalRing R] [ContinuousStar R]
variable [∀ (α) [Zero α] [TopologicalSpace α], StarOrderedRing C(α, R)₀]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p] [NonnegSpectrumClass R A]
lemma cfcₙHom_le_iff {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} :
    cfcₙHom ha f ≤ cfcₙHom ha g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, cfcₙHom_nonneg_iff, sub_nonneg]
lemma cfcₙ_le_iff (f g : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg0 : g 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ cfcₙ g a ↔ ∀ x ∈ σₙ R a, f x ≤ g x := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙHom_le_iff (show p a from ha), ContinuousMapZero.le_def]
  simp
lemma cfcₙ_nonpos_iff (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ 0 ↔ ∀ x ∈ σₙ R a, f x ≤ 0 := by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x ↦ -f x) a
end Ring
end Order
section Superset
open ContinuousMapZero
variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFCₙ : NonUnitalContinuousFunctionalCalculus R p]
@[simps!]
noncomputable def cfcₙHomSuperset {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ →⋆ₙₐ[R] A :=
  letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
  cfcₙHom ha (R := R) |>.comp <| ContinuousMapZero.nonUnitalStarAlgHom_precomp R <|
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩
lemma cfcₙHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    Continuous (cfcₙHomSuperset ha hs) :=
  letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
  (cfcₙHom_continuous ha).comp <| ContinuousMapZero.continuous_comp_left _
lemma cfcₙHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs ⟨.restrict s <| .id R, rfl⟩ = a :=
  cfcₙHom_id ha
lemma cfcₙHomSuperset_id' {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs (.id rfl) = a :=
  cfcₙHom_id ha
end Superset
section UnitalToNonUnital
open ContinuousMapZero Set Uniformity ContinuousMap
variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]
variable (R) in
noncomputable def cfcₙHom_of_cfcHom {a : A} (ha : p a) : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  let e := ContinuousMapZero.toContinuousMapHom (X := σₙ R a) (R := R)
  let f : C(spectrum R a, quasispectrum R a) :=
    ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
  let ψ := ContinuousMap.compStarAlgHom' R R f
  (cfcHom ha (R := R) : C(spectrum R a, R) →⋆ₙₐ[R] A).comp <|
    (ψ : C(σₙ R a, R) →⋆ₙₐ[R] C(spectrum R a, R)).comp e
lemma cfcₙHom_of_cfcHom_map_quasispectrum {a : A} (ha : p a) :
    ∀ f : C(σₙ R a, R)₀, σₙ R (cfcₙHom_of_cfcHom R ha f) = range f := by
  intro f
  simp only [cfcₙHom_of_cfcHom]
  rw [quasispectrum_eq_spectrum_union_zero]
  simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
    NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum ha]
  ext x
  constructor
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩, rfl⟩
    · exact ⟨0, map_zero f⟩
  · rintro ⟨x, rfl⟩
    have hx := x.2
    simp_rw [quasispectrum_eq_spectrum_union_zero R a] at hx
    obtain (hx | hx) := hx
    · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
    · apply Or.inr
      simp only [Set.mem_singleton_iff] at hx ⊢
      rw [show x = 0 from Subtype.val_injective hx, map_zero]
variable [CompleteSpace R]
open scoped ContinuousFunctionalCalculus
lemma isClosedEmbedding_cfcₙHom_of_cfcHom {a : A} (ha : p a) :
    IsClosedEmbedding (cfcₙHom_of_cfcHom R ha) := by
  let f : C(spectrum R a, σₙ R a) :=
    ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
  refine (cfcHom_isClosedEmbedding ha).comp <|
    (IsUniformInducing.isUniformEmbedding ⟨?_⟩).isClosedEmbedding
  have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
    (map_continuous f).isProperMap (map_continuous 0).isProperMap <| by
      simp only [← Subtype.val_injective.image_injective.eq_iff, f, ContinuousMap.coe_mk,
        ContinuousMap.coe_zero, range_zero, image_union, image_singleton,
        quasispectrum.coe_zero, ← range_comp, val_comp_inclusion, image_univ, Subtype.range_coe,
        quasispectrum_eq_spectrum_union_zero]
  simp_rw [ContinuousMapZero.instUniformSpace, this, uniformity_comap,
    @inf_uniformity _ (.comap _ _) (.comap _ _), uniformity_comap, Filter.comap_inf,
    Filter.comap_comap]
  refine .symm <| inf_eq_left.mpr <| le_top.trans <| eq_top_iff.mp ?_
  have : ∀ U ∈ 𝓤 (C(Unit, R)), (0, 0) ∈ U := fun U hU ↦ refl_mem_uniformity hU
  convert Filter.comap_const_of_mem this with ⟨u, v⟩ <;>
  ext ⟨x, rfl⟩ <;> [exact map_zero u; exact map_zero v]
@[deprecated (since := "2024-10-20")]
alias closedEmbedding_cfcₙHom_of_cfcHom := isClosedEmbedding_cfcₙHom_of_cfcHom
instance ContinuousFunctionalCalculus.toNonUnital : NonUnitalContinuousFunctionalCalculus R p where
  predicate_zero := cfc_predicate_zero R
  compactSpace_quasispectrum a := by
    have h_cpct : CompactSpace (spectrum R a) := inferInstance
    simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
    exact h_cpct |>.union isCompact_singleton
  exists_cfc_of_predicate _ ha :=
    ⟨cfcₙHom_of_cfcHom R ha,
      isClosedEmbedding_cfcₙHom_of_cfcHom ha,
      cfcHom_id ha,
      cfcₙHom_of_cfcHom_map_quasispectrum ha,
      fun _ ↦ cfcHom_predicate ha _⟩
open scoped NonUnitalContinuousFunctionalCalculus in
lemma cfcₙHom_eq_cfcₙHom_of_cfcHom [UniqueNonUnitalContinuousFunctionalCalculus R A] {a : A}
    (ha : p a) : cfcₙHom (R := R) ha = cfcₙHom_of_cfcHom R ha := by
  refine UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id
      (σₙ R a) ?_ _ _ ?_ ?_ ?_
  · simp
  · exact (cfcₙHom_isClosedEmbedding (R := R) ha).continuous
  · exact (isClosedEmbedding_cfcₙHom_of_cfcHom ha).continuous
  · simpa only [cfcₙHom_id (R := R) ha] using (cfcHom_id ha).symm
lemma cfcₙ_eq_cfc [UniqueNonUnitalContinuousFunctionalCalculus R A] {f : R → R} {a : A}
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f a := by
  by_cases ha : p a
  · have hf' := hf.mono <| spectrum_subset_quasispectrum R a
    rw [cfc_apply f a ha hf', cfcₙ_apply f a hf, cfcₙHom_eq_cfcₙHom_of_cfcHom, cfcₙHom_of_cfcHom]
    dsimp only [NonUnitalStarAlgHom.comp_apply, toContinuousMapHom_apply,
      NonUnitalStarAlgHom.coe_coe, compStarAlgHom'_apply]
    congr
  · simp [cfc_apply_of_not_predicate a ha, cfcₙ_apply_of_not_predicate (R := R) a ha]
end UnitalToNonUnital