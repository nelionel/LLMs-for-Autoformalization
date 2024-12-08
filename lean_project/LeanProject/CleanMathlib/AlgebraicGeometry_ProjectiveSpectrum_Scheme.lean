import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.GradedAlgebra.Radical
noncomputable section
namespace AlgebraicGeometry
open scoped DirectSum Pointwise
open DirectSum SetLike.GradedMonoid Localization
open Finset hiding mk_zero
variable {R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A)
variable [GradedAlgebra 𝒜]
open TopCat TopologicalSpace
open CategoryTheory Opposite
open ProjectiveSpectrum.StructureSheaf
set_option hygiene false
local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜
local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜
macro "Proj| " U:term : term =>
  `((Proj.toLocallyRingedSpace 𝒜).restrict
    (Opens.isOpenEmbedding (X := Proj.T) ($U : Opens Proj.T)))
local notation "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace
    <| (LocallyRingedSpace.restrict Proj (Opens.isOpenEmbedding (X := Proj.T) (U : Opens Proj.T)))
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x
local notation "sbo " f => PrimeSpectrum.basicOpen f
local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)
local notation "Spec.T " ring =>
  (Spec.locallyRingedSpaceObj (CommRingCat.of ring)).toSheafedSpace.toPresheafedSpace.1
local notation3 "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f
namespace ProjIsoSpecTopComponent
namespace ToSpec
open Ideal
variable {𝒜}
variable {f : A} {m : ℕ} (x : Proj| (pbo f))
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))
@[simp]
theorem mk_mem_carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ carrier x ↔ z.num.1 ∈ x.1.asHomogeneousIdeal := by
  rw [carrier, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one,
    mul_comm, Ideal.unit_mul_mem_iff_mem, ← Ideal.mem_comap,
    IsLocalization.comap_map_of_isPrime_disjoint (.powers f)]
  · rfl
  · infer_instance
  · exact (disjoint_powers_iff_not_mem _ (Ideal.IsPrime.isRadical inferInstance)).mpr x.2
  · exact isUnit_of_invertible _
theorem isPrime_carrier : Ideal.IsPrime (carrier x) := by
  refine Ideal.IsPrime.comap _ (hK := ?_)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) _ _ inferInstance
    ((disjoint_powers_iff_not_mem _ (Ideal.IsPrime.isRadical inferInstance)).mpr x.2)
variable (f)
@[simps (config := .lemmasOnly)]
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, isPrime_carrier x⟩
theorem preimage_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toFun f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  Set.ext fun y ↦ (mk_mem_carrier y z).not
end ToSpec
section
@[simps! (config := .lemmasOnly) apply_asIdeal]
def toSpec (f : A) : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f where
  toFun := ToSpec.toFun f
  continuous_toFun := by
    rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
    rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
    rw [ToSpec.preimage_basicOpen]
    exact (pbo x.num).2.preimage continuous_subtype_val
variable {𝒜} in
lemma toSpec_preimage_basicOpen {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toSpec 𝒜 f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  ToSpec.preimage_basicOpen f z
end
namespace FromSpec
open GradedAlgebra SetLike
open Finset hiding mk_zero
open HomogeneousLocalization
variable {𝒜}
variable {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)
open Lean Meta Elab Tactic
macro "mem_tac_aux" : tactic =>
  `(tactic| first | exact pow_mem_graded _ (Submodule.coe_mem _) | exact natCast_mem_graded _ _ |
    exact pow_mem_graded _ f_deg)
macro "mem_tac" : tactic =>
  `(tactic| first | mem_tac_aux |
    repeat (all_goals (apply SetLike.GradedMonoid.toGradedMul.mul_mem)); mem_tac_aux)
def carrier (f_deg : f ∈ 𝒜 m) (q : Spec.T A⁰_ f) : Set A :=
  {a | ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1}
theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔ ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by
      rw [← smul_eq_mul]; mem_tac⟩,
      ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1 :=
  Iff.rfl
theorem mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔
      ∀ i, (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) ∈
          algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' { s | s ∈ q.1 } :=
  (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x ∈ q.asIdeal at h
        convert h
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
        dsimp only [Subtype.coe_mk]; rw [← hx]; rfl)
theorem mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 n) :
    a ∈ carrier f_deg q ↔
      (HomogeneousLocalization.mk ⟨m * n, ⟨a ^ m, pow_mem_graded m hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal
  · refine ⟨fun h ↦ h n, fun h i ↦ if hi : i = n then hi ▸ h else ?_⟩
    convert zero_mem q.asIdeal
    apply HomogeneousLocalization.val_injective
    simp only [proj_apply, decompose_of_mem_ne _ hn (Ne.symm hi), zero_pow hm.ne',
      HomogeneousLocalization.val_mk, Localization.mk_zero, HomogeneousLocalization.val_zero]
  · simp only [proj_apply, decompose_of_mem_same _ hn]
theorem mem_carrier_iff_of_mem_mul (hm : 0 < m)
    (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 (n * m)) :
    a ∈ carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, ⟨a, mul_comm n m ▸ hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn, iff_iff_eq, eq_comm,
    ← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization.mk_pow, pow_mul]
  rfl
theorem num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    z.num.1 ∈ carrier f_deg q ↔ HomogeneousLocalization.mk z ∈ q.asIdeal := by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n ≠ 0 := fun e ↦ by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_ using 2
  · apply HomogeneousLocalization.val_injective; simp only [hn, HomogeneousLocalization.val_mk]
  · have := degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded n f_deg) (hn.symm ▸ z.den.2) this
    rw [← smul_eq_mul, this]; exact z.num.2
theorem carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a ∈ carrier f_deg q)
    (hb : b ∈ carrier f_deg q) : a + b ∈ carrier f_deg q := by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (.mk ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : ℕ → A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 : A⁰_ f)
      else
        if h1 : j ≤ m then
          letI l : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i b ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          l * r
        else
          letI l : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) * proj 𝒜 i b ^ (m + m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          l * r
  rotate_left
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem (i := j • i) (j := (m - j) • i) <;> mem_tac_aux
    rw [← add_smul, Nat.add_sub_of_le h1]; rfl
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem (i := (j-m) • i) (j := (m + m - j) • i) <;> mem_tac_aux
    rw [← add_smul]; congr; zify [le_of_not_lt h2, le_of_not_le h1]; abel
  convert_to ∑ i ∈ range (m + m + 1), g i ∈ q.1; swap
  · refine q.1.sum_mem fun j _ => nsmul_mem ?_ _; split_ifs
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
  change _ = (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) _
  dsimp only [Subtype.coe_mk]; rw [map_sum, mk_sum]
  apply Finset.sum_congr rfl fun j hj => _
  intro j hj
  change _ = HomogeneousLocalization.val _
  rw [HomogeneousLocalization.val_smul]
  split_ifs with h2 h1
  · exact ((Finset.mem_range.1 hj).not_le h2).elim
  all_goals simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero,
    HomogeneousLocalization.val_mk, Subtype.coe_mk, Localization.mk_mul, ← smul_mk]; congr 2
  · dsimp; rw [mul_assoc, ← pow_add, add_comm (m - j), Nat.add_sub_assoc h1]
  · simp_rw [pow_add]; rfl
  · dsimp; rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_not_le h1)]
  · simp_rw [pow_add]; rfl
variable (hm : 0 < m) (q : Spec.T A⁰_ f)
include hm
theorem carrier.zero_mem : (0 : A) ∈ carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1 using 1
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  convert Localization.mk_zero (S := Submonoid.powers f) _ using 1
theorem carrier.smul_mem (c x : A) (hx : x ∈ carrier f_deg q) : c • x ∈ carrier f_deg q := by
  revert c
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    let product : A⁰_ f :=
      Mul.mul (HomogeneousLocalization.mk ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, ?_⟩, ⟨n, rfl⟩⟩)
        (HomogeneousLocalization.mk ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, ?_⟩, ⟨i - n, rfl⟩⟩)
    · split_ifs with h
      · convert_to product ∈ q.1
        · dsimp [product]
          erw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mk]
          · simp_rw [mul_pow]; rw [Localization.mk_mul]
            · congr; rw [← pow_add, Nat.add_sub_of_le h]
        · apply Ideal.mul_mem_left (α := A⁰_ f) _ _ (hx _)
          rw [(_ : m • n = _)]
          · mem_tac
          · simp only [smul_eq_mul, mul_comm]
      · simpa only [map_zero, zero_pow hm.ne'] using zero_mem f_deg hm q i
    rw [(_ : m • (i - n) = _)]
    · mem_tac
    · simp only [smul_eq_mul, mul_comm]
  · simp_rw [add_smul]; exact fun _ _ => carrier.add_mem f_deg q
def carrier.asIdeal : Ideal A where
  carrier := carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q
theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 :=
  fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (Submodule.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j
def carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩
theorem carrier.denom_not_mem : f ∉ carrier.asIdeal f_deg hm q := fun rid =>
  q.isPrime.ne_top <|
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_one,
          HomogeneousLocalization.val_mk]
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp only [mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self])
theorem carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ carrier.asHomogeneousIdeal f_deg hm q :=
  fun rid => carrier.denom_not_mem f_deg hm q <| rid <| DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'
theorem carrier.asIdeal.ne_top : carrier.asIdeal f_deg hm q ≠ ⊤ := fun rid =>
  carrier.denom_not_mem f_deg hm q (rid.symm ▸ Submodule.mem_top)
theorem carrier.asIdeal.prime : (carrier.asIdeal f_deg hm q).IsPrime :=
  (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (∀ _, _ ∈ _) ∨ ∀ _, _ ∈ _ by
      rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left]
      · apply q.2.mem_or_mem; convert hxy (nx + ny) using 1
        dsimp
        simp_rw [decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (SetLike.GradedMonoid.toGradedMul.mul_mem hnx hny),
          mul_pow, pow_add]
        simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_mul, Localization.mk_mul]
        simp only [Submonoid.mk_mul_mk, mk_eq_monoidOf_mk']
      all_goals
        intro n hn; convert q.1.zero_mem using 1
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_zero]; simp_rw [proj_apply]
        convert mk_zero (S := Submonoid.powers f) _
        rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm.ne']
        · first | exact hnx | exact hny
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp <| carrier.denom_not_mem f_deg hm q⟩
end FromSpec
section toSpecFromSpec
lemma toSpec_fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f)) :
    toSpec 𝒜 f (FromSpec.toFun f_deg hm x) = x := by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z
@[deprecated (since := "2024-03-02")] alias toSpecFromSpec := toSpec_fromSpec
end toSpecFromSpec
section fromSpecToSpec
lemma fromSpec_toSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f) :
    FromSpec.toFun f_deg hm (toSpec 𝒜 f x) = x := by
  refine Subtype.ext <| ProjectiveSpectrum.ext <| HomogeneousIdeal.ext' ?_
  intros i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)
lemma toSpec_injective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Injective (toSpec 𝒜 f) := by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this
lemma toSpec_surjective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Surjective (toSpec 𝒜 f) :=
  Function.surjective_iff_hasRightInverse |>.mpr
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩
lemma toSpec_bijective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Bijective (toSpec (𝒜 := 𝒜) (f := f)) :=
  ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩
end fromSpecToSpec
namespace toSpec
variable {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
include hm f_deg
variable {𝒜} in
lemma image_basicOpen_eq_basicOpen (a : A) (i : ℕ) :
    toSpec 𝒜 f '' (Subtype.val ⁻¹' (pbo (decompose 𝒜 a i) : Set (ProjectiveSpectrum 𝒜))) =
    (PrimeSpectrum.basicOpen (R := A⁰_ f) <|
      HomogeneousLocalization.mk
        ⟨m * i, ⟨decompose 𝒜 a i ^ m,
          (smul_eq_mul ℕ) ▸ SetLike.pow_mem_graded _ (Submodule.coe_mem _)⟩,
          ⟨f^i, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg⟩, ⟨i, rfl⟩⟩).1 :=
  Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm) <|
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe, toSpec_preimage_basicOpen, ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]
end toSpec
variable {𝒜} in
def fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) where
  toFun := FromSpec.toFun f_deg hm
  continuous_toFun := by
    rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜) (pbo f).1
      |>.continuous_iff]
    rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
    have h₁ : Subtype.val (p := (pbo f).1) ⁻¹' (pbo a) =
        ⋃ i : ℕ, Subtype.val (p := (pbo f).1) ⁻¹' (pbo (decompose 𝒜 a i)) := by
      simp [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a]
    let e : _ ≃ _ :=
      ⟨FromSpec.toFun f_deg hm, ToSpec.toFun f, toSpec_fromSpec _ _ _, fromSpec_toSpec _ _ _⟩
    change IsOpen <| e ⁻¹' _
    rw [Set.preimage_equiv_eq_image_symm, h₁, Set.image_iUnion]
    exact isOpen_iUnion fun i ↦ toSpec.image_basicOpen_eq_basicOpen f_deg hm a i ▸
      PrimeSpectrum.isOpen_basicOpen
end ProjIsoSpecTopComponent
variable {𝒜} in
def projIsoSpecTopComponent {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f))  where
  hom := ProjIsoSpecTopComponent.toSpec 𝒜 f
  inv := ProjIsoSpecTopComponent.fromSpec f_deg hm
  hom_inv_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.fromSpec_toSpec 𝒜 f_deg hm)
  inv_hom_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.toSpec_fromSpec 𝒜 f_deg hm)
namespace ProjectiveSpectrum.Proj
def awayToSection (f) : CommRingCat.of (A⁰_ f) ⟶ (structureSheaf 𝒜).1.obj (op (pbo f)) where
  toFun s :=
    ⟨fun x ↦ HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) s, fun x ↦ by
      obtain ⟨s, rfl⟩ := HomogeneousLocalization.mk_surjective s
      obtain ⟨n, hn : f ^ n = s.den.1⟩ := s.den_mem
      exact ⟨_, x.2, 𝟙 _, s.1, s.2, s.3,
        fun x hsx ↦ x.2 (Ideal.IsPrime.mem_of_pow_mem inferInstance n (hn ▸ hsx)), fun _ ↦ rfl⟩⟩
  map_add' _ _ := by ext; simp only [map_add, HomogeneousLocalization.val_add, Proj.add_apply]
  map_mul' _ _ := by ext; simp only [map_mul, HomogeneousLocalization.val_mul, Proj.mul_apply]
  map_zero' := by ext; simp only [map_zero, HomogeneousLocalization.val_zero, Proj.zero_apply]
  map_one' := by ext; simp only [map_one, HomogeneousLocalization.val_one, Proj.one_apply]
lemma awayToSection_germ (f x hx) :
    awayToSection 𝒜 f ≫ (structureSheaf 𝒜).presheaf.germ _ x hx =
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx)) ≫
        (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv := by
  ext z
  apply (Proj.stalkIso' 𝒜 x).eq_symm_apply.mpr
  apply Proj.stalkIso'_germ
lemma awayToSection_apply (f : A) (x p) :
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).1 x).val p).val =
      IsLocalization.map (M := Submonoid.powers f) (T := p.1.1.toIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr p.2) x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  show (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl
def awayToΓ (f) : CommRingCat.of (A⁰_ f) ⟶ LocallyRingedSpace.Γ.obj (op <| Proj| pbo f) :=
  awayToSection 𝒜 f ≫ (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map
    (homOfLE (Opens.isOpenEmbedding_obj_top _).le).op
lemma awayToΓ_ΓToStalk (f) (x) :
    awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x =
      HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) ≫
      (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv := by
  rw [awayToΓ, Category.assoc, ← Category.assoc _ (Iso.inv _),
    Iso.eq_comp_inv, Category.assoc, Category.assoc, Presheaf.Γgerm]
  rw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ]
  simp only [Proj.toLocallyRingedSpace, Proj.toSheafedSpace]
  rw [Presheaf.germ_res, awayToSection_germ]
  rfl
def toSpec (f) : (Proj| pbo f) ⟶ Spec (A⁰_ f) :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv (Proj| pbo f) (op (CommRingCat.of <| A⁰_ f))
    (awayToΓ 𝒜 f).op
open HomogeneousLocalization IsLocalRing
lemma toSpec_base_apply_eq_comap {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = PrimeSpectrum.comap (mapId 𝒜 (Submonoid.powers_le.mpr x.2))
      (closedPoint (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)) := by
  show PrimeSpectrum.comap (awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x)
        (IsLocalRing.closedPoint ((Proj| pbo f).presheaf.stalk x)) = _
  rw [awayToΓ_ΓToStalk, CommRingCat.comp_eq_ring_hom_comp, PrimeSpectrum.comap_comp]
  exact congr(PrimeSpectrum.comap _ $(@IsLocalRing.comap_closedPoint
    (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _ _
    ((Proj| pbo f).presheaf.stalk x) _ _ _ (isLocalHom_of_isIso _)))
lemma toSpec_base_apply_eq {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = ProjIsoSpecTopComponent.toSpec 𝒜 f x :=
  toSpec_base_apply_eq_comap 𝒜 x |>.trans <| PrimeSpectrum.ext <| Ideal.ext fun z =>
  show ¬ IsUnit _ ↔ z ∈ ProjIsoSpecTopComponent.ToSpec.carrier _ by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val,
    ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.AtPrime.isUnit_mk'_iff]
  exact not_not
lemma toSpec_base_isIso {f} {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsIso (toSpec 𝒜 f).base := by
  convert (projIsoSpecTopComponent f_deg hm).isIso_hom
  exact DFunLike.ext _ _ <| toSpec_base_apply_eq 𝒜
lemma mk_mem_toSpec_base_apply {f} (x : Proj| pbo f)
    (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((toSpec 𝒜 f).base x).asIdeal ↔
      z.num.1 ∈ x.1.asHomogeneousIdeal :=
  (toSpec_base_apply_eq 𝒜 x).symm ▸ ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _
lemma toSpec_preimage_basicOpen {f}
    (t : NumDenSameDeg 𝒜 (.powers f)) :
    (Opens.map (toSpec 𝒜 f).base).obj (sbo (.mk t)) =
      Opens.comap ⟨_, continuous_subtype_val⟩ (pbo t.num.1) :=
  Opens.ext <| Opens.map_coe _ _ ▸ by
  convert (ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen f t)
  exact funext fun _ => toSpec_base_apply_eq _ _
@[reassoc]
lemma toOpen_toSpec_val_c_app (f) (U) :
    StructureSheaf.toOpen (A⁰_ f) U.unop ≫ (toSpec 𝒜 f).c.app U =
      awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.map (homOfLE le_top).op :=
  Eq.trans (by congr) <| ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app _ U
@[reassoc]
lemma toStalk_stalkMap_toSpec (f) (x) :
    StructureSheaf.toStalk _ _ ≫ (toSpec 𝒜 f).stalkMap x =
      awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x := by
  rw [StructureSheaf.toStalk, Category.assoc]
  simp_rw [CommRingCat.coe_of, ← Spec.locallyRingedSpaceObj_presheaf']
  rw [LocallyRingedSpace.stalkMap_germ (toSpec 𝒜 f),
    toOpen_toSpec_val_c_app_assoc, Presheaf.germ_res]
  rfl
lemma isLocalization_atPrime (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    @IsLocalization (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.primeCompl
      (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _
      (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra := by
  letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := y.mk_surjective
    refine isUnit_of_mul_eq_one _
      (.mk ⟨y.deg, y.den, y.num, (mk_mem_toSpec_base_apply _ _ _).not.mp hy⟩) <| val_injective _ ?_
    simp only [RingHom.algebraMap_toAlgebra, map_mk, RingHom.id_apply, val_mul, val_mk, mk_eq_mk',
      val_one, IsLocalization.mk'_mul_mk'_eq_one']
  · intro z
    obtain ⟨⟨i, a, ⟨b, hb⟩, (hb' : b ∉ x.1.1)⟩, rfl⟩ := z.mk_surjective
    refine ⟨⟨.mk ⟨i * m, ⟨a * b ^ (m - 1), ?_⟩, ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
      ⟨.mk ⟨i * m, ⟨b ^ m, mul_comm m i ▸ SetLike.pow_mem_graded _ hb⟩,
        ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
        (mk_mem_toSpec_base_apply _ _ _).not.mpr <| x.1.1.toIdeal.primeCompl.pow_mem hb' m⟩⟩,
        val_injective _ ?_⟩
    · convert SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded (m - 1) hb) using 2
      rw [← succ_nsmul', tsub_add_cancel_of_le (by omega), mul_comm, smul_eq_mul]
    · simp only [RingHom.algebraMap_toAlgebra, map_mk, RingHom.id_apply, val_mul, val_mk,
        mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk, IsLocalization.mk'_eq_iff_eq]
      rw [mul_comm b, mul_mul_mul_comm, ← pow_succ', mul_assoc, tsub_add_cancel_of_le (by omega)]
  · intros y z e
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨z, rfl⟩ := z.mk_surjective
    obtain ⟨i, c, hc, hc', e⟩ : ∃ i, ∃ c ∈ 𝒜 i, c ∉ x.1.asHomogeneousIdeal ∧
        c * (z.den.1 * y.num.1) = c * (y.den.1 * z.num.1) := by
      apply_fun HomogeneousLocalization.val at e
      simp only [RingHom.algebraMap_toAlgebra, map_mk, RingHom.id_apply, val_mk, mk_eq_mk',
        IsLocalization.mk'_eq_iff_eq] at e
      obtain ⟨⟨c, hcx⟩, hc⟩ := IsLocalization.exists_of_eq (M := x.1.1.toIdeal.primeCompl) e
      obtain ⟨i, hi⟩ := not_forall.mp ((x.1.1.isHomogeneous.mem_iff _).not.mp hcx)
      refine ⟨i, _, (decompose 𝒜 c i).2, hi, ?_⟩
      apply_fun fun x ↦ (decompose 𝒜 x (i + z.deg + y.deg)).1 at hc
      conv_rhs at hc => rw [add_right_comm]
      rwa [← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        ← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        mul_assoc, mul_assoc] at hc
      exacts [y.den.2, z.num.2, z.den.2, y.num.2]
    refine ⟨⟨.mk ⟨m * i, ⟨c ^ m, SetLike.pow_mem_graded _ hc⟩,
      ⟨f ^ i, mul_comm m i ▸ SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
      (mk_mem_toSpec_base_apply _ _ _).not.mpr <| x.1.1.toIdeal.primeCompl.pow_mem hc' _⟩,
      val_injective _ ?_⟩
    simp only [val_mul, val_mk, mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk,
      IsLocalization.mk'_eq_iff_eq, mul_assoc]
    congr 2
    rw [mul_left_comm, mul_left_comm y.den.1, ← tsub_add_cancel_of_le (show 1 ≤ m from hm),
      pow_succ, mul_assoc, mul_assoc, e]
def specStalkEquiv (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x) ≅
      CommRingCat.of (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
  letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  haveI := isLocalization_atPrime 𝒜 f x f_deg hm
  (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x))
    (Q := AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)).toRingEquiv.toCommRingCatIso
lemma toStalk_specStalkEquiv (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    StructureSheaf.toStalk (A⁰_ f) ((toSpec 𝒜 f).base x) ≫ (specStalkEquiv 𝒜 f x f_deg hm).hom =
      (mapId _ <| Submonoid.powers_le.mpr x.2 : (A⁰_ f) →+* AtPrime 𝒜 x.1.1.toIdeal) :=
  letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  letI := isLocalization_atPrime 𝒜 f x f_deg hm
  (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x))
    (Q := AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)).toAlgHom.comp_algebraMap
lemma stalkMap_toSpec (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (toSpec 𝒜 f).stalkMap x =
      (specStalkEquiv 𝒜 f x f_deg hm).hom ≫ (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv :=
  IsLocalization.ringHom_ext (R := A⁰_ f) ((toSpec 𝒜 f).base x).asIdeal.primeCompl
    (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x)) <|
    (toStalk_stalkMap_toSpec _ _ _).trans <| by
    rw [awayToΓ_ΓToStalk, ← toStalk_specStalkEquiv, Category.assoc]; rfl
lemma isIso_toSpec (f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsIso (toSpec 𝒜 f) := by
  haveI : IsIso (toSpec 𝒜 f).base := toSpec_base_isIso 𝒜 f_deg hm
  haveI (x) : IsIso ((toSpec 𝒜 f).stalkMap x) := by
    rw [stalkMap_toSpec 𝒜 f x f_deg hm]; infer_instance
  haveI : LocallyRingedSpace.IsOpenImmersion (toSpec 𝒜 f) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (toSpec 𝒜 f)
      (TopCat.homeoOfIso (asIso <| (toSpec 𝒜 f).base)).isOpenEmbedding
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _
end ProjectiveSpectrum.Proj
open ProjectiveSpectrum.Proj in
def projIsoSpec (f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj| pbo f) ≅ (Spec (A⁰_ f)) :=
  @asIso _ _ _ _ (f := toSpec 𝒜 f) (isIso_toSpec 𝒜 f f_deg hm)
def «Proj» : Scheme where
  __ := Proj.toLocallyRingedSpace 𝒜
  local_affine (x : Proj.T) := by
    classical
    obtain ⟨f, m, f_deg, hm, hx⟩ : ∃ (f : A) (m : ℕ) (_ : f ∈ 𝒜 m) (_ : 0 < m), f ∉ x.1 := by
      by_contra!
      refine x.not_irrelevant_le fun z hz ↦ ?_
      rw [← DirectSum.sum_support_decompose 𝒜 z]
      exact x.1.toIdeal.sum_mem fun k hk ↦ this _ k (SetLike.coe_mem _) <| by_contra <| by aesop
    exact ⟨⟨pbo f, hx⟩, .of (A⁰_ f), ⟨projIsoSpec 𝒜 f f_deg hm⟩⟩
end AlgebraicGeometry