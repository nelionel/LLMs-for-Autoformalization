import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.Topology.ShrinkingLemma
universe uι uE uH uM uF
open Function Filter Module Set
open scoped Topology Manifold
local notation "∞" => (⊤ : ℕ∞)
noncomputable section
variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]
variable (ι M)
structure SmoothBumpCovering [FiniteDimensional ℝ E] (s : Set M := univ) where
  c : ι → M
  toFun : ∀ i, SmoothBumpFunction I (c i)
  c_mem' : ∀ i, c i ∈ s
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1
structure SmoothPartitionOfUnity (s : Set M := univ) where
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  nonneg' : ∀ i x, 0 ≤ toFun i x
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1
variable {ι I M}
namespace SmoothPartitionOfUnity
variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}
instance {s : Set M} : FunLike (SmoothPartitionOfUnity ι I M s) ι C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'
theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x
theorem sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx
theorem exists_pos_of_mem {x} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  by_contra! h
  have H : ∀ i, f i x = 0 := fun i ↦ le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa
theorem sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x
@[simps]
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }
theorem contMDiff_sum : ContMDiff I 𝓘(ℝ) ⊤ fun x => ∑ᶠ i, f i x :=
  contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite
@[deprecated (since := "2024-11-21")] alias smooth_sum := contMDiff_sum
theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.toPartitionOfUnity.le_one i x
theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x
theorem finsum_smul_mem_convex {g : ι → M → F} {t : Set F} {x : M} (hx : x ∈ s)
    (hg : ∀ i, f i x ≠ 0 → g i x ∈ t) (ht : Convex ℝ t) : ∑ᶠ i, f i x • g i x ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg
theorem contMDiff_smul {g : M → F} {i} (hg : ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n g x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => f i x • g x :=
  contMDiff_of_tsupport fun x hx =>
    ((f i).contMDiff.contMDiffAt.of_le le_top).smul <| hg x <| tsupport_smul_subset_left _ _ hx
@[deprecated (since := "2024-11-21")] alias smooth_smul := contMDiff_smul
theorem contMDiff_finsum_smul {g : ι → M → F}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n (g i) x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  (contMDiff_finsum fun i => f.contMDiff_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _
@[deprecated (since := "2024-11-21")] alias smooth_finsum_smul := contMDiff_finsum_smul
theorem contMDiffAt_finsum {x₀ : M} {g : ι → M → F}
    (hφ : ∀ i, x₀ ∈ tsupport (f i) → ContMDiffAt I 𝓘(ℝ, F) n (g i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i ↦ ?_
  by_cases hx : x₀ ∈ tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le le_top).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_not_mem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f i) (g i)) hx) n
theorem contDiffAt_finsum {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {x₀ : E}
    {g : ι → E → F} (hφ : ∀ i, x₀ ∈ tsupport (f i) → ContDiffAt ℝ n (g i) x₀) :
    ContDiffAt ℝ n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ
section finsupport
variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)
def finsupport : Finset ι := ρ.toPartitionOfUnity.finsupport x₀
@[simp]
theorem mem_finsupport {i : ι} : i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.mem_finsupport x₀
@[simp]
theorem coe_finsupport : (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.coe_finsupport x₀
theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport hx₀
theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI
theorem sum_finsupport_smul_eq_finsum {A : Type*} [AddCommGroup A] [Module ℝ A] (φ : ι → M → A) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ
end finsupport
section fintsupport 
variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)
theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite :=
  ρ.toPartitionOfUnity.finite_tsupport _
def fintsupport (x : M) : Finset ι :=
  (ρ.finite_tsupport x).toFinset
theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _
theorem eventually_fintsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_fintsupport_subset _
theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀
theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_finsupport_subset x₀
end fintsupport
section IsSubordinate
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, tsupport (f i) ⊆ U i
variable {f}
variable {U : ι → Set M}
@[simp]
theorem isSubordinate_toPartitionOfUnity :
    f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl
alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity
theorem IsSubordinate.contMDiff_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (hg : ∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) :
    ContMDiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt <| (ho i).mem_nhds (hf i hx)
@[deprecated (since := "2024-11-21")]
alias IsSubordinate.smooth_finsum_smul := IsSubordinate.contMDiff_finsum_smul
end IsSubordinate
end SmoothPartitionOfUnity
namespace BumpCovering
theorem contMDiff_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCovering ι M s)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) ⊤ (f i)) (i : ι) : ContMDiff I 𝓘(ℝ) ⊤ (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) <| by
    simp only [Pi.sub_def, mulSupport_one_sub]
    exact f.locallyFinite
@[deprecated (since := "2024-11-21")]
alias smooth_toPartitionOfUnity := contMDiff_toPartitionOfUnity
variable {s : Set M}
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ⊤ (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }
@[simp]
theorem toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) ⊤ (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl
@[simp]
theorem coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ⊤ (f i))
    (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl
theorem IsSubordinate.toSmoothPartitionOfUnity {f : BumpCovering ι M s} {U : ι → Set M}
    (h : f.IsSubordinate U) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ⊤ (f i)) :
    (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity
end BumpCovering
namespace SmoothBumpCovering
variable [FiniteDimensional ℝ E]
variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s)
instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, tsupport (f i) ⊆ U (f.c i)
theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : fs.IsSubordinate U) (i : ι) : support (fs i) ⊆ U (fs.c i) :=
  Subset.trans subset_closure (h i)
variable (I) in
theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ (ι : Type uM) (f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_support (I := I) (hU x hx)
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs hB with
    ⟨ι, c, f, hf, hsub', hfin⟩
  choose hcs hfU using hf
  rcases exists_subset_iUnion_closed_subset hs (fun i => (f i).isOpen_support)
    (fun x _ => hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩
  choose r hrR hr using fun i => (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)
  refine ⟨ι, ⟨c, fun i => (f i).updateRIn (r i) (hrR i), hcs, ?_, fun x hx => ?_⟩, fun i => ?_⟩
  · simpa only [SmoothBumpFunction.support_updateRIn]
  · refine (mem_iUnion.1 <| hsV hx).imp fun i hi => ?_
    exact ((f i).updateRIn _ _).eventuallyEq_one_of_dist_lt
      ((f i).support_subset_source <| hVf _ hi) (hr i hi).2
  · simpa only [SmoothBumpFunction.support_updateRIn, tsupport] using hfU i
protected theorem locallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locallyFinite'
protected theorem point_finite (x : M) : {i | fs i x ≠ 0}.Finite :=
  fs.locallyFinite.point_finite x
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventuallyEq_one' x hx).choose
theorem eventuallyEq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventuallyEq_one' x hx).choose_spec
theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventuallyEq_one x hx).eq_of_nhds
theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]
theorem mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (chartAt H (fs.c i)).source :=
  (fs i).support_subset_source <| by simp [h]
theorem mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (extChartAt I (fs.c i)).source := by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h
theorem mem_chartAt_ind_source (x : M) (hx : x ∈ s) : x ∈ (chartAt H (fs.c (fs.ind x hx))).source :=
  fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)
theorem mem_extChartAt_ind_source (x : M) (hx : x ∈ s) :
    x ∈ (extChartAt I (fs.c (fs.ind x hx))).source :=
  fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support
variable [T2Space M]
variable [SmoothManifoldWithCorners I M]
def toBumpCovering : BumpCovering ι M s where
  toFun i := ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'
@[simp, nolint simpNF]
theorem isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl
alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff
theorem toSmoothPartitionOfUnity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x) :=
  rfl
open Classical in
theorem toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
    fs.toSmoothPartitionOfUnity i x =
      fs i x * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - fs j x) :=
  fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht
open Classical in
theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) :
    ∃ t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x]
        fs i * ∏ j ∈ t.filter fun j => WellOrderingRel j i, ((1 : M → ℝ) - fs j) := by
  simpa using fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x
theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h
theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) ⊆ support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i
theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity
theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x
end SmoothBumpCovering
variable (I)
variable [FiniteDimensional ℝ E]
variable [SmoothManifoldWithCorners I M]
theorem exists_smooth_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc 0 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum⟩, fun x hx => ?_, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  refine fun i => f.toSmoothPartitionOfUnity_zero_of_zero ?_
  exact nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)
theorem exists_smooth_zero_one_nhds_of_isClosed [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_smooth_zero_one_of_isClosed I isClosed_closure isClosed_closure
    (subset_compl_iff_disjoint_left.mp hvu)
  refine ⟨f, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv
theorem exists_smooth_one_nhds_of_subset_interior [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  rcases exists_smooth_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'
namespace SmoothPartitionOfUnity
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
        ContinuousMap.coe_zero]
instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩
variable [T2Space M] [SigmaCompactSpace M]
theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have := BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(ℝ) ⊤) ?_ hs U ho hU
  · rcases this with ⟨f, hf, hfU⟩
    exact ⟨f.toSmoothPartitionOfUnity hf, hfU.toSmoothPartitionOfUnity hf⟩
  · intro s t hs ht hd
    rcases exists_smooth_zero_one_of_isClosed I hs ht hd with ⟨f, hf⟩
    exact ⟨f, f.contMDiff, hf⟩
theorem exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed s) :
    ∃ f : SmoothPartitionOfUnity s I M s,
      f.IsSubordinate (fun x ↦ (chartAt H (x : M)).source) := by
  apply exists_isSubordinate _ hs _ (fun i ↦ (chartAt H _).open_source) (fun x hx ↦ ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)
variable (M)
theorem exists_isSubordinate_chartAt_source :
    ∃ f : SmoothPartitionOfUnity M I M univ, f.IsSubordinate (fun x ↦ (chartAt H x).source) := by
  apply exists_isSubordinate _ isClosed_univ _ (fun i ↦ (chartAt H _).open_source) (fun x _ ↦ ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)
end SmoothPartitionOfUnity
variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : ℕ∞}
theorem exists_contMDiffOn_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, ContMDiffOn I 𝓘(ℝ, F) n g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x := by
  choose U hU g hgs hgt using Hloc
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ (fun x => interior (U x))
      (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
      hf.contMDiff_finsum_smul (fun i => isOpen_interior) fun i => (hgs i).mono interior_subset⟩,
    fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ ?_) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)
theorem exists_smooth_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, ContMDiffOn I 𝓘(ℝ, F) ⊤ g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_contMDiffOn_forall_mem_convex_of_local I ht Hloc
theorem exists_smooth_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_smooth_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩
theorem Emetric.exists_smooth_forall_closedBall_subset {M} [EMetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, EMetric.closedBall x (ENNReal.ofReal (δ x)) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_swap ι M]
    using exists_smooth_forall_mem_convex_of_local_const I
      EMetric.exists_forall_closedBall_subset_aux₂
      (EMetric.exists_forall_closedBall_subset_aux₁ hK hU hKU hfin)
theorem Metric.exists_smooth_forall_closedBall_subset {M} [MetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, Metric.closedBall x (δ x) ⊆ U i := by
  rcases Emetric.exists_smooth_forall_closedBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.emetric_closedBall (hδ0 _).le]
  exact hδ i x hx
lemma IsOpen.exists_msmooth_support_eq_aux {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, f.support = s ∧ ContMDiff I 𝓘(ℝ) ⊤ f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_smooth_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
  · exact f_diff.comp_contMDiff contMDiff_model
  · exact Subset.trans (range_comp_subset_range _ _) f_range
theorem IsOpen.exists_msmooth_support_eq {s : Set M} (hs : IsOpen s) :
    ∃ f : M → ℝ, f.support = s ∧ ContMDiff I 𝓘(ℝ) ⊤ f ∧ ∀ x, 0 ≤ f x := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : ∀ (c : M), ∃ g : H → ℝ,
      g.support = (chartAt H c).target ∩ (chartAt H c).symm ⁻¹' s ∧
      ContMDiff I 𝓘(ℝ) ⊤ g ∧ Set.range g ⊆ Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_msmooth_support_eq_aux
    exact PartialHomeomorph.isOpen_inter_preimage_symm _ hs
  choose g g_supp g_diff hg using A
  have h'g : ∀ c x, 0 ≤ g c x := fun c x ↦ (hg c (mem_range_self (f := g c) x)).1
  have h''g : ∀ c x, 0 ≤ f c x * g c (chartAt H c x) :=
    fun c x ↦ mul_nonneg (f.nonneg c x) (h'g c _)
  refine ⟨fun x ↦ ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · apply ne_of_gt
      have B : ∃ c, 0 < f c x * g c (chartAt H c x) := by
        obtain ⟨c, hc⟩ : ∃ c, 0 < f c x := f.exists_pos_of_mem (mem_univ x)
        refine ⟨c, mul_pos hc ?_⟩
        apply lt_of_le_of_ne (h'g _ _) (Ne.symm _)
        rw [← mem_support, g_supp, ← mem_preimage, preimage_inter]
        have Hx : x ∈ tsupport (f c) := subset_tsupport _ (ne_of_gt hc)
        simp [(chartAt H c).left_inv (hf c Hx), hx, (chartAt H c).map_source (hf c Hx)]
      apply finsum_pos' (fun c ↦ h''g c x) B
      apply (f.locallyFinite.point_finite x).subset
      apply compl_subset_compl.2
      rintro c (hc : f c x = 0)
      simpa only [mul_eq_zero] using Or.inl hc
    · apply finsum_eq_zero_of_forall_eq_zero
      intro c
      by_cases Hx : x ∈ tsupport (f c)
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        rw [← nmem_support, g_supp, ← mem_preimage, preimage_inter]
        contrapose! hx
        simp only [mem_inter_iff, mem_preimage, (chartAt H c).left_inv (hf c Hx)] at hx
        exact hx.2
      · have : x ∉ support (f c) := by contrapose! Hx; exact subset_tsupport _ Hx
        rw [nmem_support] at this
        simp [this]
  · apply SmoothPartitionOfUnity.contMDiff_finsum_smul
    intro c x hx
    apply (g_diff c (chartAt H c x)).comp
    exact contMDiffAt_of_mem_maximalAtlas (SmoothManifoldWithCorners.chart_mem_maximalAtlas _)
      (hf c hx)
  · intro x
    apply finsum_nonneg (fun c ↦ h''g c x)
theorem exists_msmooth_support_eq_eq_one_iff
    {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ⊤ f ∧ range f ⊆ Icc 0 1 ∧ support f = s
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  rcases hs.exists_msmooth_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_msmooth_support_eq I with ⟨g, g_supp, g_diff, g_pos⟩
  have A : ∀ x, 0 < f x + g x := by
    intro x
    by_cases xs : x ∈ support f
    · have : 0 < f x := lt_of_le_of_ne (f_pos x) (Ne.symm xs)
      linarith [g_pos x]
    · have : 0 < g x := by
        classical
        apply lt_of_le_of_ne (g_pos x) (Ne.symm ?_)
        rw [← mem_support, g_supp]
        contrapose! xs
        simp? at xs says simp only [mem_compl_iff, Decidable.not_not] at xs
        exact h.trans f_supp.symm.subset xs
      linarith [f_pos x]
  refine ⟨fun x ↦ f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  · exact f_diff.div₀ (f_diff.add g_diff) (fun x ↦ ne_of_gt (A x))
  · refine range_subset_iff.2 (fun x ↦ ⟨div_nonneg (f_pos x) (A x).le, ?_⟩)
    apply div_le_one_of_le₀ _ (A x).le
    simpa only [le_add_iff_nonneg_right] using g_pos x
  · have B : support (fun x ↦ f x + g x) = univ := eq_univ_of_forall (fun x ↦ (A x).ne')
    simp only [support_div, f_supp, B, inter_univ]
  · intro x
    simp [div_eq_one_iff_eq (A x).ne', self_eq_add_right, ← nmem_support, g_supp]
theorem exists_msmooth_zero_iff_one_iff_of_isClosed {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ⊤ f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ s ↔ f x = 0)
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  rcases exists_msmooth_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← nmem_support, fs]