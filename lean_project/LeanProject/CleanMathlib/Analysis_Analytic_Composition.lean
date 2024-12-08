import Mathlib.Analysis.Analytic.Basic
import Mathlib.Combinatorics.Enumerative.Composition
noncomputable section
variable {𝕜 : Type*} {E F G H : Type*}
open Filter List
open scoped Topology NNReal ENNReal
section Topological
variable [CommRing 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
namespace FormalMultilinearSeries
variable [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
def applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
    (Fin n → E) → Fin c.length → F := fun v i => p (c.blocksFun i) (v ∘ c.embedding i)
theorem applyComposition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.applyComposition (Composition.ones n) = fun v i =>
      p 1 fun _ => v (Fin.castLE (Composition.length_le _) i) := by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by omega
  refine congr_arg v ?_
  rw [Fin.ext_iff, Fin.coe_castLE, Composition.ones_embedding, Fin.val_mk]
theorem applyComposition_single (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : 0 < n)
    (v : Fin n → E) : p.applyComposition (Composition.single n hn) v = fun _j => p n v := by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert Composition.single_embedding hn ⟨i, hi2⟩ using 1
  cases' j with j_val j_property
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  congr!
  simp
@[simp]
theorem removeZero_applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (c : Composition n) : p.removeZero.applyComposition c = p.applyComposition c := by
  ext v i
  simp [applyComposition, zero_lt_one.trans_le (c.one_le_blocksFun i), removeZero_of_pos]
theorem applyComposition_update (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n)
    (j : Fin n) (v : Fin n → E) (z : E) :
    p.applyComposition c (Function.update v j z) =
      Function.update (p.applyComposition c v) (c.index j)
        (p (c.blocksFun (c.index j))
          (Function.update (v ∘ c.embedding (c.index j)) (c.invEmbedding j) z)) := by
  ext k
  by_cases h : k = c.index j
  · rw [h]
    let r : Fin (c.blocksFun (c.index j)) → Fin n := c.embedding (c.index j)
    simp only [Function.update_same]
    change p (c.blocksFun (c.index j)) (Function.update v j z ∘ r) = _
    let j' := c.invEmbedding j
    suffices B : Function.update v j z ∘ r = Function.update (v ∘ r) j' z by rw [B]
    suffices C : Function.update v (r j') z ∘ r = Function.update (v ∘ r) j' z by
      convert C; exact (c.embedding_comp_inv j).symm
    exact Function.update_comp_eq_of_injective _ (c.embedding _).injective _ _
  · simp only [h, Function.update_eq_self, Function.update_noteq, Ne, not_false_iff]
    let r : Fin (c.blocksFun k) → Fin n := c.embedding k
    change p (c.blocksFun k) (Function.update v j z ∘ r) = p (c.blocksFun k) (v ∘ r)
    suffices B : Function.update v j z ∘ r = v ∘ r by rw [B]
    apply Function.update_comp_eq_of_not_mem_range
    rwa [c.mem_range_embedding_iff']
@[simp]
theorem compContinuousLinearMap_applyComposition {n : ℕ} (p : FormalMultilinearSeries 𝕜 F G)
    (f : E →L[𝕜] F) (c : Composition n) (v : Fin n → E) :
    (p.compContinuousLinearMap f).applyComposition c v = p.applyComposition c (f ∘ v) := by
  simp (config := {unfoldPartialApp := true}) [applyComposition]; rfl
end FormalMultilinearSeries
namespace ContinuousMultilinearMap
open FormalMultilinearSeries
variable [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
def compAlongComposition {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) : E [×n]→L[𝕜] G where
  toFun v := f (p.applyComposition c v)
  map_update_add' v i x y := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyComposition_update, ContinuousMultilinearMap.map_update_add]
  map_update_smul' v i c x := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyComposition_update, ContinuousMultilinearMap.map_update_smul]
  cont :=
    f.cont.comp <|
      continuous_pi fun _ => (coe_continuous _).comp <| continuous_pi fun _ => continuous_apply _
@[simp]
theorem compAlongComposition_apply {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) (v : Fin n → E) :
    (f.compAlongComposition p c) v = f (p.applyComposition c v) :=
  rfl
end ContinuousMultilinearMap
namespace FormalMultilinearSeries
variable [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
def compAlongComposition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) : (E [×n]→L[𝕜] G) :=
  (q c.length).compAlongComposition p c
@[simp]
theorem compAlongComposition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) (v : Fin n → E) :
    (q.compAlongComposition p c) v = q c.length (p.applyComposition c v) :=
  rfl
protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => ∑ c : Composition n, q.compAlongComposition p c
theorem comp_coeff_zero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 → E) (v' : Fin 0 → F) : (q.comp p) 0 v = q 0 v' := by
  let c : Composition 0 := Composition.ones 0
  dsimp [FormalMultilinearSeries.comp]
  have : {c} = (Finset.univ : Finset (Composition 0)) := by
    apply Finset.eq_of_subset_of_card_le <;> simp [Finset.card_univ, composition_card 0]
  rw [← this, Finset.sum_singleton, compAlongComposition_apply]
  symm; congr! 
@[simp]
theorem comp_coeff_zero' (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 0 → E) : (q.comp p) 0 v = q 0 fun _i => 0 :=
  q.comp_coeff_zero p v _
theorem comp_coeff_zero'' (q : FormalMultilinearSeries 𝕜 E F) (p : FormalMultilinearSeries 𝕜 E E) :
    (q.comp p) 0 = q 0 := by ext v; exact q.comp_coeff_zero p _ _
theorem comp_coeff_one (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (v : Fin 1 → E) : (q.comp p) 1 v = q 1 fun _i => p 1 v := by
  have : {Composition.ones 1} = (Finset.univ : Finset (Composition 1)) :=
    Finset.eq_univ_of_card _ (by simp [composition_card])
  simp only [FormalMultilinearSeries.comp, compAlongComposition_apply, ← this,
    Finset.sum_singleton]
  refine q.congr (by simp) fun i hi1 hi2 => ?_
  simp only [applyComposition_ones]
  exact p.congr rfl fun j _hj1 hj2 => by congr! 
theorem removeZero_comp_of_pos (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : 0 < n) :
    q.removeZero.comp p n = q.comp p n := by
  ext v
  simp only [FormalMultilinearSeries.comp, compAlongComposition,
    ContinuousMultilinearMap.compAlongComposition_apply, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _hc => ?_
  rw [removeZero_of_pos _ (c.length_pos_of_pos hn)]
@[simp]
theorem comp_removeZero (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    q.comp p.removeZero = q.comp p := by ext n; simp [FormalMultilinearSeries.comp]
end FormalMultilinearSeries
end Topological
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]
namespace FormalMultilinearSeries
theorem compAlongComposition_bound {n : ℕ} (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n)
    (f : F [×c.length]→L[𝕜] G) (v : Fin n → E) :
    ‖f.compAlongComposition p c v‖ ≤ (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ :=
  calc
    ‖f.compAlongComposition p c v‖ = ‖f (p.applyComposition c v)‖ := rfl
    _ ≤ ‖f‖ * ∏ i, ‖p.applyComposition c v i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖f‖ * ∏ i, ‖p (c.blocksFun i)‖ * ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine Finset.prod_le_prod (fun i _hi => norm_nonneg _) fun i _hi => ?_
      apply ContinuousMultilinearMap.le_opNorm
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) *
        ∏ i, ∏ j : Fin (c.blocksFun i), ‖(v ∘ c.embedding i) j‖ := by
      rw [Finset.prod_mul_distrib, mul_assoc]
    _ = (‖f‖ * ∏ i, ‖p (c.blocksFun i)‖) * ∏ i : Fin n, ‖v i‖ := by
      rw [← c.blocksFinEquiv.prod_comp, ← Finset.univ_sigma_univ, Finset.prod_sigma]
      congr
theorem compAlongComposition_norm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖ ≤ ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)
theorem compAlongComposition_nnnorm {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : Composition n) :
    ‖q.compAlongComposition p c‖₊ ≤ ‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊ := by
  rw [← NNReal.coe_le_coe]; push_cast; exact q.compAlongComposition_norm p c
section
variable (𝕜 E)
def id (x : E) : FormalMultilinearSeries 𝕜 E E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 E E).symm (ContinuousLinearMap.id 𝕜 E)
  | _ => 0
@[simp] theorem id_apply_zero (x : E) (v : Fin 0 → E) :
    (FormalMultilinearSeries.id 𝕜 E x) 0 v = x := rfl
@[simp]
theorem id_apply_one (x : E) (v : Fin 1 → E) : (FormalMultilinearSeries.id 𝕜 E x) 1 v = v 0 :=
  rfl
theorem id_apply_one' (x : E) {n : ℕ} (h : n = 1) (v : Fin n → E) :
    (id 𝕜 E x) n v = v ⟨0, h.symm ▸ zero_lt_one⟩ := by
  subst n
  apply id_apply_one
@[simp]
theorem id_apply_of_one_lt (x : E) {n : ℕ} (h : 1 < n) :
    (FormalMultilinearSeries.id 𝕜 E x) n = 0 := by
  cases' n with n
  · contradiction
  · cases n
    · contradiction
    · rfl
end
@[simp]
theorem comp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) : p.comp (id 𝕜 E x) = p := by
  ext1 n
  dsimp [FormalMultilinearSeries.comp]
  rw [Finset.sum_eq_single (Composition.ones n)]
  · show compAlongComposition p (id 𝕜 E x) (Composition.ones n) = p n
    ext v
    rw [compAlongComposition_apply]
    apply p.congr (Composition.ones_length n)
    intros
    rw [applyComposition_ones]
    refine congr_arg v ?_
    rw [Fin.ext_iff, Fin.coe_castLE, Fin.val_mk]
  · show
    ∀ b : Composition n,
      b ∈ Finset.univ → b ≠ Composition.ones n → compAlongComposition p (id 𝕜 E x) b = 0
    intro b _ hb
    obtain ⟨k, hk, lt_k⟩ : ∃ (k : ℕ), k ∈ Composition.blocks b ∧ 1 < k :=
      Composition.ne_ones_iff.1 hb
    obtain ⟨i, hi⟩ : ∃ (i : Fin b.blocks.length), b.blocks[i] = k :=
      List.get_of_mem hk
    let j : Fin b.length := ⟨i.val, b.blocks_length ▸ i.prop⟩
    have A : 1 < b.blocksFun j := by convert lt_k
    ext v
    rw [compAlongComposition_apply, ContinuousMultilinearMap.zero_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ j
    dsimp [applyComposition]
    rw [id_apply_of_one_lt _ _ _ A]
    rfl
  · simp
@[simp]
theorem id_comp (p : FormalMultilinearSeries 𝕜 E F) (v0 : Fin 0 → E) :
    (id 𝕜 F (p 0 v0)).comp p = p := by
  ext1 n
  by_cases hn : n = 0
  · rw [hn]
    ext v
    simp only [comp_coeff_zero', id_apply_zero]
    congr with i
    exact i.elim0
  · dsimp [FormalMultilinearSeries.comp]
    have n_pos : 0 < n := bot_lt_iff_ne_bot.mpr hn
    rw [Finset.sum_eq_single (Composition.single n n_pos)]
    · show compAlongComposition (id 𝕜 F (p 0 v0)) p (Composition.single n n_pos) = p n
      ext v
      rw [compAlongComposition_apply, id_apply_one' _ _ _ (Composition.single_length n_pos)]
      dsimp [applyComposition]
      refine p.congr rfl fun i him hin => congr_arg v <| ?_
      ext; simp
    · show
      ∀ b : Composition n, b ∈ Finset.univ → b ≠ Composition.single n n_pos →
        compAlongComposition (id 𝕜 F (p 0 v0)) p b = 0
      intro b _ hb
      have A : 1 < b.length := by
        have : b.length ≠ 1 := by simpa [Composition.eq_single_iff_length] using hb
        have : 0 < b.length := Composition.length_pos_of_pos b n_pos
        omega
      ext v
      rw [compAlongComposition_apply, id_apply_of_one_lt _ _ _ A]
      rfl
    · simp
theorem id_comp' (p : FormalMultilinearSeries 𝕜 E F) (x : F) (v0 : Fin 0 → E) (h : x = p 0 v0) :
    (id 𝕜 F x).comp p = p := by
  simp [h]
section
theorem comp_summable_nnreal (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (hq : 0 < q.radius) (hp : 0 < p.radius) :
    ∃ r > (0 : ℝ≥0),
      Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hq) with ⟨rq, rq_pos, hrq⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hp) with ⟨rp, rp_pos, hrp⟩
  simp only [lt_min_iff, ENNReal.coe_lt_one_iff, ENNReal.coe_pos] at hrp hrq rp_pos rq_pos
  obtain ⟨Cq, _hCq0, hCq⟩ : ∃ Cq > 0, ∀ n, ‖q n‖₊ * rq ^ n ≤ Cq :=
    q.nnnorm_mul_pow_le_of_lt_radius hrq.2
  obtain ⟨Cp, hCp1, hCp⟩ : ∃ Cp ≥ 1, ∀ n, ‖p n‖₊ * rp ^ n ≤ Cp := by
    rcases p.nnnorm_mul_pow_le_of_lt_radius hrp.2 with ⟨Cp, -, hCp⟩
    exact ⟨max Cp 1, le_max_right _ _, fun n => (hCp n).trans (le_max_left _ _)⟩
  let r0 : ℝ≥0 := (4 * Cp)⁻¹
  have r0_pos : 0 < r0 := inv_pos.2 (mul_pos zero_lt_four (zero_lt_one.trans_le hCp1))
  set r : ℝ≥0 := rp * rq * r0
  have r_pos : 0 < r := mul_pos (mul_pos rp_pos rq_pos) r0_pos
  have I :
    ∀ i : Σ n : ℕ, Composition n, ‖q.compAlongComposition p i.2‖₊ * r ^ i.1 ≤ Cq / 4 ^ i.1 := by
    rintro ⟨n, c⟩
    have A := calc
      ‖q c.length‖₊ * rq ^ n ≤ ‖q c.length‖₊ * rq ^ c.length :=
        mul_le_mul' le_rfl (pow_le_pow_of_le_one rq.2 hrq.1.le c.length_le)
      _ ≤ Cq := hCq _
    have B := calc
      (∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n = ∏ i, ‖p (c.blocksFun i)‖₊ * rp ^ c.blocksFun i := by
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]
      _ ≤ ∏ _i : Fin c.length, Cp := Finset.prod_le_prod' fun i _ => hCp _
      _ = Cp ^ c.length := by simp
      _ ≤ Cp ^ n := pow_right_mono₀ hCp1 c.length_le
    calc
      ‖q.compAlongComposition p c‖₊ * r ^ n ≤
          (‖q c.length‖₊ * ∏ i, ‖p (c.blocksFun i)‖₊) * r ^ n :=
        mul_le_mul' (q.compAlongComposition_nnnorm p c) le_rfl
      _ = ‖q c.length‖₊ * rq ^ n * ((∏ i, ‖p (c.blocksFun i)‖₊) * rp ^ n) * r0 ^ n := by
        ring
      _ ≤ Cq * Cp ^ n * r0 ^ n := mul_le_mul' (mul_le_mul' A B) le_rfl
      _ = Cq / 4 ^ n := by
        simp only [r0]
        field_simp [mul_pow, (zero_lt_one.trans_le hCp1).ne']
        ring
  refine ⟨r, r_pos, NNReal.summable_of_le I ?_⟩
  simp_rw [div_eq_mul_inv]
  refine Summable.mul_left _ ?_
  have : ∀ n : ℕ, HasSum (fun c : Composition n => (4 ^ n : ℝ≥0)⁻¹) (2 ^ (n - 1) / 4 ^ n) := by
    intro n
    convert hasSum_fintype fun c : Composition n => (4 ^ n : ℝ≥0)⁻¹
    simp [Finset.card_univ, composition_card, div_eq_mul_inv]
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, (NNReal.summable_nat_add_iff 1).1 ?_⟩
  convert (NNReal.summable_geometric (NNReal.div_lt_one_of_lt one_lt_two)).mul_left (1 / 4) using 1
  ext1 n
  rw [(this _).tsum_eq, add_tsub_cancel_right]
  field_simp [← mul_assoc, pow_succ, mul_pow, show (4 : ℝ≥0) = 2 * 2 by norm_num,
    mul_right_comm]
end
theorem le_comp_radius_of_summable (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (r : ℝ≥0)
    (hr : Summable fun i : Σ n, Composition n => ‖q.compAlongComposition p i.2‖₊ * r ^ i.1) :
    (r : ℝ≥0∞) ≤ (q.comp p).radius := by
  refine
    le_radius_of_bound_nnreal _
      (∑' i : Σ n, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst) fun n => ?_
  calc
    ‖FormalMultilinearSeries.comp q p n‖₊ * r ^ n ≤
        ∑' c : Composition n, ‖compAlongComposition q p c‖₊ * r ^ n := by
      rw [tsum_fintype, ← Finset.sum_mul]
      exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
    _ ≤ ∑' i : Σ n : ℕ, Composition n, ‖compAlongComposition q p i.snd‖₊ * r ^ i.fst :=
      NNReal.tsum_comp_le_tsum_of_inj hr sigma_mk_injective
def compPartialSumSource (m M N : ℕ) : Finset (Σ n, Fin n → ℕ) :=
  Finset.sigma (Finset.Ico m M) (fun n : ℕ => Fintype.piFinset fun _i : Fin n => Finset.Ico 1 N : _)
@[simp]
theorem mem_compPartialSumSource_iff (m M N : ℕ) (i : Σ n, Fin n → ℕ) :
    i ∈ compPartialSumSource m M N ↔
      (m ≤ i.1 ∧ i.1 < M) ∧ ∀ a : Fin i.1, 1 ≤ i.2 a ∧ i.2 a < N := by
  simp only [compPartialSumSource, Finset.mem_Ico, Fintype.mem_piFinset, Finset.mem_sigma]
def compChangeOfVariables (m M N : ℕ) (i : Σ n, Fin n → ℕ) (hi : i ∈ compPartialSumSource m M N) :
    Σ n, Composition n := by
  rcases i with ⟨n, f⟩
  rw [mem_compPartialSumSource_iff] at hi
  refine ⟨∑ j, f j, ofFn fun a => f a, fun hi' => ?_, by simp [sum_ofFn]⟩
  rename_i i
  obtain ⟨j, rfl⟩ : ∃ j : Fin n, f j = i := by rwa [mem_ofFn, Set.mem_range] at hi'
  exact (hi.2 j).1
@[simp]
theorem compChangeOfVariables_length (m M N : ℕ) {i : Σ n, Fin n → ℕ}
    (hi : i ∈ compPartialSumSource m M N) :
    Composition.length (compChangeOfVariables m M N i hi).2 = i.1 := by
  rcases i with ⟨k, blocks_fun⟩
  dsimp [compChangeOfVariables]
  simp only [Composition.length, map_ofFn, length_ofFn]
theorem compChangeOfVariables_blocksFun (m M N : ℕ) {i : Σ n, Fin n → ℕ}
    (hi : i ∈ compPartialSumSource m M N) (j : Fin i.1) :
    (compChangeOfVariables m M N i hi).2.blocksFun
        ⟨j, (compChangeOfVariables_length m M N hi).symm ▸ j.2⟩ =
      i.2 j := by
  rcases i with ⟨n, f⟩
  dsimp [Composition.blocksFun, Composition.blocks, compChangeOfVariables]
  simp only [map_ofFn, List.getElem_ofFn, Function.comp_apply]
def compPartialSumTargetSet (m M N : ℕ) : Set (Σ n, Composition n) :=
  {i | m ≤ i.2.length ∧ i.2.length < M ∧ ∀ j : Fin i.2.length, i.2.blocksFun j < N}
theorem compPartialSumTargetSet_image_compPartialSumSource (m M N : ℕ)
    (i : Σ n, Composition n) (hi : i ∈ compPartialSumTargetSet m M N) :
    ∃ (j : _) (hj : j ∈ compPartialSumSource m M N), compChangeOfVariables m M N j hj = i := by
  rcases i with ⟨n, c⟩
  refine ⟨⟨c.length, c.blocksFun⟩, ?_, ?_⟩
  · simp only [compPartialSumTargetSet, Set.mem_setOf_eq] at hi
    simp only [mem_compPartialSumSource_iff, hi.left, hi.right, true_and, and_true]
    exact fun a => c.one_le_blocks' _
  · dsimp [compChangeOfVariables]
    rw [Composition.sigma_eq_iff_blocks_eq]
    simp only [Composition.blocksFun, Composition.blocks, Subtype.coe_eta]
    conv_rhs => rw [← List.ofFn_get c.blocks]
def compPartialSumTarget (m M N : ℕ) : Finset (Σ n, Composition n) :=
  Set.Finite.toFinset <|
    ((Finset.finite_toSet _).dependent_image _).subset <|
      compPartialSumTargetSet_image_compPartialSumSource m M N
@[simp]
theorem mem_compPartialSumTarget_iff {m M N : ℕ} {a : Σ n, Composition n} :
    a ∈ compPartialSumTarget m M N ↔
      m ≤ a.2.length ∧ a.2.length < M ∧ ∀ j : Fin a.2.length, a.2.blocksFun j < N := by
  simp [compPartialSumTarget, compPartialSumTargetSet]
theorem compChangeOfVariables_sum {α : Type*} [AddCommMonoid α] (m M N : ℕ)
    (f : (Σ n : ℕ, Fin n → ℕ) → α) (g : (Σ n, Composition n) → α)
    (h : ∀ (e) (he : e ∈ compPartialSumSource m M N), f e = g (compChangeOfVariables m M N e he)) :
    ∑ e ∈ compPartialSumSource m M N, f e = ∑ e ∈ compPartialSumTarget m M N, g e := by
  apply Finset.sum_bij (compChangeOfVariables m M N)
  · rintro ⟨k, blocks_fun⟩ H
    rw [mem_compPartialSumSource_iff] at H
    simp only at H
    simp only [mem_compPartialSumTarget_iff, Composition.length, Composition.blocks, H.left,
      map_ofFn, length_ofFn, true_and, compChangeOfVariables]
    intro j
    simp only [Composition.blocksFun, (H.right _).right, List.get_ofFn]
  · rintro ⟨k, blocks_fun⟩ H ⟨k', blocks_fun'⟩ H' heq
    obtain rfl : k = k' := by
      have := (compChangeOfVariables_length m M N H).symm
      rwa [heq, compChangeOfVariables_length] at this
    congr
    funext i
    calc
      blocks_fun i = (compChangeOfVariables m M N _ H).2.blocksFun _ :=
        (compChangeOfVariables_blocksFun m M N H i).symm
      _ = (compChangeOfVariables m M N _ H').2.blocksFun _ := by
        apply Composition.blocksFun_congr <;>
        first | rw [heq] | rfl
      _ = blocks_fun' i := compChangeOfVariables_blocksFun m M N H' i
  · intro i hi
    apply compPartialSumTargetSet_image_compPartialSumSource m M N i
    simpa [compPartialSumTarget] using hi
  · rintro ⟨k, blocks_fun⟩ H
    rw [h]
theorem compPartialSumTarget_tendsto_prod_atTop :
    Tendsto (fun (p : ℕ × ℕ) => compPartialSumTarget 0 p.1 p.2) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro m n hmn a ha
    have : ∀ i, i < m.1 → i < n.1 := fun i hi => lt_of_lt_of_le hi hmn.1
    have : ∀ i, i < m.2 → i < n.2 := fun i hi => lt_of_lt_of_le hi hmn.2
    aesop
  · rintro ⟨n, c⟩
    simp only [mem_compPartialSumTarget_iff]
    obtain ⟨n, hn⟩ : BddAbove ((Finset.univ.image fun i : Fin c.length => c.blocksFun i) : Set ℕ) :=
      Finset.bddAbove _
    refine
      ⟨max n c.length + 1, bot_le, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _), fun j =>
        lt_of_le_of_lt (le_trans ?_ (le_max_left _ _)) (lt_add_one _)⟩
    apply hn
    simp only [Finset.mem_image_of_mem, Finset.mem_coe, Finset.mem_univ]
theorem compPartialSumTarget_tendsto_atTop :
    Tendsto (fun N => compPartialSumTarget 0 N N) atTop atTop := by
  apply Tendsto.comp compPartialSumTarget_tendsto_prod_atTop tendsto_atTop_diagonal
theorem comp_partialSum (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (M N : ℕ) (z : E) :
    q.partialSum M (∑ i ∈ Finset.Ico 1 N, p i fun _j => z) =
      ∑ i ∈ compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z := by
  suffices H :
    (∑ n ∈ Finset.range M,
        ∑ r ∈ Fintype.piFinset fun i : Fin n => Finset.Ico 1 N,
          q n fun i : Fin n => p (r i) fun _j => z) =
      ∑ i ∈ compPartialSumTarget 0 M N, q.compAlongComposition p i.2 fun _j => z by
    simpa only [FormalMultilinearSeries.partialSum, ContinuousMultilinearMap.map_sum_finset] using H
  rw [Finset.range_eq_Ico, Finset.sum_sigma']
  apply compChangeOfVariables_sum 0 M N
  rintro ⟨k, blocks_fun⟩ H
  apply congr _ (compChangeOfVariables_length 0 M N H).symm
  intros
  rw [← compChangeOfVariables_blocksFun 0 M N H]
  rfl
end FormalMultilinearSeries
open FormalMultilinearSeries
theorem HasFPowerSeriesWithinAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E} {t : Set F} {s : Set E}
    (hg : HasFPowerSeriesWithinAt g q t (f x)) (hf : HasFPowerSeriesWithinAt f p s x)
    (hs : Set.MapsTo f s t) : HasFPowerSeriesWithinAt (g ∘ f) (q.comp p) s x := by
  rcases hg with ⟨rg, Hg⟩
  rcases hf with ⟨rf, Hf⟩
  rcases q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos with ⟨r, r_pos : 0 < r, hr⟩
  obtain ⟨δ, δpos, hδ⟩ :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ {z : E}, z ∈ insert x s ∩ EMetric.ball x δ
      → f z ∈ insert (f x) t ∩ EMetric.ball (f x) rg := by
    have : insert (f x) t ∩ EMetric.ball (f x) rg ∈ 𝓝[insert (f x) t] (f x) := by
      apply inter_mem_nhdsWithin
      exact EMetric.ball_mem_nhds _ Hg.r_pos
    have := Hf.analyticWithinAt.continuousWithinAt_insert.tendsto_nhdsWithin (hs.insert x) this
    rcases EMetric.mem_nhdsWithin_iff.1 this with ⟨δ, δpos, Hδ⟩
    exact ⟨δ, δpos, fun {z} hz => Hδ (by rwa [Set.inter_comm])⟩
  let rf' := min rf δ
  have min_pos : 0 < min rf' r := by
    simp only [rf', r_pos, Hf.r_pos, δpos, lt_min_iff, ENNReal.coe_pos, and_self_iff]
  refine ⟨min rf' r, ?_⟩
  refine
    ⟨le_trans (min_le_right rf' r) (FormalMultilinearSeries.le_comp_radius_of_summable q p r hr),
      min_pos, fun {y} h'y hy ↦ ?_⟩
  have y_mem : y ∈ EMetric.ball (0 : E) rf :=
    (EMetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))) hy
  have fy_mem : f (x + y) ∈ insert (f x) t ∩ EMetric.ball (f x) rg := by
    apply hδ
    have : y ∈ EMetric.ball (0 : E) δ :=
      (EMetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))) hy
    simpa [-Set.mem_insert_iff, edist_eq_coe_nnnorm_sub, h'y]
  have A : Tendsto (fun n ↦ (n, ∑ a ∈ Finset.Ico 1 n, p a fun _ ↦ y))
      atTop (atTop ×ˢ 𝓝 (f (x + y) - f x)) := by
    apply Tendsto.prod_mk tendsto_id
    have L : ∀ᶠ n in atTop, (∑ a ∈ Finset.range n, p a fun _b ↦ y) - f x
        = ∑ a ∈ Finset.Ico 1 n, p a fun _b ↦ y := by
      rw [eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      symm
      rw [eq_sub_iff_add_eq', Finset.range_eq_Ico, ← Hf.coeff_zero fun _i => y,
        Finset.sum_eq_sum_Ico_succ_bot hn]
    have :
      Tendsto (fun n => (∑ a ∈ Finset.range n, p a fun _b => y) - f x) atTop
        (𝓝 (f (x + y) - f x)) :=
      (Hf.hasSum h'y y_mem).tendsto_sum_nat.sub tendsto_const_nhds
    exact Tendsto.congr' L this
  have B : Tendsto (fun n => q.partialSum n (∑ a ∈ Finset.Ico 1 n, p a fun _b ↦ y)) atTop
      (𝓝 (g (f (x + y)))) := by
    have : Tendsto (fun (z : ℕ × F) ↦ q.partialSum z.1 z.2)
        (atTop ×ˢ 𝓝 (f (x + y) - f x)) (𝓝 (g (f x + (f (x + y) - f x)))) := by
      apply Hg.tendsto_partialSum_prod (y := f (x + y) - f x)
      · simpa [edist_eq_coe_nnnorm_sub] using fy_mem.2
      · simpa using fy_mem.1
    simpa using this.comp A
  have C :
    Tendsto
      (fun n => ∑ i ∈ compPartialSumTarget 0 n n, q.compAlongComposition p i.2 fun _j => y)
      atTop (𝓝 (g (f (x + y)))) := by
    simpa [comp_partialSum] using B
  have D :
    HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (g (f (x + y))) :=
    haveI cau :
      CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i ∈ s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded _ (NNReal.summable_coe.2 hr) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ ≤
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ ≤ ‖compAlongComposition q p c‖ * (r : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const, Finset.card_fin]
          gcongr
          rw [EMetric.mem_ball, edist_eq_coe_nnnorm] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    tendsto_nhds_of_cauchySeq_of_subseq cau compPartialSumTarget_tendsto_atTop C
  have E : HasSum (fun n => (q.comp p) n fun _j => y) (g (f (x + y))) := by
    apply D.sigma
    intro n
    dsimp [FormalMultilinearSeries.comp]
    convert hasSum_fintype (α := G) (β := Composition n) _
    simp only [ContinuousMultilinearMap.sum_apply]
    rfl
  rw [Function.comp_apply]
  exact E
theorem HasFPowerSeriesAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hg : HasFPowerSeriesAt g q (f x)) (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt (g ∘ f) (q.comp p) x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf hg ⊢
  apply hg.comp hf (by simp)
theorem AnalyticWithinAt.comp {g : F → G} {f : E → F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  let ⟨_q, hq⟩ := hg
  let ⟨_p, hp⟩ := hf
  exact (hq.comp hp h).analyticWithinAt
theorem AnalyticWithinAt.comp_of_eq {g : F → G} {f : E → F} {y : F} {x : E} {t : Set F} {s : Set E}
    (hg : AnalyticWithinAt 𝕜 g t y) (hf : AnalyticWithinAt 𝕜 f s x) (h : Set.MapsTo f s t)
    (hy : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← hy] at hg
  exact hg.comp hf h
lemma AnalyticOn.comp {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp (hg x m) h
@[deprecated (since := "2024-09-26")]
alias AnalyticWithinOn.comp := AnalyticOn.comp
theorem AnalyticAt.comp {g : F → G} {f : E → F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
    (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← analyticWithinAt_univ] at hg hf ⊢
  apply hg.comp hf (by simp)
theorem AnalyticAt.comp_of_eq {g : F → G} {f : E → F} {y : F} {x : E} (hg : AnalyticAt 𝕜 g y)
    (hf : AnalyticAt 𝕜 f x) (hy : f x = y) : AnalyticAt 𝕜 (g ∘ f) x := by
  rw [← hy] at hg
  exact hg.comp hf
theorem AnalyticAt.comp_analyticWithinAt {g : F → G} {f : E → F} {x : E} {s : Set E}
    (hg : AnalyticAt 𝕜 g (f x)) (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← analyticWithinAt_univ] at hg
  exact hg.comp hf (Set.mapsTo_univ _ _)
theorem AnalyticAt.comp_analyticWithinAt_of_eq {g : F → G} {f : E → F} {x : E} {y : F} {s : Set E}
    (hg : AnalyticAt 𝕜 g y) (hf : AnalyticWithinAt 𝕜 f s x) (h : f x = y) :
    AnalyticWithinAt 𝕜 (g ∘ f) s x := by
  rw [← h] at hg
  exact hg.comp_analyticWithinAt hf
theorem AnalyticOnNhd.comp' {s : Set E} {g : F → G} {f : E → F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
    (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (g ∘ f) s :=
  fun z hz => (hg (f z) (Set.mem_image_of_mem f hz)).comp (hf z hz)
@[deprecated (since := "2024-09-26")]
alias AnalyticOn.comp' := AnalyticOnNhd.comp'
theorem AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F}
    (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set.MapsTo f s t) :
    AnalyticOnNhd 𝕜 (g ∘ f) s :=
  comp' (mono hg (Set.mapsTo'.mp st)) hf
lemma AnalyticOnNhd.comp_analyticOn {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s) :
    AnalyticOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp_analyticWithinAt (hg x m)
@[deprecated (since := "2024-09-26")]
alias AnalyticOn.comp_analyticWithinOn := AnalyticOnNhd.comp_analyticOn
namespace Composition
variable {n : ℕ}
theorem sigma_composition_eq_iff (i j : Σ a : Composition n, Composition a.length) :
    i = j ↔ i.1.blocks = j.1.blocks ∧ i.2.blocks = j.2.blocks := by
  refine ⟨by rintro rfl; exact ⟨rfl, rfl⟩, ?_⟩
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rintro ⟨h, h'⟩
  have H : a = a' := by ext1; exact h
  induction H; congr; ext1; exact h'
theorem sigma_pi_composition_eq_iff
    (u v : Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i)) :
    u = v ↔ (ofFn fun i => (u.2 i).blocks) = ofFn fun i => (v.2 i).blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases u with ⟨a, b⟩
  rcases v with ⟨a', b'⟩
  dsimp at H
  have h : a = a' := by
    ext1
    have :
      map List.sum (ofFn fun i : Fin (Composition.length a) => (b i).blocks) =
        map List.sum (ofFn fun i : Fin (Composition.length a') => (b' i).blocks) := by
      rw [H]
    simp only [map_ofFn] at this
    change
      (ofFn fun i : Fin (Composition.length a) => (b i).blocks.sum) =
        ofFn fun i : Fin (Composition.length a') => (b' i).blocks.sum at this
    simpa [Composition.blocks_sum, Composition.ofFn_blocksFun] using this
  induction h
  ext1
  · rfl
  · simp only [heq_eq_eq, ofFn_inj] at H ⊢
    ext1 i
    ext1
    exact congrFun H i
def gather (a : Composition n) (b : Composition a.length) : Composition n where
  blocks := (a.blocks.splitWrtComposition b).map sum
  blocks_pos := by
    rw [forall_mem_map]
    intro j hj
    suffices H : ∀ i ∈ j, 1 ≤ i by calc
      0 < j.length := length_pos_of_mem_splitWrtComposition hj
      _ ≤ j.sum := length_le_sum_of_one_le _ H
    intro i hi
    apply a.one_le_blocks
    rw [← a.blocks.flatten_splitWrtComposition b]
    exact mem_flatten_of_mem hj hi
  blocks_sum := by rw [← sum_flatten, flatten_splitWrtComposition, a.blocks_sum]
theorem length_gather (a : Composition n) (b : Composition a.length) :
    length (a.gather b) = b.length :=
  show (map List.sum (a.blocks.splitWrtComposition b)).length = b.blocks.length by
    rw [length_map, length_splitWrtComposition]
def sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin (a.gather b).length) : Composition ((a.gather b).blocksFun i) where
  blocks :=
    (a.blocks.splitWrtComposition b)[i.val]'(by
      rw [length_splitWrtComposition, ← length_gather]; exact i.2)
  blocks_pos {i} hi :=
    a.blocks_pos
      (by
        rw [← a.blocks.flatten_splitWrtComposition b]
        exact mem_flatten_of_mem (List.getElem_mem _) hi)
  blocks_sum := by simp [Composition.blocksFun, getElem_map, Composition.gather]
theorem length_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) :
    Composition.length (Composition.sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩) =
      Composition.blocksFun b i :=
  show List.length ((splitWrtComposition a.blocks b)[i.1]) = blocksFun b i by
    rw [getElem_map_rev List.length, getElem_of_eq (map_length_splitWrtComposition _ _)]; rfl
theorem blocksFun_sigmaCompositionAux (a : Composition n) (b : Composition a.length)
    (i : Fin b.length) (j : Fin (blocksFun b i)) :
    blocksFun (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ i.2⟩)
        ⟨j, (length_sigmaCompositionAux a b i).symm ▸ j.2⟩ =
      blocksFun a (embedding b i j) := by
  unfold sigmaCompositionAux
  rw [blocksFun, get_eq_getElem, getElem_of_eq (getElem_splitWrtComposition _ _ _ _),
    getElem_drop, getElem_take]; rfl
theorem sizeUpTo_sizeUpTo_add (a : Composition n) (b : Composition a.length) {i j : ℕ}
    (hi : i < b.length) (hj : j < blocksFun b ⟨i, hi⟩) :
    sizeUpTo a (sizeUpTo b i + j) =
      sizeUpTo (a.gather b) i +
        sizeUpTo (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) j := by
  induction j with
  | zero =>
    show
      sum (take (b.blocks.take i).sum a.blocks) =
        sum (take i (map sum (splitWrtComposition a.blocks b)))
    induction' i with i IH
    · rfl
    · have A : i < b.length := Nat.lt_of_succ_lt hi
      have B : i < List.length (map List.sum (splitWrtComposition a.blocks b)) := by simp [A]
      have C : 0 < blocksFun b ⟨i, A⟩ := Composition.blocks_pos' _ _ _
      rw [sum_take_succ _ _ B, ← IH A C]
      have :
        take (sum (take i b.blocks)) a.blocks =
          take (sum (take i b.blocks)) (take (sum (take (i + 1) b.blocks)) a.blocks) := by
        rw [take_take, min_eq_left]
        apply monotone_sum_take _ (Nat.le_succ _)
      rw [this, getElem_map, getElem_splitWrtComposition, ←
        take_append_drop (sum (take i b.blocks)) (take (sum (take (Nat.succ i) b.blocks)) a.blocks),
        sum_append]
      congr
      rw [take_append_drop]
  | succ j IHj =>
    have A : j < blocksFun b ⟨i, hi⟩ := lt_trans (lt_add_one j) hj
    have B : j < length (sigmaCompositionAux a b ⟨i, (length_gather a b).symm ▸ hi⟩) := by
      convert A; rw [← length_sigmaCompositionAux]
    have C : sizeUpTo b i + j < sizeUpTo b (i + 1) := by
      simp only [sizeUpTo_succ b hi, add_lt_add_iff_left]
      exact A
    have D : sizeUpTo b i + j < length a := lt_of_lt_of_le C (b.sizeUpTo_le _)
    have : sizeUpTo b i + Nat.succ j = (sizeUpTo b i + j).succ := rfl
    rw [this, sizeUpTo_succ _ D, IHj A, sizeUpTo_succ _ B]
    simp only [sigmaCompositionAux, add_assoc, add_left_inj, Fin.val_mk]
    rw [getElem_of_eq (getElem_splitWrtComposition _ _ _ _), getElem_drop, getElem_take' _ _ C]
def sigmaEquivSigmaPi (n : ℕ) :
    (Σ a : Composition n, Composition a.length) ≃
      Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i) where
  toFun i := ⟨i.1.gather i.2, i.1.sigmaCompositionAux i.2⟩
  invFun i :=
    ⟨{  blocks := (ofFn fun j => (i.2 j).blocks).flatten
        blocks_pos := by
          simp only [and_imp, List.mem_flatten, exists_imp, forall_mem_ofFn_iff]
          exact @fun i j hj => Composition.blocks_pos _ hj
        blocks_sum := by simp [sum_ofFn, Composition.blocks_sum, Composition.sum_blocksFun] },
      { blocks := ofFn fun j => (i.2 j).length
        blocks_pos := by
          intro k hk
          refine ((forall_mem_ofFn_iff (P := fun i => 0 < i)).2 fun j => ?_) k hk
          exact Composition.length_pos_of_pos _ (Composition.blocks_pos' _ _ _)
        blocks_sum := by dsimp only [Composition.length]; simp [sum_ofFn] }⟩
  left_inv := by
    rintro ⟨a, b⟩
    rw [sigma_composition_eq_iff]
    dsimp
    constructor
    · conv_rhs =>
        rw [← flatten_splitWrtComposition a.blocks b, ← ofFn_get (splitWrtComposition a.blocks b)]
      have A : length (gather a b) = List.length (splitWrtComposition a.blocks b) := by
        simp only [length, gather, length_map, length_splitWrtComposition]
      congr! 2
      exact (Fin.heq_fun_iff A (α := List ℕ)).2 fun i => rfl
    · have B : Composition.length (Composition.gather a b) = List.length b.blocks :=
        Composition.length_gather _ _
      conv_rhs => rw [← ofFn_getElem b.blocks]
      congr 1
      refine (Fin.heq_fun_iff B).2 fun i => ?_
      rw [sigmaCompositionAux, Composition.length, List.getElem_map_rev List.length,
        List.getElem_of_eq (map_length_splitWrtComposition _ _)]
  right_inv := by
    rintro ⟨c, d⟩
    have : map List.sum (ofFn fun i : Fin (Composition.length c) => (d i).blocks) = c.blocks := by
      simp [map_ofFn, Function.comp_def, Composition.blocks_sum, Composition.ofFn_blocksFun]
    rw [sigma_pi_composition_eq_iff]
    dsimp
    congr! 1
    · congr
      ext1
      dsimp [Composition.gather]
      rwa [splitWrtComposition_flatten]
      simp only [map_ofFn]
      rfl
    · rw [Fin.heq_fun_iff]
      · intro i
        dsimp [Composition.sigmaCompositionAux]
        rw [getElem_of_eq (splitWrtComposition_flatten _ _ _)]
        · simp only [List.getElem_ofFn]
        · simp only [map_ofFn]
          rfl
      · congr
end Composition
namespace FormalMultilinearSeries
open Composition
theorem comp_assoc (r : FormalMultilinearSeries 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) : (r.comp q).comp p = r.comp (q.comp p) := by
  ext n v
  let f : (Σ a : Composition n, Composition a.length) → H := fun c =>
    r c.2.length (applyComposition q c.2 (applyComposition p c.1 v))
  let g : (Σ c : Composition n, ∀ i : Fin c.length, Composition (c.blocksFun i)) → H := fun c =>
    r c.1.length fun i : Fin c.1.length =>
      q (c.2 i).length (applyComposition p (c.2 i) (v ∘ c.1.embedding i))
  suffices ∑ c, f c = ∑ c, g c by
    simpa (config := { unfoldPartialApp := true }) only [FormalMultilinearSeries.comp,
      ContinuousMultilinearMap.sum_apply, compAlongComposition_apply, Finset.sum_sigma',
      applyComposition, ContinuousMultilinearMap.map_sum]
  rw [← (sigmaEquivSigmaPi n).sum_comp]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  dsimp [sigmaEquivSigmaPi]
  apply r.congr (Composition.length_gather a b).symm
  intro i hi1 hi2
  apply q.congr (length_sigmaCompositionAux a b _).symm
  intro j hj1 hj2
  apply p.congr (blocksFun_sigmaCompositionAux a b _ _).symm
  intro k hk1 hk2
  refine congr_arg v (Fin.ext ?_)
  dsimp [Composition.embedding]
  rw [sizeUpTo_sizeUpTo_add _ _ hi1 hj1, add_assoc]
end FormalMultilinearSeries