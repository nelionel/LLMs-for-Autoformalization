import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sets.Compacts
noncomputable section
universe u
open Set Function TopologicalSpace Filter Topology ENNReal
namespace EMetric
section
variable {α : Type u} [EMetricSpace α] {s : Set α}
instance Closeds.emetricSpace : EMetricSpace (Closeds α) where
  edist s t := hausdorffEdist (s : Set α) t
  edist_self _ := hausdorffEdist_self
  edist_comm _ _ := hausdorffEdist_comm
  edist_triangle _ _ _ := hausdorffEdist_triangle
  eq_of_edist_eq_zero {s t} h :=
    Closeds.ext <| (hausdorffEdist_zero_iff_eq_of_closed s.closed t.closed).1 h
theorem continuous_infEdist_hausdorffEdist :
    Continuous fun p : α × Closeds α => infEdist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEdist x s ≤ infEdist x t + hausdorffEdist (t : Set α) s :=
      infEdist_le_infEdist_add_hausdorffEdist
    _ ≤ infEdist y t + edist x y + hausdorffEdist (t : Set α) s :=
      (add_le_add_right infEdist_le_infEdist_add_edist _)
    _ = infEdist y t + (edist x y + hausdorffEdist (s : Set α) t) := by
      rw [add_assoc, hausdorffEdist_comm]
    _ ≤ infEdist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) :=
      (add_le_add_left (add_le_add (le_max_left _ _) (le_max_right _ _)) _)
    _ = infEdist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]
theorem isClosed_subsets_of_isClosed (hs : IsClosed s) :
    IsClosed { t : Closeds α | (t : Set α) ⊆ s } := by
  refine isClosed_of_closure_subset fun
    (t : Closeds α) (ht : t ∈ closure {t : Closeds α | (t : Set α) ⊆ s}) (x : α) (hx : x ∈ t) => ?_
  have : x ∈ closure s := by
    refine mem_closure_iff.2 fun ε εpos => ?_
    obtain ⟨u : Closeds α, hu : u ∈ {t : Closeds α | (t : Set α) ⊆ s}, Dtu : edist t u < ε⟩ :=
      mem_closure_iff.1 ht ε εpos
    obtain ⟨y : α, hy : y ∈ u, Dxy : edist x y < ε⟩ := exists_edist_lt_of_hausdorffEdist_lt hx Dtu
    exact ⟨y, hu hy, Dxy⟩
  rwa [hs.closure_eq] at this
theorem Closeds.edist_eq {s t : Closeds α} : edist s t = hausdorffEdist (s : Set α) t :=
  rfl
instance Closeds.completeSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
  let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n
  have B_pos : ∀ n, (0 : ℝ≥0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : ∀ n, B n ≠ ⊤ := by simp [B, ENNReal.pow_ne_top]
  refine complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m ≥ n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  have I1 : ∀ n, ∀ x ∈ s n, ∃ y ∈ t0, edist x y ≤ 2 * B n := by
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      ∃ z : ∀ l, s (n + l), (z 0 : α) = x ∧ ∀ k, edist (z k : α) (z (k + 1) : α) ≤ B n / 2 ^ k := by
      have : ∀ (l) (z : s (n + l)), ∃ z' : s (n + l + 1), edist (z : α) z' ≤ B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : ∃ z' ∈ s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEdist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, Nat.rec_add_one, true_and]
      exact fun k => (this k _).choose_spec
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    have : y ∈ t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop, Set.mem_preimage,
              Set.preimage_iUnion]
            exact ⟨k, fun m hm => ⟨n + m, zero_add k ▸ add_le_add (zero_le n) hm, (z m).2⟩⟩)
    use this
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : ∀ n, ∀ x ∈ t0, ∃ y ∈ s n, edist x y ≤ 2 * B n := by
    intro n x xt0
    have : x ∈ closure (⋃ m ≥ n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : ℕ, m_ge_n : m ≥ n, hm : z ∈ (s m : Set α)⟩ := hz
    have : hausdorffEdist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y ∈ (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEdist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := add_le_add (le_of_lt Dxz) (le_of_lt Dzy)
          _ = 2 * B n := (two_mul _).symm
          ⟩
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n =>
    hausdorffEdist_le_of_mem_edist (I1 n) (I2 n)
  refine tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
      by simp [ENNReal.one_lt_two]) (Or.inr <| by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩
instance Closeds.compactSpace [CompactSpace α] : CompactSpace (Closeds α) :=
  ⟨by
    refine
      isCompact_of_totallyBounded_isClosed (EMetric.totallyBounded_iff.2 fun ε εpos => ?_)
        isClosed_univ
    rcases exists_between εpos with ⟨δ, δpos, δlt⟩
    obtain ⟨s : Set α, fs : s.Finite, hs : univ ⊆ ⋃ y ∈ s, ball y δ⟩ :=
      EMetric.totallyBounded_iff.1
        (isCompact_iff_totallyBounded_isComplete.1 (@isCompact_univ α _ _)).1 δ δpos
    have main : ∀ u : Set α, ∃ v ⊆ s, hausdorffEdist u v ≤ δ := by
      intro u
      let v := { x : α | x ∈ s ∧ ∃ y ∈ u, edist x y < δ }
      exists v, (fun x hx => hx.1 : v ⊆ s)
      refine hausdorffEdist_le_of_mem_edist ?_ ?_
      · intro x hx
        have : x ∈ ⋃ y ∈ s, ball y δ := hs (by simp)
        rcases mem_iUnion₂.1 this with ⟨y, ys, dy⟩
        have : edist y x < δ := by simpa [edist_comm]
        exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_lt dy⟩
      · rintro x ⟨_, ⟨y, yu, hy⟩⟩
        exact ⟨y, yu, le_of_lt hy⟩
    let F := { f : Closeds α | (f : Set α) ⊆ s }
    refine ⟨F, ?_, fun u _ => ?_⟩
    · apply @Finite.of_finite_image _ _ F _
      · apply fs.finite_subsets.subset fun b => _
        · exact fun s => (s : Set α)
        simp only [F, and_imp, Set.mem_image, Set.mem_setOf_eq, exists_imp]
        intro _ x hx hx'
        rwa [hx'] at hx
      · exact SetLike.coe_injective.injOn
    · obtain ⟨t0, t0s, Dut0⟩ := main u
      have : IsClosed t0 := (fs.subset t0s).isCompact.isClosed
      let t : Closeds α := ⟨t0, this⟩
      have : t ∈ F := t0s
      have : edist u t < ε := lt_of_le_of_lt Dut0 δlt
      apply mem_iUnion₂.2
      exact ⟨t, ‹t ∈ F›, this⟩⟩
instance NonemptyCompacts.emetricSpace : EMetricSpace (NonemptyCompacts α) where
  edist s t := hausdorffEdist (s : Set α) t
  edist_self _ := hausdorffEdist_self
  edist_comm _ _ := hausdorffEdist_comm
  edist_triangle _ _ _ := hausdorffEdist_triangle
  eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEdist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this
theorem NonemptyCompacts.ToCloseds.isUniformEmbedding :
    IsUniformEmbedding (@NonemptyCompacts.toCloseds α _ _) :=
  Isometry.isUniformEmbedding fun _ _ => rfl
@[deprecated (since := "2024-10-01")]
alias NonemptyCompacts.ToCloseds.uniformEmbedding := NonemptyCompacts.ToCloseds.isUniformEmbedding
theorem NonemptyCompacts.isClosed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) := by
  have :
    range NonemptyCompacts.toCloseds =
      { s : Closeds α | (s : Set α).Nonempty ∧ IsCompact (s : Set α) } := by
    ext s
    refine ⟨?_, fun h => ⟨⟨⟨s, h.2⟩, h.1⟩, Closeds.ext rfl⟩⟩
    rintro ⟨s, hs, rfl⟩
    exact ⟨s.nonempty, s.isCompact⟩
  rw [this]
  refine isClosed_of_closure_subset fun s hs => ⟨?_, ?_⟩
  · 
    rcases mem_closure_iff.1 hs ⊤ ENNReal.coe_lt_top with ⟨t, ht, Dst⟩
    rw [edist_comm] at Dst
    exact nonempty_of_hausdorffEdist_ne_top ht.1 (ne_of_lt Dst)
  · refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, s.closed.isComplete⟩
    refine totallyBounded_iff.2 fun ε (εpos : 0 < ε) => ?_
    rcases mem_closure_iff.1 hs (ε / 2) (ENNReal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
    rcases totallyBounded_iff.1 (isCompact_iff_totallyBounded_isComplete.1 ht.2).1 (ε / 2)
        (ENNReal.half_pos εpos.ne') with
      ⟨u, fu, ut⟩
    refine ⟨u, ⟨fu, fun x hx => ?_⟩⟩
    rcases exists_edist_lt_of_hausdorffEdist_lt hx Dst with ⟨z, hz, Dxz⟩
    rcases mem_iUnion₂.1 (ut hz) with ⟨y, hy, Dzy⟩
    have : edist x y < ε :=
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add Dxz Dzy
        _ = ε := ENNReal.add_halves _
    exact mem_biUnion hy this
instance NonemptyCompacts.completeSpace [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  (completeSpace_iff_isComplete_range
        NonemptyCompacts.ToCloseds.isUniformEmbedding.isUniformInducing).2 <|
    NonemptyCompacts.isClosed_in_closeds.isComplete
instance NonemptyCompacts.compactSpace [CompactSpace α] : CompactSpace (NonemptyCompacts α) :=
  ⟨by
    rw [NonemptyCompacts.ToCloseds.isUniformEmbedding.isEmbedding.isCompact_iff, image_univ]
    exact NonemptyCompacts.isClosed_in_closeds.isCompact⟩
instance NonemptyCompacts.secondCountableTopology [SecondCountableTopology α] :
    SecondCountableTopology (NonemptyCompacts α) :=
  haveI : SeparableSpace (NonemptyCompacts α) := by
    rcases exists_countable_dense α with ⟨s, cs, s_dense⟩
    let v0 := { t : Set α | t.Finite ∧ t ⊆ s }
    let v : Set (NonemptyCompacts α) := { t : NonemptyCompacts α | (t : Set α) ∈ v0 }
    refine ⟨⟨v, ?_, ?_⟩⟩
    · have : v0.Countable := countable_setOf_finite_subset cs
      exact this.preimage SetLike.coe_injective
    · refine fun t => mem_closure_iff.2 fun ε εpos => ?_
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      have δpos' : 0 < δ / 2 := ENNReal.half_pos δpos.ne'
      have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2 := by
        intro x
        rcases mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
        exact ⟨y, ⟨ys, hy⟩⟩
      let F x := (Exy x).choose
      have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => (Exy x).choose_spec
      have : TotallyBounded (t : Set α) := t.isCompact.totallyBounded
      obtain ⟨a : Set α, af : Set.Finite a, ta : (t : Set α) ⊆ ⋃ y ∈ a, ball y (δ / 2)⟩ :=
        totallyBounded_iff.1 this (δ / 2) δpos'
      let b := F '' a
      have : b.Finite := af.image _
      have tb : ∀ x ∈ t, ∃ y ∈ b, edist x y < δ := by
        intro x hx
        rcases mem_iUnion₂.1 (ta hx) with ⟨z, za, Dxz⟩
        exists F z, mem_image_of_mem _ za
        calc
          edist x (F z) ≤ edist x z + edist z (F z) := edist_triangle _ _ _
          _ < δ / 2 + δ / 2 := ENNReal.add_lt_add Dxz (Fspec z).2
          _ = δ := ENNReal.add_halves _
      let c := { y ∈ b | ∃ x ∈ t, edist x y < δ }
      have : c.Finite := ‹b.Finite›.subset fun x hx => hx.1
      have tc : ∀ x ∈ t, ∃ y ∈ c, edist x y ≤ δ := by
        intro x hx
        rcases tb x hx with ⟨y, yv, Dxy⟩
        have : y ∈ c := by simpa [c, -mem_image] using ⟨yv, ⟨x, hx, Dxy⟩⟩
        exact ⟨y, this, le_of_lt Dxy⟩
      have ct : ∀ y ∈ c, ∃ x ∈ t, edist y x ≤ δ := by
        rintro y ⟨_, x, xt, Dyx⟩
        have : edist y x ≤ δ :=
          calc
            edist y x = edist x y := edist_comm _ _
            _ ≤ δ := le_of_lt Dyx
        exact ⟨x, xt, this⟩
      have : hausdorffEdist (t : Set α) c ≤ δ := hausdorffEdist_le_of_mem_edist tc ct
      have Dtc : hausdorffEdist (t : Set α) c < ε := this.trans_lt δlt
      have hc : c.Nonempty := nonempty_of_hausdorffEdist_ne_top t.nonempty (ne_top_of_lt Dtc)
      let d : NonemptyCompacts α := ⟨⟨c, ‹c.Finite›.isCompact⟩, hc⟩
      have : c ⊆ s := by
        intro x hx
        rcases (mem_image _ _ _).1 hx.1 with ⟨y, ⟨_, yx⟩⟩
        rw [← yx]
        exact (Fspec y).1
      have : d ∈ v := ⟨‹c.Finite›, this⟩
      exact ⟨d, ‹d ∈ v›, Dtc⟩
  UniformSpace.secondCountable_of_separable (NonemptyCompacts α)
end
end EMetric
namespace Metric
section
variable {α : Type u} [MetricSpace α]
instance NonemptyCompacts.metricSpace : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    hausdorffEdist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} :
    dist x y = hausdorffDist (x : Set α) y :=
  rfl
theorem lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)
theorem lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 := by
  convert @LipschitzWith.uncurry α (NonemptyCompacts α) ℝ _ _ _
    (fun (x : α) (s : NonemptyCompacts α) => infDist x s) 1 1
    (fun s => lipschitz_infDist_pt ↑s) lipschitz_infDist_set
  norm_num
theorem uniformContinuous_infDist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_infDist.uniformContinuous
end 
end Metric 