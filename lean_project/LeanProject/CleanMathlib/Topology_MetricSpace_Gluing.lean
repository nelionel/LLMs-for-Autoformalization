import Mathlib.Topology.MetricSpace.Isometry
noncomputable section
universe u v w
open Function Set Uniformity Topology
namespace Metric
section ApproxGluing
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}
def glueDist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : X ⊕ Y → X ⊕ Y → ℝ
  | .inl x, .inl y => dist x y
  | .inr x, .inr y => dist x y
  | .inl x, .inr y => (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
  | .inr x, .inl y => (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε
private theorem glueDist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glueDist Φ Ψ ε x x = 0
  | .inl _ => dist_self _
  | .inr _ => dist_self _
theorem glueDist_glued_points [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
    glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p)) = ε := by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : ∀ q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ =>
      add_nonneg dist_nonneg dist_nonneg
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]
private theorem glueDist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Φ Ψ ε x y = glueDist Φ Ψ ε y x
  | .inl _, .inl _ => dist_comm _ _
  | .inr _, .inr _ => dist_comm _ _
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl
theorem glueDist_swap (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Ψ Φ ε x.swap y.swap = glueDist Φ Ψ ε x y
  | .inl _, .inl _ => rfl
  | .inr _, .inr _ => rfl
  | .inl _, .inr _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, dist_comm, add_comm]
  | .inr _, .inl _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, dist_comm, add_comm]
theorem le_glueDist_inl_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inl x) (.inr y) :=
  le_add_of_nonneg_left <| Real.iInf_nonneg fun _ => add_nonneg dist_nonneg dist_nonneg
theorem le_glueDist_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inr x) (.inl y) := by
  rw [glueDist_comm]; apply le_glueDist_inl_inr
section
variable [Nonempty Z]
private theorem glueDist_triangle_inl_inr_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x : X) (y z : Y) :
    glueDist Φ Ψ ε (.inl x) (.inr z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inr z) := by
  simp only [glueDist]
  rw [add_right_comm, add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => add_nonneg dist_nonneg dist_nonneg
  · linarith [dist_triangle_left z (Ψ p) y]
private theorem glueDist_triangle_inl_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) (x : X) (y : Y) (z : X) :
    glueDist Φ Ψ ε (.inl x) (.inl z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inl z) := by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm, add_assoc, ← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]
private theorem glueDist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) :
    ∀ x y z, glueDist Φ Ψ ε x z ≤ glueDist Φ Ψ ε x y + glueDist Φ Ψ ε y z
  | .inl _, .inl _, .inl _ => dist_triangle _ _ _
  | .inr _, .inr _, .inr _ => dist_triangle _ _ _
  | .inr x, .inl y, .inl z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inr
  | .inr x, .inr y, .inl z => by
    simpa only [glueDist_comm, add_comm] using glueDist_triangle_inl_inr_inr _ _ _ z y x
  | .inl x, .inl y, .inr z => by
    simpa only [← glueDist_swap Φ, glueDist_comm, add_comm, Sum.swap_inl, Sum.swap_inr]
      using glueDist_triangle_inl_inr_inr Ψ Φ ε z y x
  | .inl _, .inr _, .inr _ => glueDist_triangle_inl_inr_inr ..
  | .inl x, .inr y, .inl z => glueDist_triangle_inl_inr_inl Φ Ψ ε H x y z
  | .inr x, .inl y, .inr z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inl
    simpa only [abs_sub_comm]
end
private theorem eq_of_glueDist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
    ∀ p q : X ⊕ Y, glueDist Φ Ψ ε p q = 0 → p = q
  | .inl x, .inl y, h => by rw [eq_of_dist_eq_zero h]
  | .inl x, .inr y, h => by exfalso; linarith [le_glueDist_inl_inr Φ Ψ ε x y]
  | .inr x, .inl y, h => by exfalso; linarith [le_glueDist_inr_inl Φ Ψ ε x y]
  | .inr x, .inr y, h => by rw [eq_of_dist_eq_zero h]
theorem Sum.mem_uniformity_iff_glueDist (hε : 0 < ε) (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ δ > 0, ∀ a b, glueDist Φ Ψ ε a b < δ → (a, b) ∈ s := by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_lt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_lt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩
def glueMetricApprox [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) : MetricSpace (X ⊕ Y) where
  dist := glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := eq_of_glueDist_eq_zero Φ Ψ ε ε0 _ _
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ <| Sum.mem_uniformity_iff_glueDist ε0
end ApproxGluing
section Sum
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y]
protected def Sum.dist : X ⊕ Y → X ⊕ Y → ℝ
  | .inl a, .inl a' => dist a a'
  | .inr b, .inr b' => dist b b'
  | .inl a, .inr b => dist a (Nonempty.some ⟨a⟩) + 1 + dist (Nonempty.some ⟨b⟩) b
  | .inr b, .inl a => dist b (Nonempty.some ⟨b⟩) + 1 + dist (Nonempty.some ⟨a⟩) a
theorem Sum.dist_eq_glueDist {p q : X ⊕ Y} (x : X) (y : Y) :
    Sum.dist p q =
      glueDist (fun _ : Unit => Nonempty.some ⟨x⟩) (fun _ : Unit => Nonempty.some ⟨y⟩) 1 p q := by
  cases p <;> cases q <;> first |rfl|simp [Sum.dist, glueDist, dist_comm, add_comm,
    add_left_comm, add_assoc]
private theorem Sum.dist_comm (x y : X ⊕ Y) : Sum.dist x y = Sum.dist y x := by
  cases x <;> cases y <;> simp [Sum.dist, _root_.dist_comm, add_comm, add_left_comm, add_assoc]
theorem Sum.one_le_dist_inl_inr {x : X} {y : Y} : 1 ≤ Sum.dist (.inl x) (.inr y) :=
  le_trans (le_add_of_nonneg_right dist_nonneg) <|
    add_le_add_right (le_add_of_nonneg_left dist_nonneg) _
theorem Sum.one_le_dist_inr_inl {x : X} {y : Y} : 1 ≤ Sum.dist (.inr y) (.inl x) := by
  rw [Sum.dist_comm]; exact Sum.one_le_dist_inl_inr
private theorem Sum.mem_uniformity (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ ε > 0, ∀ a b, Sum.dist a b < ε → (a, b) ∈ s := by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inl_inr
    · cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inr_inl
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, mem_uniformity_dist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩
def metricSpaceSum : MetricSpace (X ⊕ Y) where
  dist := Sum.dist
  dist_self x := by cases x <;> simp only [Sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle
    | .inl p, .inl q, .inl r => dist_triangle p q r
    | .inl p, .inr q, _ => by
      simp only [Sum.dist_eq_glueDist p q]
      exact glueDist_triangle _ _ _ (by norm_num) _ _ _
    | _, .inl q, .inr r => by
      simp only [Sum.dist_eq_glueDist q r]
      exact glueDist_triangle _ _ _ (by norm_num) _ _ _
    | .inr p, _, .inl r => by
      simp only [Sum.dist_eq_glueDist r p]
      exact glueDist_triangle _ _ _ (by norm_num) _ _ _
    | .inr p, .inr q, .inr r => dist_triangle p q r
  eq_of_dist_eq_zero {p q} h := by
    cases' p with p p <;> cases' q with q q
    · rw [eq_of_dist_eq_zero h]
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist p q).symm.trans h)
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist q p).symm.trans h)
    · rw [eq_of_dist_eq_zero h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity
attribute [local instance] metricSpaceSum
theorem Sum.dist_eq {x y : X ⊕ Y} : dist x y = Sum.dist x y := rfl
theorem isometry_inl : Isometry (Sum.inl : X → X ⊕ Y) :=
  Isometry.of_dist_eq fun _ _ => rfl
theorem isometry_inr : Isometry (Sum.inr : Y → X ⊕ Y) :=
  Isometry.of_dist_eq fun _ _ => rfl
end Sum
namespace Sigma
variable {ι : Type*} {E : ι → Type*} [∀ i, MetricSpace (E i)]
open Classical in
protected def dist : (Σ i, E i) → (Σ i, E i) → ℝ
  | ⟨i, x⟩, ⟨j, y⟩ =>
    if h : i = j then
      haveI : E j = E i := by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y
def instDist : Dist (Σi, E i) :=
  ⟨Sigma.dist⟩
attribute [local instance] Sigma.instDist
@[simp]
theorem dist_same (i : ι) (x y : E i) : dist (Sigma.mk i x) ⟨i, y⟩ = dist x y := by
  simp [Dist.dist, Sigma.dist]
@[simp]
theorem dist_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y :=
  dif_neg h
theorem one_le_dist_of_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    1 ≤ dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ := by
  rw [Sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]
theorem fst_eq_of_dist_lt_one (x y : Σi, E i) (h : dist x y < 1) : x.1 = y.1 := by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h
protected theorem dist_triangle (x y z : Σi, E i) : dist x z ≤ dist x y + dist y z := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z ≤ dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ ≤ _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ ≤ _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]
protected theorem isOpen_iff (s : Set (Σi, E i)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ball x ε ⊆ Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ Sigma.dist ⟨i, x⟩ ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine fun H => isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ∀ y, dist (⟨i, x⟩ : Σj, E j) y < ε → y ∈ s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.dist_same]
    exact mem_ball'.1 hy
protected def metricSpace : MetricSpace (Σi, E i) := by
  refine MetricSpace.ofDistTopology Sigma.dist ?_ ?_ Sigma.dist_triangle Sigma.isOpen_iff ?_
  · rintro ⟨i, x⟩
    simp [Sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [Sigma.dist, dist_comm]
    · simp only [Sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [Sigma.dist]
    · intro h
      apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ Sigma.dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by rw [h]; exact zero_lt_one
attribute [local instance] Sigma.metricSpace
open Topology
open Filter
theorem isometry_mk (i : ι) : Isometry (Sigma.mk i : E i → Σk, E k) :=
  Isometry.of_dist_eq fun x y => by simp
protected theorem completeSpace [∀ i, CompleteSpace (E i)] : CompleteSpace (Σi, E i) := by
  set s : ι → Set (Σi, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σk, E k) × Σk, E k | dist p.1 p.2 < 1 }
  have hc : ∀ i, IsComplete (s i) := fun i => by
    simp only [s, ← range_sigmaMk]
    exact (isometry_mk i).isUniformInducing.isComplete_range
  have hd : ∀ (i j), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert isComplete_iUnion_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp only [s, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]
end Sigma
section Gluing
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Nonempty Z] [MetricSpace Z] [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y}
  {ε : ℝ}
def gluePremetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (X ⊕ Y) where
  dist := glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq]; simp
def GlueSpace (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _ :=
  @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace
instance (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : MetricSpace (GlueSpace hΦ hΨ) :=
  inferInstanceAs <| MetricSpace <|
    @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace
def toGlueL (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inl x)
def toGlueR (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inr y)
instance inhabitedLeft (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueL _ _ default⟩
instance inhabitedRight (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueR _ _ default⟩
theorem toGlue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    toGlueL hΦ hΨ ∘ Φ = toGlueR hΦ hΨ ∘ Ψ := by
  let i : PseudoMetricSpace (X ⊕ Y) := gluePremetric hΦ hΨ
  let _ := i.toUniformSpace.toTopologicalSpace
  funext
  simp only [comp, toGlueL, toGlueR]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact glueDist_glued_points Φ Ψ 0 _
theorem toGlueL_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueL hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl
theorem toGlueR_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueR hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl
end Gluing
section InductiveLimit
open Nat
variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {f : ∀ n, X n → X (n + 1)}
def inductiveLimitDist (f : ∀ n, X n → X (n + 1)) (x y : Σn, X n) : ℝ :=
  dist (leRecOn (le_max_left x.1 y.1) (f _) x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) (f _) y.2 : X (max x.1 y.1))
theorem inductiveLimitDist_eq_dist (I : ∀ n, Isometry (f n)) (x y : Σn, X n) :
    ∀ m (hx : x.1 ≤ m) (hy : y.1 ≤ m), inductiveLimitDist f x y =
      dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m)
  | 0, hx, hy => by
    cases' x with i x; cases' y with j y
    obtain rfl : i = 0 := nonpos_iff_eq_zero.1 hx
    obtain rfl : j = 0 := nonpos_iff_eq_zero.1 hy
    rfl
  | (m + 1), hx, hy => by
    by_cases h : max x.1 y.1 = (m + 1)
    · generalize m + 1 = m' at *
      subst m'
      rfl
    · have : max x.1 y.1 ≤ succ m := by simp [hx, hy]
      have : max x.1 y.1 ≤ m := by simpa [h] using of_le_succ this
      have xm : x.1 ≤ m := le_trans (le_max_left _ _) this
      have ym : y.1 ≤ m := le_trans (le_max_right _ _) this
      rw [leRecOn_succ xm, leRecOn_succ ym, (I m).dist_eq]
      exact inductiveLimitDist_eq_dist I x y m xm ym
def inductivePremetric (I : ∀ n, Isometry (f n)) : PseudoMetricSpace (Σn, X n) where
  dist := inductiveLimitDist f
  dist_self x := by simp [dist, inductiveLimitDist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 ≤ m := le_max_left _ _
    have hy : y.1 ≤ m := le_max_right _ _
    unfold dist; simp only
    rw [inductiveLimitDist_eq_dist I x y m hx hy, inductiveLimitDist_eq_dist I y x m hy hx,
      dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 ≤ m := le_max_right _ _
    calc
      inductiveLimitDist f x z = dist (leRecOn hx (f _) x.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        inductiveLimitDist_eq_dist I x z m hx hz
      _ ≤ dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) +
            dist (leRecOn hy (f _) y.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductiveLimitDist f x y + inductiveLimitDist f y z := by
        rw [inductiveLimitDist_eq_dist I x y m hx hy, inductiveLimitDist_eq_dist I y z m hy hz]
attribute [local instance] inductivePremetric
def InductiveLimit (I : ∀ n, Isometry (f n)) : Type _ :=
  @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace
instance {I : ∀ (n : ℕ), Isometry (f n)} : MetricSpace (InductiveLimit (f := f) I) :=
  inferInstanceAs <| MetricSpace <|
    @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace
def toInductiveLimit (I : ∀ n, Isometry (f n)) (n : ℕ) (x : X n) : Metric.InductiveLimit I :=
  Quotient.mk'' (Sigma.mk n x)
instance (I : ∀ n, Isometry (f n)) [Inhabited (X 0)] : Inhabited (InductiveLimit I) :=
  ⟨toInductiveLimit _ 0 default⟩
theorem toInductiveLimit_isometry (I : ∀ n, Isometry (f n)) (n : ℕ) :
    Isometry (toInductiveLimit I n) :=
  Isometry.of_dist_eq fun x y => by
    change inductiveLimitDist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductiveLimitDist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_refl n) (le_refl n), leRecOn_self,
      leRecOn_self]
theorem toInductiveLimit_commute (I : ∀ n, Isometry (f n)) (n : ℕ) :
    toInductiveLimit I n.succ ∘ f n = toInductiveLimit I n := by
  let h := inductivePremetric I
  let _ := h.toUniformSpace.toTopologicalSpace
  funext x
  simp only [comp, toInductiveLimit]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  show inductiveLimitDist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  rw [inductiveLimitDist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ, leRecOn_self,
    leRecOn_succ, leRecOn_self, dist_self]
  exact le_succ _
end InductiveLimit
end Metric