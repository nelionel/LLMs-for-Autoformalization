import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.GromovHausdorffRealized
import Mathlib.Topology.MetricSpace.Kuratowski
noncomputable section
open scoped Topology ENNReal Cardinal
open Set Function TopologicalSpace Filter Metric Quotient Bornology
open BoundedContinuousFunction Nat Int kuratowskiEmbedding
open Sum (inl inr)
local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞
universe u v w
attribute [local instance] metricSpaceSum
namespace GromovHausdorff
section GHSpace
private def IsometryRel (x : NonemptyCompacts ℓ_infty_ℝ) (y : NonemptyCompacts ℓ_infty_ℝ) : Prop :=
  Nonempty (x ≃ᵢ y)
private theorem equivalence_isometryRel : Equivalence IsometryRel :=
  ⟨fun _ => Nonempty.intro (IsometryEquiv.refl _), fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩
instance IsometryRel.setoid : Setoid (NonemptyCompacts ℓ_infty_ℝ) :=
  Setoid.mk IsometryRel equivalence_isometryRel
def GHSpace : Type :=
  Quotient IsometryRel.setoid
def toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHSpace :=
  ⟦NonemptyCompacts.kuratowskiEmbedding X⟧
instance : Inhabited GHSpace :=
  ⟨Quot.mk _ ⟨⟨{0}, isCompact_singleton⟩, singleton_nonempty _⟩⟩
def GHSpace.Rep (p : GHSpace) : Type :=
  (Quotient.out p : NonemptyCompacts ℓ_infty_ℝ)
theorem eq_toGHSpace_iff {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {p : NonemptyCompacts ℓ_infty_ℝ} :
    ⟦p⟧ = toGHSpace X ↔ ∃ Ψ : X → ℓ_infty_ℝ, Isometry Ψ ∧ range Ψ = p := by
  simp only [toGHSpace, Quotient.eq]
  refine ⟨fun h => ?_, ?_⟩
  · rcases Setoid.symm h with ⟨e⟩
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.trans e
    use fun x => f x, isometry_subtype_coe.comp f.isometry
    erw [range_comp, f.range_eq_univ, Set.image_univ, Subtype.range_coe]
  · rintro ⟨Ψ, ⟨isomΨ, rangeΨ⟩⟩
    have f :=
      ((kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm.trans
          isomΨ.isometryEquivOnRange).symm
    have E : (range Ψ ≃ᵢ NonemptyCompacts.kuratowskiEmbedding X)
        = (p ≃ᵢ range (kuratowskiEmbedding X)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rw [rangeΨ]; rfl
    exact ⟨cast E f⟩
theorem eq_toGHSpace {p : NonemptyCompacts ℓ_infty_ℝ} : ⟦p⟧ = toGHSpace p :=
  eq_toGHSpace_iff.2 ⟨fun x => x, isometry_subtype_coe, Subtype.range_coe⟩
section
instance repGHSpaceMetricSpace {p : GHSpace} : MetricSpace p.Rep :=
  inferInstanceAs <| MetricSpace p.out
instance rep_gHSpace_compactSpace {p : GHSpace} : CompactSpace p.Rep :=
  inferInstanceAs <| CompactSpace p.out
instance rep_gHSpace_nonempty {p : GHSpace} : Nonempty p.Rep :=
  inferInstanceAs <| Nonempty p.out
end
theorem GHSpace.toGHSpace_rep (p : GHSpace) : toGHSpace p.Rep = p := by
  change toGHSpace (Quot.out p : NonemptyCompacts ℓ_infty_ℝ) = p
  rw [← eq_toGHSpace]
  exact Quot.out_eq p
theorem toGHSpace_eq_toGHSpace_iff_isometryEquiv {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y) :=
  ⟨by
    simp only [toGHSpace]
    rw [Quotient.eq]
    rintro ⟨e⟩
    have I :
      (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) =
        (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange.symm
    exact ⟨f.trans <| (cast I e).trans g⟩, by
    rintro ⟨e⟩
    simp only [toGHSpace, Quotient.eq']
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange
    have I :
      (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) =
        (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    rw [Quotient.eq]
    exact ⟨cast I ((f.trans e).trans g)⟩⟩
instance : Dist GHSpace where
  dist x y := sInf <| (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
    hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) '' { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y }
def ghDist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y]
    [Nonempty Y] [CompactSpace Y] : ℝ :=
  dist (toGHSpace X) (toGHSpace Y)
theorem dist_ghDist (p q : GHSpace) : dist p q = ghDist p.Rep q.Rep := by
  rw [ghDist, p.toGHSpace_rep, q.toGHSpace_rep]
theorem ghDist_le_hausdorffDist {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {γ : Type w} [MetricSpace γ]
    {Φ : X → γ} {Ψ : Y → γ} (ha : Isometry Φ) (hb : Isometry Ψ) :
    ghDist X Y ≤ hausdorffDist (range Φ) (range Ψ) := by
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  let s : Set γ := range Φ ∪ range Ψ
  let Φ' : X → Subtype s := fun y => ⟨Φ y, mem_union_left _ (mem_range_self _)⟩
  let Ψ' : Y → Subtype s := fun y => ⟨Ψ y, mem_union_right _ (mem_range_self _)⟩
  have IΦ' : Isometry Φ' := fun x y => ha x y
  have IΨ' : Isometry Ψ' := fun x y => hb x y
  have : IsCompact s := (isCompact_range ha.continuous).union (isCompact_range hb.continuous)
  letI : MetricSpace (Subtype s) := by infer_instance
  haveI : CompactSpace (Subtype s) := ⟨isCompact_iff_isCompact_univ.1 ‹IsCompact s›⟩
  haveI : Nonempty (Subtype s) := ⟨Φ' xX⟩
  have ΦΦ' : Φ = Subtype.val ∘ Φ' := by funext; rfl
  have ΨΨ' : Ψ = Subtype.val ∘ Ψ' := by funext; rfl
  have : hausdorffDist (range Φ) (range Ψ) = hausdorffDist (range Φ') (range Ψ') := by
    rw [ΦΦ', ΨΨ', range_comp, range_comp]
    exact hausdorffDist_image isometry_subtype_coe
  rw [this]
  let F := kuratowskiEmbedding (Subtype s)
  have : hausdorffDist (F '' range Φ') (F '' range Ψ') = hausdorffDist (range Φ') (range Ψ') :=
    hausdorffDist_image (kuratowskiEmbedding.isometry _)
  rw [← this]
  let A : NonemptyCompacts ℓ_infty_ℝ :=
    ⟨⟨F '' range Φ',
        (isCompact_range IΦ'.continuous).image (kuratowskiEmbedding.isometry _).continuous⟩,
      (range_nonempty _).image _⟩
  let B : NonemptyCompacts ℓ_infty_ℝ :=
    ⟨⟨F '' range Ψ',
        (isCompact_range IΨ'.continuous).image (kuratowskiEmbedding.isometry _).continuous⟩,
      (range_nonempty _).image _⟩
  have AX : ⟦A⟧ = toGHSpace X := by
    rw [eq_toGHSpace_iff]
    exact ⟨fun x => F (Φ' x), (kuratowskiEmbedding.isometry _).comp IΦ', range_comp _ _⟩
  have BY : ⟦B⟧ = toGHSpace Y := by
    rw [eq_toGHSpace_iff]
    exact ⟨fun x => F (Ψ' x), (kuratowskiEmbedding.isometry _).comp IΨ', range_comp _ _⟩
  refine csInf_le ⟨0, ?_⟩ ?_
  · simp only [lowerBounds, mem_image, mem_prod, mem_setOf_eq, Prod.exists, and_imp,
      forall_exists_index]
    intro t _ _ _ _ ht
    rw [← ht]
    exact hausdorffDist_nonneg
  apply (mem_image _ _ _).2
  exists (⟨A, B⟩ : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ)
theorem hausdorffDist_optimal {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) = ghDist X Y := by
  inhabit X; inhabit Y
  have A :
    ∀ p q : NonemptyCompacts ℓ_infty_ℝ,
      ⟦p⟧ = toGHSpace X →
        ⟦q⟧ = toGHSpace Y →
          hausdorffDist (p : Set ℓ_infty_ℝ) q < diam (univ : Set X) + 1 + diam (univ : Set Y) →
            hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
              hausdorffDist (p : Set ℓ_infty_ℝ) q := by
    intro p q hp hq bound
    rcases eq_toGHSpace_iff.1 hp with ⟨Φ, ⟨Φisom, Φrange⟩⟩
    rcases eq_toGHSpace_iff.1 hq with ⟨Ψ, ⟨Ψisom, Ψrange⟩⟩
    have I : diam (range Φ ∪ range Ψ) ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by
      rcases exists_mem_of_nonempty X with ⟨xX, _⟩
      have : ∃ y ∈ range Ψ, dist (Φ xX) y < diam (univ : Set X) + 1 + diam (univ : Set Y) := by
        rw [Ψrange]
        have : Φ xX ∈ (p : Set _) := Φrange ▸ (mem_range_self _)
        exact
          exists_dist_lt_of_hausdorffDist_lt this bound
            (hausdorffEdist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty
              p.isCompact.isBounded q.isCompact.isBounded)
      rcases this with ⟨y, hy, dy⟩
      rcases mem_range.1 hy with ⟨z, hzy⟩
      rw [← hzy] at dy
      have DΦ : diam (range Φ) = diam (univ : Set X) := Φisom.diam_range
      have DΨ : diam (range Ψ) = diam (univ : Set Y) := Ψisom.diam_range
      calc
        diam (range Φ ∪ range Ψ) ≤ diam (range Φ) + dist (Φ xX) (Ψ z) + diam (range Ψ) :=
          diam_union (mem_range_self _) (mem_range_self _)
        _ ≤
            diam (univ : Set X) + (diam (univ : Set X) + 1 + diam (univ : Set Y)) +
              diam (univ : Set Y) := by
          rw [DΦ, DΨ]
          gcongr
        _ = 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by ring
    let f : X ⊕ Y → ℓ_infty_ℝ := fun x =>
      match x with
      | inl y => Φ y
      | inr z => Ψ z
    let F : (X ⊕ Y) × (X ⊕ Y) → ℝ := fun p => dist (f p.1) (f p.2)
    have Fgood : F ∈ candidates X Y := by
      simp only [F, candidates, forall_const, add_comm, eq_self_iff_true,
        dist_eq_zero, and_self_iff, Set.mem_setOf_eq]
      repeat' constructor
      · exact fun x y =>
          calc
            F (inl x, inl y) = dist (Φ x) (Φ y) := rfl
            _ = dist x y := Φisom.dist_eq x y
      · exact fun x y =>
          calc
            F (inr x, inr y) = dist (Ψ x) (Ψ y) := rfl
            _ = dist x y := Ψisom.dist_eq x y
      · exact fun x y => dist_comm _ _
      · exact fun x y z => dist_triangle _ _ _
      · exact fun x y =>
          calc
            F (x, y) ≤ diam (range Φ ∪ range Ψ) := by
              have A : ∀ z : X ⊕ Y, f z ∈ range Φ ∪ range Ψ := by
                intro z
                cases z
                · apply mem_union_left; apply mem_range_self
                · apply mem_union_right; apply mem_range_self
              refine dist_le_diam_of_mem ?_ (A _) (A _)
              rw [Φrange, Ψrange]
              exact (p ⊔ q).isCompact.isBounded
            _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := I
    let Fb := candidatesBOfCandidates F Fgood
    have : hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤ HD Fb :=
      hausdorffDist_optimal_le_HD _ _ (candidatesBOfCandidates_mem F Fgood)
    refine le_trans this (le_of_forall_le_of_dense fun r hr => ?_)
    have I1 : ∀ x : X, (⨅ y, Fb (inl x, inr y)) ≤ r := by
      intro x
      have : f (inl x) ∈ (p : Set _) := Φrange ▸ (mem_range_self _)
      rcases exists_dist_lt_of_hausdorffDist_lt this hr
          (hausdorffEdist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty p.isCompact.isBounded
            q.isCompact.isBounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Ψ := by rwa [← Ψrange] at zq
      rcases mem_range.1 this with ⟨y, hy⟩
      calc
        (⨅ y, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          ciInf_le (by simpa only [add_zero] using HD_below_aux1 0) y
        _ = dist (Φ x) (Ψ y) := rfl
        _ = dist (f (inl x)) z := by rw [hy]
        _ ≤ r := le_of_lt hz
    have I2 : ∀ y : Y, (⨅ x, Fb (inl x, inr y)) ≤ r := by
      intro y
      have : f (inr y) ∈ (q : Set _) := Ψrange ▸ (mem_range_self _)
      rcases exists_dist_lt_of_hausdorffDist_lt' this hr
          (hausdorffEdist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty p.isCompact.isBounded
            q.isCompact.isBounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Φ := by rwa [← Φrange] at zq
      rcases mem_range.1 this with ⟨x, hx⟩
      calc
        (⨅ x, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          ciInf_le (by simpa only [add_zero] using HD_below_aux2 0) x
        _ = dist (Φ x) (Ψ y) := rfl
        _ = dist z (f (inr y)) := by rw [hx]
        _ ≤ r := le_of_lt hz
    simp only [HD, ciSup_le I1, ciSup_le I2, max_le_iff, and_self_iff]
  have B :
    ∀ p q : NonemptyCompacts ℓ_infty_ℝ,
      ⟦p⟧ = toGHSpace X →
        ⟦q⟧ = toGHSpace Y →
          hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
            hausdorffDist (p : Set ℓ_infty_ℝ) q := by
    intro p q hp hq
    by_cases h :
      hausdorffDist (p : Set ℓ_infty_ℝ) q < diam (univ : Set X) + 1 + diam (univ : Set Y)
    · exact A p q hp hq h
    · calc
        hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
            HD (candidatesBDist X Y) :=
          hausdorffDist_optimal_le_HD _ _ candidatesBDist_mem_candidatesB
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := HD_candidatesBDist_le
        _ ≤ hausdorffDist (p : Set ℓ_infty_ℝ) q := not_lt.1 h
  refine le_antisymm ?_ ?_
  · apply le_csInf
    · refine (Set.Nonempty.prod ?_ ?_).image _ <;> exact ⟨_, rfl⟩
    · rintro b ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
      exact B p q hp hq
  · exact ghDist_le_hausdorffDist (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y)
theorem ghDist_eq_hausdorffDist (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Y : Type v) [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    ∃ Φ : X → ℓ_infty_ℝ,
      ∃ Ψ : Y → ℓ_infty_ℝ,
        Isometry Φ ∧ Isometry Ψ ∧ ghDist X Y = hausdorffDist (range Φ) (range Ψ) := by
  let F := kuratowskiEmbedding (OptimalGHCoupling X Y)
  let Φ := F ∘ optimalGHInjl X Y
  let Ψ := F ∘ optimalGHInjr X Y
  refine ⟨Φ, Ψ, ?_, ?_, ?_⟩
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjl X Y)
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjr X Y)
  · rw [← image_univ, ← image_univ, image_comp F, image_univ, image_comp F (optimalGHInjr X Y),
      image_univ, ← hausdorffDist_optimal]
    exact (hausdorffDist_image (kuratowskiEmbedding.isometry _)).symm
instance : MetricSpace GHSpace where
  dist := dist
  dist_self x := by
    rcases exists_rep x with ⟨y, hy⟩
    refine le_antisymm ?_ ?_
    · apply csInf_le
      · exact ⟨0, by rintro b ⟨⟨u, v⟩, -, rfl⟩; exact hausdorffDist_nonneg⟩
      · simp only [mem_image, mem_prod, mem_setOf_eq, Prod.exists]
        exists y, y
        simpa only [and_self_iff, hausdorffDist_self_zero, eq_self_iff_true, and_true]
    · apply le_csInf
      · exact Set.Nonempty.image _ <| Set.Nonempty.prod ⟨y, hy⟩ ⟨y, hy⟩
      · rintro b ⟨⟨u, v⟩, -, rfl⟩; exact hausdorffDist_nonneg
  dist_comm x y := by
    have A :
      (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
            hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) ''
          { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y } =
        (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
              hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) ∘
            Prod.swap ''
          { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y } := by
      funext
      simp only [comp_apply, Prod.fst_swap, Prod.snd_swap]
      congr
      simp (config := { singlePass := true }) only [hausdorffDist_comm]
    simp only [dist, A, image_comp, image_swap_prod]
  eq_of_dist_eq_zero {x} {y} hxy := by
    rcases ghDist_eq_hausdorffDist x.Rep y.Rep with ⟨Φ, Ψ, Φisom, Ψisom, DΦΨ⟩
    rw [← dist_ghDist] at DΦΨ
    simp_rw [hxy] at DΦΨ 
    have : range Φ = range Ψ := by
      have hΦ : IsCompact (range Φ) := isCompact_range Φisom.continuous
      have hΨ : IsCompact (range Ψ) := isCompact_range Ψisom.continuous
      apply (IsClosed.hausdorffDist_zero_iff_eq _ _ _).1 DΦΨ.symm
      · exact hΦ.isClosed
      · exact hΨ.isClosed
      · exact hausdorffEdist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
          hΦ.isBounded hΨ.isBounded
    have T : (range Ψ ≃ᵢ y.Rep) = (range Φ ≃ᵢ y.Rep) := by rw [this]
    have eΨ := cast T Ψisom.isometryEquivOnRange.symm
    have e := Φisom.isometryEquivOnRange.trans eΨ
    rw [← x.toGHSpace_rep, ← y.toGHSpace_rep, toGHSpace_eq_toGHSpace_iff_isometryEquiv]
    exact ⟨e⟩
  dist_triangle x y z := by
    let X := x.Rep
    let Y := y.Rep
    let Z := z.Rep
    let γ1 := OptimalGHCoupling X Y
    let γ2 := OptimalGHCoupling Y Z
    let Φ : Y → γ1 := optimalGHInjr X Y
    have hΦ : Isometry Φ := isometry_optimalGHInjr X Y
    let Ψ : Y → γ2 := optimalGHInjl Y Z
    have hΨ : Isometry Ψ := isometry_optimalGHInjl Y Z
    have Comm : toGlueL hΦ hΨ ∘ optimalGHInjr X Y = toGlueR hΦ hΨ ∘ optimalGHInjl Y Z :=
      toGlue_commute hΦ hΨ
    calc
      dist x z = dist (toGHSpace X) (toGHSpace Z) := by
        rw [x.toGHSpace_rep, z.toGHSpace_rep]
      _ ≤ hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjl X Y))
            (range (toGlueR hΦ hΨ ∘ optimalGHInjr Y Z)) :=
        (ghDist_le_hausdorffDist ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjl X Y))
          ((toGlueR_isometry hΦ hΨ).comp (isometry_optimalGHInjr Y Z)))
      _ ≤ hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjl X Y))
              (range (toGlueL hΦ hΨ ∘ optimalGHInjr X Y)) +
            hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjr X Y))
              (range (toGlueR hΦ hΨ ∘ optimalGHInjr Y Z)) := by
        refine hausdorffDist_triangle <| hausdorffEdist_ne_top_of_nonempty_of_bounded
          (range_nonempty _) (range_nonempty _) ?_ ?_
        · exact (isCompact_range (Isometry.continuous
            ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjl X Y)))).isBounded
        · exact (isCompact_range (Isometry.continuous
            ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjr X Y)))).isBounded
      _ = hausdorffDist (toGlueL hΦ hΨ '' range (optimalGHInjl X Y))
              (toGlueL hΦ hΨ '' range (optimalGHInjr X Y)) +
            hausdorffDist (toGlueR hΦ hΨ '' range (optimalGHInjl Y Z))
              (toGlueR hΦ hΨ '' range (optimalGHInjr Y Z)) := by
        simp only [← range_comp, Comm, eq_self_iff_true, add_right_inj]
      _ = hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) +
            hausdorffDist (range (optimalGHInjl Y Z)) (range (optimalGHInjr Y Z)) := by
        rw [hausdorffDist_image (toGlueL_isometry hΦ hΨ),
          hausdorffDist_image (toGlueR_isometry hΦ hΨ)]
      _ = dist (toGHSpace X) (toGHSpace Y) + dist (toGHSpace Y) (toGHSpace Z) := by
        rw [hausdorffDist_optimal, hausdorffDist_optimal, ghDist, ghDist]
      _ = dist x y + dist y z := by rw [x.toGHSpace_rep, y.toGHSpace_rep, z.toGHSpace_rep]
end GHSpace
end GromovHausdorff
def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X]
    (p : NonemptyCompacts X) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p
open TopologicalSpace
namespace GromovHausdorff
section NonemptyCompacts
variable {X : Type u} [MetricSpace X]
theorem ghDist_le_nonemptyCompacts_dist (p q : NonemptyCompacts X) :
    dist p.toGHSpace q.toGHSpace ≤ dist p q := by
  have ha : Isometry ((↑) : p → X) := isometry_subtype_coe
  have hb : Isometry ((↑) : q → X) := isometry_subtype_coe
  have A : dist p q = hausdorffDist (p : Set X) q := rfl
  have I : ↑p = range ((↑) : p → X) := Subtype.range_coe_subtype.symm
  have J : ↑q = range ((↑) : q → X) := Subtype.range_coe_subtype.symm
  rw [A, I, J]
  exact ghDist_le_hausdorffDist ha hb
theorem toGHSpace_lipschitz :
    LipschitzWith 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  LipschitzWith.mk_one ghDist_le_nonemptyCompacts_dist
theorem toGHSpace_continuous :
    Continuous (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  toGHSpace_lipschitz.continuous
end NonemptyCompacts
section
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]
theorem ghDist_le_of_approx_subsets {s : Set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ}
    (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁) (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
    (H : ∀ x y : s, |dist x y - dist (Φ x) (Φ y)| ≤ ε₂) : ghDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ := by
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  rcases hs xX with ⟨xs, hxs, Dxs⟩
  have sne : s.Nonempty := ⟨xs, hxs⟩
  letI : Nonempty s := sne.to_subtype
  have : 0 ≤ ε₂ := le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)
  have : ∀ p q : s, |dist p q - dist (Φ p) (Φ q)| ≤ 2 * (ε₂ / 2 + δ) := fun p q =>
    calc
      |dist p q - dist (Φ p) (Φ q)| ≤ ε₂ := H p q
      _ ≤ 2 * (ε₂ / 2 + δ) := by linarith
  letI : MetricSpace (X ⊕ Y) :=
    glueMetricApprox (fun x : s => (x : X)) (fun x => Φ x) (ε₂ / 2 + δ) (by linarith) this
  let Fl := @Sum.inl X Y
  let Fr := @Sum.inr X Y
  have Il : Isometry Fl := Isometry.of_dist_eq fun x y => rfl
  have Ir : Isometry Fr := Isometry.of_dist_eq fun x y => rfl
  have : ghDist X Y ≤ hausdorffDist (range Fl) (range Fr) := ghDist_le_hausdorffDist Il Ir
  have :
    hausdorffDist (range Fl) (range Fr) ≤
      hausdorffDist (range Fl) (Fl '' s) + hausdorffDist (Fl '' s) (range Fr) :=
    have B : IsBounded (range Fl) := (isCompact_range Il.continuous).isBounded
    hausdorffDist_triangle
      (hausdorffEdist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B
        (B.subset (image_subset_range _ _)))
  have :
    hausdorffDist (Fl '' s) (range Fr) ≤
      hausdorffDist (Fl '' s) (Fr '' range Φ) + hausdorffDist (Fr '' range Φ) (range Fr) :=
    have B : IsBounded (range Fr) := (isCompact_range Ir.continuous).isBounded
    hausdorffDist_triangle'
      (hausdorffEdist_ne_top_of_nonempty_of_bounded ((range_nonempty _).image _) (range_nonempty _)
        (B.subset (image_subset_range _ _)) B)
  have : hausdorffDist (range Fl) (Fl '' s) ≤ ε₁ := by
    rw [← image_univ, hausdorffDist_image Il]
    have : 0 ≤ ε₁ := le_trans dist_nonneg Dxs
    refine hausdorffDist_le_of_mem_dist this (fun x _ => hs x) fun x _ =>
      ⟨x, mem_univ _, by simpa only [dist_self]⟩
  have : hausdorffDist (Fl '' s) (Fr '' range Φ) ≤ ε₂ / 2 + δ := by
    refine hausdorffDist_le_of_mem_dist (by linarith) ?_ ?_
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩
      rw [← xx']
      use Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)
      exact le_of_eq (glueDist_glued_points (fun x : s => (x : X)) Φ (ε₂ / 2 + δ) ⟨x, x_in_s⟩)
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩
      use Fl x, mem_image_of_mem _ x.2
      rw [← yx', ← xy, dist_comm]
      exact le_of_eq (glueDist_glued_points (Z := s) (@Subtype.val X s) Φ (ε₂ / 2 + δ) x)
  have : hausdorffDist (Fr '' range Φ) (range Fr) ≤ ε₃ := by
    rw [← @image_univ _ _ Fr, hausdorffDist_image Ir]
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩
    rcases hs' xY with ⟨xs', Dxs'⟩
    have : 0 ≤ ε₃ := le_trans dist_nonneg Dxs'
    refine hausdorffDist_le_of_mem_dist this
      (fun x _ => ⟨x, mem_univ _, by simpa only [dist_self]⟩)
      fun x _ => ?_
    rcases hs' x with ⟨y, Dy⟩
    exact ⟨Φ y, mem_range_self _, Dy⟩
  linarith
end
instance : SecondCountableTopology GHSpace := by
  refine secondCountable_of_countable_discretization fun δ δpos => ?_
  let ε := 2 / 5 * δ
  have εpos : 0 < ε := mul_pos (by norm_num) δpos
  have : ∀ p : GHSpace, ∃ s : Set p.Rep, s.Finite ∧ univ ⊆ ⋃ x ∈ s, ball x ε := fun p => by
    simpa only [subset_univ, true_and] using
      finite_cover_balls_of_compact (α := p.Rep) isCompact_univ εpos
  choose s hs using this
  have : ∀ p : GHSpace, ∀ t : Set p.Rep, t.Finite → ∃ n : ℕ, ∃ _ : Equiv t (Fin n), True := by
    intro p t ht
    letI : Fintype t := Finite.fintype ht
    exact ⟨Fintype.card t, Fintype.equivFin t, trivial⟩
  choose N e _ using this
  let N := fun p : GHSpace => N p (s p) (hs p).1
  let E := fun p : GHSpace => e p (s p) (hs p).1
  let F : GHSpace → Σ n : ℕ, Fin n → Fin n → ℤ := fun p =>
    ⟨N p, fun a b => ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋⟩
  refine ⟨Σ n, Fin n → Fin n → ℤ, by infer_instance, F, fun p q hpq => ?_⟩
  have Npq : N p = N q := (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.Rep := fun x => Ψ x
  have main : ghDist p.Rep q.Rep ≤ ε + ε / 2 + ε := by
    refine ghDist_le_of_approx_subsets Φ ?_ ?_ ?_
    · show ∀ x : p.Rep, ∃ y ∈ s p, dist x y ≤ ε
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y ε := (hs p).2 (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_of_lt hy⟩
    · show ∀ x : q.Rep, ∃ z : s p, dist x (Φ z) ≤ ε
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y ε := (hs q).2 (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).is_lt
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.val_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]; exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by simp only [Φ, Ψ]; rw [C1, C2, C3]
      rw [this]
      exact le_of_lt hy
    · show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
      intro x y
      rw [show dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) from rfl]
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [Ψ, Equiv.apply_symm_apply, Fin.coe_cast]
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = ((E q) (Ψ y)).1 := by
        simp only [Ψ, Equiv.apply_symm_apply, Fin.coe_cast]
      have : (F p).2 ((E p) x) ((E p) y) = ⌊ε⁻¹ * dist x y⌋ := by
        simp only [(E p).symm_apply_apply]
      have Ap : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = ⌊ε⁻¹ * dist x y⌋ := by rw [← this]
      have : (F q).2 ((E q) (Ψ x)) ((E q) (Ψ y)) = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        simp only [(E q).symm_apply_apply]
      have Aq : (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        rw [← this]
        refine congr_arg₂ (F q).2 ?_ ?_ <;> ext1
        exacts [i', j']
      have : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ := by
        have hpq' : HEq (F p).snd (F q).snd := (Sigma.mk.inj_iff.1 hpq).2
        rw [Fin.heq_fun₂_iff Npq Npq] at hpq'
        rw [← hpq']
      rw [Ap, Aq] at this
      have I :=
        calc
          |ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| :=
            (abs_mul _ _).symm
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| := by congr; ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
      calc
        |dist x y - dist (Ψ x) (Ψ y)| = ε * ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| := by
          rw [mul_inv_cancel₀ (ne_of_gt εpos), one_mul]
        _ = ε * (|ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)|) := by
          rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        _ = ε := mul_one _
  calc
    dist p q = ghDist p.Rep q.Rep := dist_ghDist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ := by ring
theorem totallyBounded {t : Set GHSpace} {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (ulim : Tendsto u atTop (𝓝 0)) (hdiam : ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C)
    (hcov : ∀ p ∈ t, ∀ n : ℕ, ∃ s : Set (GHSpace.Rep p),
      (#s) ≤ K n ∧ univ ⊆ ⋃ x ∈ s, ball x (u n)) :
    TotallyBounded t := by
  refine Metric.totallyBounded_of_finite_discretization fun δ δpos => ?_
  let ε := 1 / 5 * δ
  have εpos : 0 < ε := mul_pos (by norm_num) δpos
  rcases Metric.tendsto_atTop.1 ulim ε εpos with ⟨n, hn⟩
  have u_le_ε : u n ≤ ε := by
    have := hn n le_rfl
    simp only [Real.dist_eq, add_zero, sub_eq_add_neg, neg_zero] at this
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
  have :
    ∀ p : GHSpace,
      ∃ s : Set p.Rep, ∃ N ≤ K n, ∃ _ : Equiv s (Fin N), p ∈ t → univ ⊆ ⋃ x ∈ s, ball x (u n) := by
    intro p
    by_cases hp : p ∉ t
    · have : Nonempty (Equiv (∅ : Set p.Rep) (Fin 0)) := by
        rw [← Fintype.card_eq]
        simp only [empty_card', Fintype.card_fin]
      use ∅, 0, bot_le, this.some
      exact fun hp' => (hp hp').elim
    · rcases hcov _ (Set.not_not_mem.1 hp) n with ⟨s, ⟨scard, scover⟩⟩
      rcases Cardinal.lt_aleph0.1 (lt_of_le_of_lt scard (Cardinal.nat_lt_aleph0 _)) with ⟨N, hN⟩
      rw [hN, Nat.cast_le] at scard
      have : #s = #(Fin N) := by rw [hN, Cardinal.mk_fin]
      cases' Quotient.exact this with E
      use s, N, scard, E
      simp only [scover, imp_true_iff]
  choose s N hN E hs using this
  let M := ⌊ε⁻¹ * max C 0⌋₊
  let F : GHSpace → Σ k : Fin (K n).succ, Fin k → Fin k → Fin M.succ := fun p =>
    ⟨⟨N p, lt_of_le_of_lt (hN p) (Nat.lt_succ_self _)⟩, fun a b =>
      ⟨min M ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋₊,
        (min_le_left _ _).trans_lt (Nat.lt_succ_self _)⟩⟩
  refine ⟨_, ?_, fun p => F p, ?_⟩
  · infer_instance
  rintro ⟨p, pt⟩ ⟨q, qt⟩ hpq
  have Npq : N p = N q := Fin.ext_iff.1 (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.Rep := fun x => Ψ x
  have main : ghDist p.Rep q.Rep ≤ ε + ε / 2 + ε := by
    refine ghDist_le_of_approx_subsets Φ ?_ ?_ ?_
    · show ∀ x : p.Rep, ∃ y ∈ s p, dist x y ≤ ε
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y (u n) := (hs p pt) (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_trans (le_of_lt hy) u_le_ε⟩
    · show ∀ x : q.Rep, ∃ z : s p, dist x (Φ z) ≤ ε
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y (u n) := (hs q qt) (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).2
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.val_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]; exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by simp only [Ψ, Φ]; rw [C1, C2, C3]
      rw [this]
      exact le_trans (le_of_lt hy) u_le_ε
    · show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
      intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [Ψ, Equiv.apply_symm_apply, Fin.coe_cast]
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = (E q) (Ψ y) := by simp only [Ψ, Equiv.apply_symm_apply, Fin.coe_cast]
      have Ap : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ⌊ε⁻¹ * dist x y⌋₊ :=
        calc
          ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F p).2 ((E p) x) ((E p) y)).1 := by
            congr
          _ = min M ⌊ε⁻¹ * dist x y⌋₊ := by simp only [(E p).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist x y⌋₊ := by
            refine min_eq_right (Nat.floor_mono ?_)
            refine mul_le_mul_of_nonneg_left (le_trans ?_ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (x : p.Rep) y ≤ C
            refine (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans ?_
            exact hdiam p pt
      have Aq : ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ :=
        calc
          ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ((F q).2 ((E q) (Ψ x)) ((E q) (Ψ y))).1 := by
            exact congr_arg₂ (Fin.val <| (F q).2 · ·) (Fin.ext i') (Fin.ext j')
          _ = min M ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by simp only [(E q).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by
            refine min_eq_right (Nat.floor_mono ?_)
            refine mul_le_mul_of_nonneg_left (le_trans ?_ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (Ψ x : q.Rep) (Ψ y) ≤ C
            refine (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans ?_
            exact hdiam q qt
      have : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 := by
        have hpq' : HEq (F p).snd (F q).snd := (Sigma.mk.inj_iff.1 hpq).2
        rw [Fin.heq_fun₂_iff Npq Npq] at hpq'
        rw [← hpq']
      have : ⌊ε⁻¹ * dist x y⌋ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        rw [Ap, Aq] at this
        have D : 0 ≤ ⌊ε⁻¹ * dist x y⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        have D' : 0 ≤ ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        rw [← Int.toNat_of_nonneg D, ← Int.toNat_of_nonneg D', Int.floor_toNat, Int.floor_toNat,
          this]
      have I :=
        calc
          |ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| :=
            (abs_mul _ _).symm
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| := by congr; ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
      calc
        |dist x y - dist (Ψ x) (Ψ y)| = ε * ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| := by
          rw [mul_inv_cancel₀ (ne_of_gt εpos), one_mul]
        _ = ε * (|ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)|) := by
          rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        _ = ε := mul_one _
  calc
    dist p q = ghDist p.Rep q.Rep := dist_ghDist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ / 2 := by simp only [ε, one_div]; ring
    _ < δ := half_lt_self δpos
section Complete
variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]
structure AuxGluingStruct (A : Type) [MetricSpace A] : Type 1 where
  Space : Type
  metric : MetricSpace Space
  embed : A → Space
  isom : Isometry embed
attribute [local instance] AuxGluingStruct.metric
instance (A : Type) [MetricSpace A] : Inhabited (AuxGluingStruct A) :=
  ⟨{  Space := A
      metric := by infer_instance
      embed := id
      isom := fun x y => by exact rfl }⟩
def auxGluing (n : ℕ) : AuxGluingStruct (X n) :=
  Nat.recOn n default fun n Y =>
    { Space := GlueSpace Y.isom (isometry_optimalGHInjl (X n) (X (n + 1)))
      metric := by infer_instance
      embed :=
        toGlueR Y.isom (isometry_optimalGHInjl (X n) (X (n + 1))) ∘ optimalGHInjr (X n) (X (n + 1))
      isom := (toGlueR_isometry _ _).comp (isometry_optimalGHInjr (X n) (X (n + 1))) }
instance : CompleteSpace GHSpace := by
  set d := fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n
  have : ∀ n : ℕ, 0 < d n := fun _ ↦ by positivity
  refine Metric.complete_of_convergent_controlled_sequences d this fun u hu => ?_
  let X n := (u n).Rep
  let Y := auxGluing X
  have E :
    ∀ n : ℕ,
      GlueSpace (Y n).isom (isometry_optimalGHInjl (X n) (X (n + 1))) = (Y (n + 1)).Space :=
    fun n => by dsimp only [Y, auxGluing]
  let c n := cast (E n)
  have ic : ∀ n, Isometry (c n) := fun n x y => by dsimp only [Y, auxGluing]; exact rfl
  let f : ∀ n, (Y n).Space → (Y (n + 1)).Space := fun n =>
    c n ∘ toGlueL (Y n).isom (isometry_optimalGHInjl (X n) (X n.succ))
  have I : ∀ n, Isometry (f n) := fun n => (ic n).comp (toGlueL_isometry _ _)
  let Z0 := Metric.InductiveLimit I
  let Z := UniformSpace.Completion Z0
  let Φ := toInductiveLimit I
  let coeZ := ((↑) : Z0 → Z)
  let X2 n := range (coeZ ∘ Φ n ∘ (Y n).embed)
  have isom : ∀ n, Isometry (coeZ ∘ Φ n ∘ (Y n).embed) := by
    intro n
    refine UniformSpace.Completion.coe_isometry.comp ?_
    exact (toInductiveLimit_isometry _ _).comp (Y n).isom
  have X2n : ∀ n, X2 n =
    range ((coeZ ∘ Φ n.succ ∘ c n ∘ toGlueR (Y n).isom
      (isometry_optimalGHInjl (X n) (X n.succ))) ∘ optimalGHInjl (X n) (X n.succ)) := by
    intro n
    change X2 n = range (coeZ ∘ Φ n.succ ∘ c n ∘
      toGlueR (Y n).isom (isometry_optimalGHInjl (X n) (X n.succ)) ∘
      optimalGHInjl (X n) (X n.succ))
    simp only [X2, Φ]
    rw [← toInductiveLimit_commute I]
    simp only [f]
    rw [← toGlue_commute]
    rfl
  have X2nsucc : ∀ n, X2 n.succ =
      range ((coeZ ∘ Φ n.succ ∘ c n ∘ toGlueR (Y n).isom
        (isometry_optimalGHInjl (X n) (X n.succ))) ∘ optimalGHInjr (X n) (X n.succ)) := by
    intro n
    rfl
  have D2 : ∀ n, hausdorffDist (X2 n) (X2 n.succ) < d n := fun n ↦ by
    rw [X2n n, X2nsucc n, range_comp, range_comp, hausdorffDist_image,
      hausdorffDist_optimal, ← dist_ghDist]
    · exact hu n n n.succ (le_refl n) (le_succ n)
    · apply UniformSpace.Completion.coe_isometry.comp _
      exact (toInductiveLimit_isometry _ _).comp ((ic n).comp (toGlueR_isometry _ _))
  let X3 : ℕ → NonemptyCompacts Z := fun n =>
    ⟨⟨X2 n, isCompact_range (isom n).continuous⟩, range_nonempty _⟩
  have : CauchySeq X3 := by
    refine cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => ?_
    rw [one_mul]
    exact le_of_lt (D2 n)
  rcases cauchySeq_tendsto_of_complete this with ⟨L, hL⟩
  have : ∀ n, (NonemptyCompacts.toGHSpace ∘ X3) n = u n := by
    intro n
    rw [Function.comp_apply, NonemptyCompacts.toGHSpace, ← (u n).toGHSpace_rep,
      toGHSpace_eq_toGHSpace_iff_isometryEquiv]
    constructor
    convert (isom n).isometryEquivOnRange.symm
  use L.toGHSpace
  apply Filter.Tendsto.congr this
  refine Tendsto.comp ?_ hL
  apply toGHSpace_continuous.tendsto
end Complete
end GromovHausdorff