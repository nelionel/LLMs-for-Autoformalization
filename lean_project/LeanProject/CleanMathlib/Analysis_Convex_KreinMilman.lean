import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Algebra.ContinuousAffineMap
open Set
open scoped Classical
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T1Space F]
theorem IsCompact.extremePoints_nonempty (hscomp : IsCompact s) (hsnemp : s.Nonempty) :
    (s.extremePoints ℝ).Nonempty := by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme ℝ s t }
  rsuffices ⟨t, ht⟩ : ∃ t, Minimal (· ∈ S) t
  · obtain ⟨⟨x,hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_contra hyx
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx
    obtain ⟨z, hzt, hz⟩ :=
      (hscomp.of_isClosed_subset htclos hst.1).exists_isMaxOn ⟨x, hxt⟩
        l.continuous.continuousOn
    have h : IsExposed ℝ t ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }) := fun _ => ⟨l, rfl⟩
    rw [ ht.eq_of_ge (y := ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }))
      ⟨⟨z, hzt, hz⟩, h.isClosed htclos, hst.trans h.isExtreme⟩ (t.sep_subset _)] at hyB
    exact hl.not_le (hyB.2 x hxt)
  refine zorn_superset _ fun F hFS hF => ?_
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  · exact ⟨s, ⟨hsnemp, hscomp.isClosed, IsExtreme.rfl⟩, fun _ => False.elim⟩
  refine ⟨⋂₀ F, ⟨?_, isClosed_sInter fun t ht => (hFS ht).2.1,
    isExtreme_sInter hFnemp fun t ht => (hFS ht).2.2⟩, fun t ht => sInter_subset_of_mem ht⟩
  haveI : Nonempty (↥F) := hFnemp.to_subtype
  rw [sInter_eq_iInter]
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun t u => ?_)
    (fun t => (hFS t.mem).1)
    (fun t => hscomp.of_isClosed_subset (hFS t.mem).2.1 (hFS t.mem).2.2.1) fun t =>
      (hFS t.mem).2.1
  obtain htu | hut := hF.total t.mem u.mem
  exacts [⟨t, Subset.rfl, htu⟩, ⟨u, hut, Subset.rfl⟩]
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed ℝ s ({ y ∈ s | ∀ z ∈ s, l z ≤ l y }) := fun _ => ⟨l, rfl⟩
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_isMaxOn ⟨x, hxA⟩ l.continuous.continuousOn
  obtain ⟨y, hy⟩ := (h.isCompact hscomp).extremePoints_nonempty ⟨z, hzA, hz⟩
  linarith [hlr _ (subset_closure <| subset_convexHull _ _ <|
    h.isExtreme.extremePoints_subset_extremePoints hy), hy.1.2 x hxA]
lemma surjOn_extremePoints_image (f : E →ᴬ[ℝ] F) (hs : IsCompact s) :
    SurjOn f (extremePoints ℝ s) (extremePoints ℝ (f '' s)) := by
  rintro w hw
  have ht : IsCompact {x ∈ s | f x = w} :=
    hs.inter_right <| isClosed_singleton.preimage f.continuous
  have ht₀ : {x ∈ s | f x = w}.Nonempty := by simpa using extremePoints_subset hw
  obtain ⟨x, ⟨hx, rfl⟩, hyt⟩ := ht.extremePoints_nonempty ht₀
  refine mem_image_of_mem _ ⟨hx, fun y hy z hz hxyz ↦ ?_⟩
  have := by simpa using image_openSegment _ f.toAffineMap y z
  have := hw.2 (mem_image_of_mem _ hy) (mem_image_of_mem _ hz) <| by
    rw [← this]; exact mem_image_of_mem _ hxyz
  exact hyt ⟨hy, this.1⟩ ⟨hz, this.2⟩ hxyz