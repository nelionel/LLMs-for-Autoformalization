import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Group.Basic
open scoped Topology Pointwise
open MulAction Set Function
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  [Group G] [TopologicalGroup G] [MulAction G X]
  [SigmaCompactSpace G] [BaireSpace X] [T2Space X]
  [ContinuousSMul G X] [IsPretransitive G X]
@[to_additive "Consider a sigma-compact additive group acting continuously and transitively on a
Baire space. Then the orbit map is open around zero. It follows in
`isOpenMap_vadd_of_sigmaCompact` that it is open around any point."]
theorem smul_singleton_mem_nhds_of_sigmaCompact
    {U : Set G} (hU : U ∈ 𝓝 1) (x : X) : U • {x} ∈ 𝓝 x := by
  obtain ⟨V, V_mem, V_closed, V_symm, VU⟩ : ∃ V ∈ 𝓝 (1 : G), IsClosed V ∧ V⁻¹ = V ∧ V * V ⊆ U :=
    exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, s_count, hs⟩ : ∃ (s : Set G), s.Countable ∧ ⋃ g ∈ s, g • V = univ :=
    countable_cover_nhds_of_sigmaCompact fun _ ↦ by simpa
  let K : ℕ → Set G := compactCovering G
  let F : ℕ × s → Set X := fun p ↦ (K p.1 ∩ (p.2 : G) • V) • ({x} : Set X)
  obtain ⟨⟨n, ⟨g, hg⟩⟩, hi⟩ : ∃ i, (interior (F i)).Nonempty := by
    have : Nonempty X := ⟨x⟩
    have : Encodable s := Countable.toEncodable s_count
    apply nonempty_interior_of_iUnion_of_closed
    · rintro ⟨n, ⟨g, hg⟩⟩
      apply IsCompact.isClosed
      suffices H : IsCompact ((fun (g : G) ↦ g • x) '' (K n ∩ g • V)) by
        simpa only [F, smul_singleton] using H
      apply IsCompact.image
      · exact (isCompact_compactCovering G n).inter_right (V_closed.smul g)
      · exact continuous_id.smul continuous_const
    · apply eq_univ_iff_forall.2 (fun y ↦ ?_)
      obtain ⟨h, rfl⟩ : ∃ h, h • x = y := exists_smul_eq G x y
      obtain ⟨n, hn⟩ : ∃ n, h ∈ K n := exists_mem_compactCovering h
      obtain ⟨g, gs, hg⟩ : ∃ g ∈ s, h ∈ g • V := exists_set_mem_of_union_eq_top s _ hs _
      simp only [F, smul_singleton, mem_iUnion, mem_image, mem_inter_iff, Prod.exists,
        Subtype.exists, exists_prop]
      exact ⟨n, g, gs, h, ⟨hn, hg⟩, rfl⟩
  have I : (interior ((g • V) • {x})).Nonempty := by
    apply hi.mono
    apply interior_mono
    exact smul_subset_smul_right inter_subset_right
  obtain ⟨y, hy⟩ : (interior (V • ({x} : Set X))).Nonempty := by
    rw [smul_assoc, interior_smul] at I
    exact smul_set_nonempty.1 I
  obtain ⟨g', hg', rfl⟩ : ∃ g' ∈ V, g' • x = y := by simpa using interior_subset hy
  have J : (g' ⁻¹ • V) • {x} ∈ 𝓝 x := by
    apply mem_interior_iff_mem_nhds.1
    rwa [smul_assoc, interior_smul, mem_inv_smul_set_iff]
  have : (g'⁻¹ • V) • {x} ⊆ U • ({x} : Set X) := by
    apply smul_subset_smul_right
    apply Subset.trans (smul_set_subset_smul (inv_mem_inv.2 hg')) ?_
    rw [V_symm]
    exact VU
  exact Filter.mem_of_superset J this
@[to_additive "Consider a sigma-compact additive group acting continuously and transitively on a
Baire space. Then the orbit map is open. This is a version of the open mapping theorem, valid
notably for the action of a sigma-compact locally compact group on a locally compact space."]
theorem isOpenMap_smul_of_sigmaCompact (x : X) : IsOpenMap (fun (g : G) ↦ g • x) := by
  simp_rw [isOpenMap_iff_nhds_le, Filter.le_map_iff]
  intro g U hU
  have : (· • x) = (· • (g • x)) ∘ (· * g⁻¹) := by
    ext g
    simp [smul_smul]
  rw [this, image_comp, ← smul_singleton]
  apply smul_singleton_mem_nhds_of_sigmaCompact
  simpa using isOpenMap_mul_right g⁻¹ |>.image_mem_nhds hU
@[to_additive]
theorem MonoidHom.isOpenMap_of_sigmaCompact
    {H : Type*} [Group H] [TopologicalSpace H] [BaireSpace H] [T2Space H] [ContinuousMul H]
    (f : G →* H) (hf : Function.Surjective f) (h'f : Continuous f) :
    IsOpenMap f := by
  let A : MulAction G H := MulAction.compHom _ f
  have : ContinuousSMul G H := continuousSMul_compHom h'f
  have : IsPretransitive G H := isPretransitive_compHom hf
  have : f = (fun (g : G) ↦ g • (1 : H)) := by simp [MulAction.compHom_smul_def]
  rw [this]
  exact isOpenMap_smul_of_sigmaCompact _