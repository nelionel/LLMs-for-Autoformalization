import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.Perm.Support
open Equiv List MulAction Pointwise Set Subgroup
variable {G α : Type*} [Group G] [MulAction G α]
theorem finite_compl_fixedBy_closure_iff {S : Set G} :
    (∀ g ∈ closure S, (fixedBy α g)ᶜ.Finite) ↔ ∀ g ∈ S, (fixedBy α g)ᶜ.Finite :=
  ⟨fun h g hg ↦ h g (subset_closure hg), fun h g hg ↦ by
    refine closure_induction h (by simp) (fun g g' _ _ hg hg' ↦ (hg.union hg').subset ?_)
      (by simp) hg
    simp_rw [← compl_inter, compl_subset_compl, fixedBy_mul]⟩
theorem exists_smul_not_mem_of_subset_orbit_closure (S : Set G) (T : Set α) {a : α}
    (hS : ∀ g ∈ S, g⁻¹ ∈ S) (subset : T ⊆ orbit (closure S) a) (not_mem : a ∉ T)
    (nonempty : T.Nonempty) : ∃ σ ∈ S, ∃ a ∈ T, σ • a ∉ T := by
  have key0 : ¬ closure S ≤ stabilizer G T := by
    have ⟨b, hb⟩ := nonempty
    obtain ⟨σ, rfl⟩ := subset hb
    contrapose! not_mem with h
    exact smul_mem_smul_set_iff.mp ((h σ.2).symm ▸ hb)
  contrapose! key0
  refine (closure_le _).mpr fun σ hσ ↦ ?_
  simp_rw [SetLike.mem_coe, mem_stabilizer_iff, Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact fun a ↦ ⟨fun h ↦ smul_inv_smul σ a ▸ key0 σ hσ (σ⁻¹ • a) h, key0 σ⁻¹ (hS σ hσ) a⟩
variable [DecidableEq α]
theorem finite_compl_fixedBy_swap {x y : α} : (fixedBy α (swap x y))ᶜ.Finite :=
  Set.Finite.subset (s := {x, y}) (by simp)
    (compl_subset_comm.mp fun z h ↦ by apply swap_apply_of_ne_of_ne <;> rintro rfl <;> simp at h)
theorem Equiv.Perm.IsSwap.finite_compl_fixedBy {σ : Perm α} (h : σ.IsSwap) :
    (fixedBy α σ)ᶜ.Finite := by
  obtain ⟨x, y, -, rfl⟩ := h
  exact finite_compl_fixedBy_swap
theorem SubmonoidClass.swap_mem_trans {a b c : α} {C} [SetLike C (Perm α)]
    [SubmonoidClass C (Perm α)] (M : C) (hab : swap a b ∈ M) (hbc : swap b c ∈ M) :
    swap a c ∈ M := by
  obtain rfl | hab' := eq_or_ne a b
  · exact hbc
  obtain rfl | hac := eq_or_ne a c
  · exact swap_self a ▸ one_mem M
  rw [swap_comm, ← swap_mul_swap_mul_swap hab' hac]
  exact mul_mem (mul_mem hbc hab) hbc
theorem swap_mem_closure_isSwap {S : Set (Perm α)} (hS : ∀ f ∈ S, f.IsSwap) {x y : α} :
    swap x y ∈ closure S ↔ x ∈ orbit (closure S) y := by
  refine ⟨fun h ↦ ⟨⟨swap x y, h⟩, swap_apply_right x y⟩, fun hf ↦ ?_⟩
  by_contra h
  have := exists_smul_not_mem_of_subset_orbit_closure S {x | swap x y ∈ closure S}
    (fun f hf ↦ ?_) (fun z hz ↦ ?_) h ⟨y, ?_⟩
  · obtain ⟨σ, hσ, a, ha, hσa⟩ := this
    obtain ⟨z, w, hzw, rfl⟩ := hS σ hσ
    have := ne_of_mem_of_not_mem ha hσa
    rw [Perm.smul_def, ne_comm, swap_apply_ne_self_iff, and_iff_right hzw] at this
    refine hσa (SubmonoidClass.swap_mem_trans (closure S) ?_ ha)
    obtain rfl | rfl := this <;> simpa [swap_comm] using subset_closure hσ
  · obtain ⟨x, y, -, rfl⟩ := hS f hf; rwa [swap_inv]
  · exact orbit_eq_iff.mpr hf ▸ ⟨⟨swap z y, hz⟩, swap_apply_right z y⟩
  · rw [mem_setOf, swap_self]; apply one_mem
theorem mem_closure_isSwap {S : Set (Perm α)} (hS : ∀ f ∈ S, f.IsSwap) {f : Perm α} :
    f ∈ closure S ↔ (fixedBy α f)ᶜ.Finite ∧ ∀ x, f x ∈ orbit (closure S) x := by
  refine ⟨fun hf ↦ ⟨?_, fun x ↦ mem_orbit_iff.mpr ⟨⟨f, hf⟩, rfl⟩⟩, ?_⟩
  · exact finite_compl_fixedBy_closure_iff.mpr (fun f hf ↦ (hS f hf).finite_compl_fixedBy) _ hf
  rintro ⟨fin, hf⟩
  set supp := (fixedBy α f)ᶜ with supp_eq
  suffices h : (fixedBy α f)ᶜ ⊆ supp → f ∈ closure S from h supp_eq.symm.subset
  clear_value supp; clear supp_eq; revert f
  apply fin.induction_on ..
  · rintro f - emp; convert (closure S).one_mem; ext; by_contra h; exact emp h
  rintro a s - - ih f hf supp_subset
  refine (mul_mem_cancel_left ((swap_mem_closure_isSwap hS).2 (hf a))).1
    (ih (fun b ↦ ?_) fun b hb ↦ ?_)
  · rw [Perm.mul_apply, swap_apply_def]; split_ifs with h1 h2
    · rw [← orbit_eq_iff.mpr (hf b), h1, orbit_eq_iff.mpr (hf a)]; apply mem_orbit_self
    · rw [← orbit_eq_iff.mpr (hf b), h2]; apply hf
    · exact hf b
  · contrapose! hb
    simp_rw [not_mem_compl_iff, mem_fixedBy, Perm.smul_def, Perm.mul_apply, swap_apply_def,
      apply_eq_iff_eq]
    by_cases hb' : f b = b
    · rw [hb']; split_ifs with h <;> simp only [h]
    simp [show b = a by simpa [hb] using supp_subset hb']
theorem mem_closure_isSwap' {f : Perm α} :
    f ∈ closure {σ : Perm α | σ.IsSwap} ↔ (fixedBy α f)ᶜ.Finite := by
  refine (mem_closure_isSwap fun _ ↦ id).trans
    (and_iff_left fun x ↦ ⟨⟨swap x (f x), ?_⟩, swap_apply_left x (f x)⟩)
  by_cases h : x = f x
  · rw [← h, swap_self]
    apply Subgroup.one_mem
  · exact subset_closure ⟨x, f x, h, rfl⟩
theorem closure_of_isSwap_of_isPretransitive [Finite α] {S : Set (Perm α)} (hS : ∀ σ ∈ S, σ.IsSwap)
    [MulAction.IsPretransitive (Subgroup.closure S) α] : Subgroup.closure S = ⊤ := by
  simp [eq_top_iff', mem_closure_isSwap hS, orbit_eq_univ, Set.toFinite]
theorem surjective_of_isSwap_of_isPretransitive [Finite α] (S : Set G)
    (hS1 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom G α σ)) (hS2 : Subgroup.closure S = ⊤)
    [h : MulAction.IsPretransitive G α] : Function.Surjective (MulAction.toPermHom G α) := by
  rw [← MonoidHom.range_eq_top]
  have := MulAction.IsPretransitive.of_compHom (α := α) (MulAction.toPermHom G α).rangeRestrict
  rw [MonoidHom.range_eq_map, ← hS2, MonoidHom.map_closure] at this ⊢
  exact closure_of_isSwap_of_isPretransitive (Set.forall_mem_image.2 hS1)