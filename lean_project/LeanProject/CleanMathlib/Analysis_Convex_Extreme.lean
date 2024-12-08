import Mathlib.Analysis.Convex.Hull
open Function Set
open scoped Classical
open Affine
variable {𝕜 E F ι : Type*} {π : ι → Type*}
section SMul
variable (𝕜) [OrderedSemiring 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
def IsExtreme (A B : Set E) : Prop :=
  B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ openSegment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
def Set.extremePoints (A : Set E) : Set E :=
  { x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x }
@[refl]
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨Subset.rfl, fun _ hx₁A _ hx₂A _ _ _ ↦ ⟨hx₁A, hx₂A⟩⟩
variable {𝕜} {A B C : Set E} {x : E}
protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A
@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
    IsExtreme 𝕜 A C := by
  refine ⟨Subset.trans hBC.1 hAB.1, fun x₁ hx₁A x₂ hx₂A x hxC hx ↦ ?_⟩
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A (hBC.1 hxC) hx
  exact hBC.2 hx₁B hx₂B hxC hx
protected theorem IsExtreme.antisymm : AntiSymmetric (IsExtreme 𝕜 : Set E → Set E → Prop) :=
  fun _ _ hAB hBA ↦ Subset.antisymm hBA.1 hAB.1
instance : IsPartialOrder (Set E) (IsExtreme 𝕜) where
  refl := IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  antisymm := IsExtreme.antisymm
theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) :
    IsExtreme 𝕜 A (B ∩ C) := by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A hxB hx
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 hx₁A hx₂A hxC hx
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩
protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
    IsExtreme 𝕜 B C :=
  ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx ↦ hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩
theorem isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι → Set E}
    (hAF : ∀ i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i) := by
  obtain i := Classical.arbitrary ι
  refine ⟨iInter_subset_of_subset i (hAF i).1, fun x₁ hx₁A x₂ hx₂A x hxF hx ↦ ?_⟩
  simp_rw [mem_iInter] at hxF ⊢
  have h := fun i ↦ (hAF i).2 hx₁A hx₂A (hxF i) hx
  exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩
theorem isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂ B ∈ F, B) := by
  haveI := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F ↦ hA _ i.2
theorem isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : ∀ B ∈ F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂₀ F) := by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF
theorem mem_extremePoints : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x :=
  Iff.rfl
@[simp] lemma isExtreme_singleton : IsExtreme 𝕜 A {x} ↔ x ∈ A.extremePoints 𝕜 := by
  refine ⟨fun hx ↦ ⟨singleton_subset_iff.1 hx.1, fun x₁ hx₁ x₂ hx₂ ↦ hx.2 hx₁ hx₂ rfl⟩, ?_⟩
  rintro ⟨hxA, hAx⟩
  use singleton_subset_iff.2 hxA
  rintro x₁ hx₁A x₂ hx₂A y (rfl : y = x)
  exact hAx hx₁A hx₂A
alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton
theorem extremePoints_subset : A.extremePoints 𝕜 ⊆ A :=
  fun _ hx ↦ hx.1
@[simp]
theorem extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extremePoints_subset
@[simp]
theorem extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x} :=
  extremePoints_subset.antisymm <|
    singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ hx₂ _ ↦ ⟨hx₁, hx₂⟩⟩
theorem inter_extremePoints_subset_extremePoints_of_subset (hBA : B ⊆ A) :
    B ∩ A.extremePoints 𝕜 ⊆ B.extremePoints 𝕜 :=
  fun _ ⟨hxB, hxA⟩ ↦ ⟨hxB, fun _ hx₁ _ hx₂ hx ↦ hxA.2 (hBA hx₁) (hBA hx₂) hx⟩
theorem IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 ⊆ A.extremePoints 𝕜 :=
  fun _ ↦ by simpa only [← isExtreme_singleton] using hAB.trans
theorem IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 = B ∩ A.extremePoints 𝕜 :=
  Subset.antisymm (fun _ hx ↦ ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)
end SMul
section OrderedSemiring
variable [OrderedSemiring 𝕜] [AddCommGroup E] [AddCommGroup F] [∀ i, AddCommGroup (π i)]
  [Module 𝕜 E] [Module 𝕜 F] [∀ i, Module 𝕜 (π i)] {A B : Set E}
theorem IsExtreme.convex_diff (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) : Convex 𝕜 (A \ B) :=
  convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx ↦
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB ↦ hx₁B (hAB.2 hx₁A hx₂A hxB hx).1⟩
@[simp]
theorem extremePoints_prod (s : Set E) (t : Set F) :
    (s ×ˢ t).extremePoints 𝕜 = s.extremePoints 𝕜 ×ˢ t.extremePoints 𝕜 := by
  ext
  refine (and_congr_right fun hx ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩).trans and_and_and_comm
  constructor
  · rintro x₁ hx₁ x₂ hx₂ hx_fst
    refine (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) ?_).imp (congr_arg Prod.fst)
        (congr_arg Prod.fst)
    rw [← Prod.image_mk_openSegment_left]
    exact ⟨_, hx_fst, rfl⟩
  · rintro x₁ hx₁ x₂ hx₂ hx_snd
    refine (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) ?_).imp (congr_arg Prod.snd)
        (congr_arg Prod.snd)
    rw [← Prod.image_mk_openSegment_right]
    exact ⟨_, hx_snd, rfl⟩
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    simp_rw [Prod.ext_iff]
    exact and_and_and_comm.1
        ⟨h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congr_arg Prod.fst hx'⟩,
          h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congr_arg Prod.snd hx'⟩⟩
@[simp]
theorem extremePoints_pi (s : ∀ i, Set (π i)) :
    (univ.pi s).extremePoints 𝕜 = univ.pi fun i ↦ (s i).extremePoints 𝕜 := by
  ext x
  simp only [mem_extremePoints, mem_pi, mem_univ, true_imp_iff, @forall_and ι]
  refine and_congr_right fun hx ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    refine (h (update x i x₁) ?_ (update x i x₂) ?_ ?_).imp (fun h₁ ↦ by rw [← h₁, update_same])
        fun h₂ ↦ by rw [← h₂, update_same]
    iterate 2
      rintro j
      obtain rfl | hji := eq_or_ne j i
      · rwa [update_same]
      · rw [update_noteq hji]
        exact hx _
    rw [← Pi.image_update_openSegment]
    exact ⟨_, hi, update_eq_self _ _⟩
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    simp_rw [funext_iff, ← forall_and]
    exact fun i ↦ h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, congr_fun hx' _⟩
end OrderedSemiring
section OrderedRing
variable {L : Type*} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [EquivLike L E F] [LinearEquivClass L 𝕜 E F]
lemma image_extremePoints (f : L) (s : Set E) :
    f '' extremePoints 𝕜 s = extremePoints 𝕜 (f '' s) := by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : ∀ x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_image, (EquivLike.injective f).eq_iff, ← this]
end OrderedRing
section LinearOrderedRing
variable [LinearOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [DenselyOrdered 𝕜] [NoZeroSMulDivisors 𝕜 E] {A : Set E} {x : E}
theorem mem_extremePoints_iff_forall_segment : x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ᵉ (x₁ ∈ A) (x₂ ∈ A), x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x₂ = x := by
  refine and_congr_right fun hxA ↦ forall₄_congr fun x₁ h₁ x₂ h₂ ↦ ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ _ hx) with (rfl | rfl)
    exacts [⟨rfl, (left_mem_openSegment_iff.1 hx).symm⟩, ⟨right_mem_openSegment_iff.1 hx, rfl⟩]
theorem Convex.mem_extremePoints_iff_convex_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A ∧ Convex 𝕜 (A \ {x}) := by
  use fun hx ↦ ⟨hx.1, (isExtreme_singleton.2 hx).convex_diff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx ↦ ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ ↦ h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, fun hx₂ ↦ h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl
theorem Convex.mem_extremePoints_iff_mem_diff_convexHull_diff (hA : Convex 𝕜 A) :
    x ∈ A.extremePoints 𝕜 ↔ x ∈ A \ convexHull 𝕜 (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_convex_diff, hA.convex_remove_iff_not_mem_convexHull_remove,
    mem_diff]
theorem extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 ⊆ A := by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_diff] at hx
  by_contra h
  exact (convexHull_min (subset_diff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl
end LinearOrderedRing