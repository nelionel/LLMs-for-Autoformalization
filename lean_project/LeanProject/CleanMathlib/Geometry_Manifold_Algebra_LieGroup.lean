import Mathlib.Geometry.Manifold.Algebra.Monoid
noncomputable section
open scoped Manifold
class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothAdd I G : Prop where
  smooth_neg : ContMDiff I I ⊤ fun a : G => -a
@[to_additive]
class LieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothMul I G : Prop where
  smooth_inv : ContMDiff I I ⊤ fun a : G => a⁻¹
section PointwiseDivision
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {n : ℕ∞}
section
variable (I)
@[to_additive "In an additive Lie group, inversion is a smooth map."]
theorem contMDiff_inv : ContMDiff I I ⊤ fun x : G => x⁻¹ :=
  LieGroup.smooth_inv
@[deprecated (since := "2024-11-21")] alias smooth_inv := contMDiff_inv
@[deprecated (since := "2024-11-21")] alias smooth_neg := contMDiff_neg
include I in
@[to_additive "An additive Lie group is an additive topological group. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]."]
theorem topologicalGroup_of_lieGroup : TopologicalGroup G :=
  { continuousMul_of_smooth I with continuous_inv := (contMDiff_inv I).continuous }
end
@[to_additive]
theorem ContMDiffWithinAt.inv {f : M → G} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt I' I n f s x₀) : ContMDiffWithinAt I' I n (fun x => (f x)⁻¹) s x₀ :=
  ((contMDiff_inv I).of_le le_top).contMDiffAt.contMDiffWithinAt.comp x₀ hf <| Set.mapsTo_univ _ _
@[to_additive]
theorem ContMDiffAt.inv {f : M → G} {x₀ : M} (hf : ContMDiffAt I' I n f x₀) :
    ContMDiffAt I' I n (fun x => (f x)⁻¹) x₀ :=
  ((contMDiff_inv I).of_le le_top).contMDiffAt.comp x₀ hf
@[to_additive]
theorem ContMDiffOn.inv {f : M → G} {s : Set M} (hf : ContMDiffOn I' I n f s) :
    ContMDiffOn I' I n (fun x => (f x)⁻¹) s := fun x hx => (hf x hx).inv
@[to_additive]
theorem ContMDiff.inv {f : M → G} (hf : ContMDiff I' I n f) : ContMDiff I' I n fun x => (f x)⁻¹ :=
  fun x => (hf x).inv
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.inv := ContMDiffWithinAt.inv
@[deprecated (since := "2024-11-21")] alias SmoothAt.inv := ContMDiffAt.inv
@[deprecated (since := "2024-11-21")] alias SmoothOn.inv := ContMDiffOn.inv
@[deprecated (since := "2024-11-21")] alias Smooth.inv := ContMDiff.inv
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.neg := ContMDiffWithinAt.neg
@[deprecated (since := "2024-11-21")] alias SmoothAt.neg := ContMDiffAt.neg
@[deprecated (since := "2024-11-21")] alias SmoothOn.neg := ContMDiffOn.neg
@[deprecated (since := "2024-11-21")] alias Smooth.neg := ContMDiff.neg
@[to_additive]
theorem ContMDiffWithinAt.div {f g : M → G} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt I' I n f s x₀) (hg : ContMDiffWithinAt I' I n g s x₀) :
    ContMDiffWithinAt I' I n (fun x => f x / g x) s x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
@[to_additive]
theorem ContMDiffAt.div {f g : M → G} {x₀ : M} (hf : ContMDiffAt I' I n f x₀)
    (hg : ContMDiffAt I' I n g x₀) : ContMDiffAt I' I n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
@[to_additive]
theorem ContMDiffOn.div {f g : M → G} {s : Set M} (hf : ContMDiffOn I' I n f s)
    (hg : ContMDiffOn I' I n g s) : ContMDiffOn I' I n (fun x => f x / g x) s := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
@[to_additive]
theorem ContMDiff.div {f g : M → G} (hf : ContMDiff I' I n f) (hg : ContMDiff I' I n g) :
    ContMDiff I' I n fun x => f x / g x := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.div := ContMDiffWithinAt.div
@[deprecated (since := "2024-11-21")] alias SmoothAt.div := ContMDiffAt.div
@[deprecated (since := "2024-11-21")] alias SmoothOn.div := ContMDiffOn.div
@[deprecated (since := "2024-11-21")] alias Smooth.div := ContMDiff.div
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.sub := ContMDiffWithinAt.sub
@[deprecated (since := "2024-11-21")] alias SmoothAt.sub := ContMDiffAt.sub
@[deprecated (since := "2024-11-21")] alias SmoothOn.sub := ContMDiffOn.sub
@[deprecated (since := "2024-11-21")] alias Smooth.sub := ContMDiff.sub
end PointwiseDivision
section Product
@[to_additive]
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
    [Group G'] [LieGroup I' G'] : LieGroup (I.prod I') (G × G') :=
  { SmoothMul.prod _ _ _ _ with smooth_inv := contMDiff_fst.inv.prod_mk contMDiff_snd.inv }
end Product
instance normedSpaceLieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) E where
  smooth_neg := contDiff_neg.contMDiff
section SmoothInv₀
class SmoothInv₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Inv G] [Zero G] [TopologicalSpace G] [ChartedSpace H G] : Prop where
  smoothAt_inv₀ : ∀ ⦃x : G⦄, x ≠ 0 → ContMDiffAt I I ⊤ (fun y ↦ y⁻¹) x
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] : SmoothInv₀ 𝓘(𝕜) 𝕜 where
  smoothAt_inv₀ x hx := by
    change ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) ⊤ Inv.inv x
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_inv 𝕜 hx
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Inv G] [Zero G] [SmoothInv₀ I G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {n : ℕ∞} {f : M → G}
theorem contMDiffAt_inv₀ {x : G} (hx : x ≠ 0) : ContMDiffAt I I ⊤ (fun y ↦ y⁻¹) x :=
  SmoothInv₀.smoothAt_inv₀ hx
@[deprecated (since := "2024-11-21")] alias smoothAt_inv₀ := contMDiffAt_inv₀
include I in
theorem hasContinuousInv₀_of_hasSmoothInv₀ : HasContinuousInv₀ G :=
  { continuousAt_inv₀ := fun _ hx ↦ (contMDiffAt_inv₀ I hx).continuousAt }
theorem contMDiffOn_inv₀ : ContMDiffOn I I ⊤ (Inv.inv : G → G) {0}ᶜ := fun _x hx =>
  (contMDiffAt_inv₀ I hx).contMDiffWithinAt
@[deprecated (since := "2024-11-21")] alias smoothOn_inv₀ := contMDiffOn_inv₀
@[deprecated (since := "2024-11-21")] alias SmoothOn_inv₀ := contMDiffOn_inv₀
variable {I} {s : Set M} {a : M}
theorem ContMDiffWithinAt.inv₀ (hf : ContMDiffWithinAt I' I n f s a) (ha : f a ≠ 0) :
    ContMDiffWithinAt I' I n (fun x => (f x)⁻¹) s a :=
  ((contMDiffAt_inv₀ I ha).of_le le_top).comp_contMDiffWithinAt a hf
theorem ContMDiffAt.inv₀ (hf : ContMDiffAt I' I n f a) (ha : f a ≠ 0) :
    ContMDiffAt I' I n (fun x ↦ (f x)⁻¹) a :=
  ((contMDiffAt_inv₀ I ha).of_le le_top).comp a hf
theorem ContMDiff.inv₀ (hf : ContMDiff I' I n f) (h0 : ∀ x, f x ≠ 0) :
    ContMDiff I' I n (fun x ↦ (f x)⁻¹) :=
  fun x ↦ ContMDiffAt.inv₀ (hf x) (h0 x)
theorem ContMDiffOn.inv₀ (hf : ContMDiffOn I' I n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContMDiffOn I' I n (fun x => (f x)⁻¹) s :=
  fun x hx ↦ ContMDiffWithinAt.inv₀ (hf x hx) (h0 x hx)
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.inv₀ := ContMDiffWithinAt.inv₀
@[deprecated (since := "2024-11-21")] alias SmoothAt.inv₀ := ContMDiffAt.inv₀
@[deprecated (since := "2024-11-21")] alias SmoothOn.inv₀ := ContMDiffOn.inv₀
@[deprecated (since := "2024-11-21")] alias Smooth.inv₀ := ContMDiff.inv₀
end SmoothInv₀
section Div
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [GroupWithZero G] [SmoothInv₀ I G] [SmoothMul I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f g : M → G} {s : Set M} {a : M} {n : ℕ∞}
theorem ContMDiffWithinAt.div₀
    (hf : ContMDiffWithinAt I' I n f s a) (hg : ContMDiffWithinAt I' I n g s a) (h₀ : g a ≠ 0) :
    ContMDiffWithinAt I' I n (f / g) s a := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)
theorem ContMDiffOn.div₀ (hf : ContMDiffOn I' I n f s) (hg : ContMDiffOn I' I n g s)
    (h₀ : ∀ x ∈ s, g x ≠ 0) : ContMDiffOn I' I n (f / g) s := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)
theorem ContMDiffAt.div₀ (hf : ContMDiffAt I' I n f a) (hg : ContMDiffAt I' I n g a)
    (h₀ : g a ≠ 0) : ContMDiffAt I' I n (f / g) a := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)
theorem ContMDiff.div₀ (hf : ContMDiff I' I n f) (hg : ContMDiff I' I n g) (h₀ : ∀ x, g x ≠ 0) :
    ContMDiff I' I n (f / g) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)
@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.div₀ := ContMDiffWithinAt.div₀
@[deprecated (since := "2024-11-21")] alias SmoothAt.div₀ := ContMDiffAt.div₀
@[deprecated (since := "2024-11-21")] alias SmoothOn.div₀ := ContMDiffOn.div₀
@[deprecated (since := "2024-11-21")] alias Smooth.div₀ := ContMDiff.div₀
end Div