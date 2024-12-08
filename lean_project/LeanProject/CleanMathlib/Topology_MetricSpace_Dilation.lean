import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.FunLike.Basic
noncomputable section
open Bornology Function Set Topology
open scoped ENNReal NNReal
section Defs
variable (α : Type*) (β : Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
structure Dilation where
  toFun : α → β
  edist_eq' : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (toFun x) (toFun y) = r * edist x y
infixl:25 " →ᵈ " => Dilation
class DilationClass (F : Type*) (α β : outParam Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [FunLike F α β] : Prop where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (f x) (f y) = r * edist x y
end Defs
namespace Dilation
variable {α : Type*} {β : Type*} {γ : Type*} {F : Type*}
section Setup
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]
instance funLike : FunLike (α →ᵈ β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
instance toDilationClass : DilationClass (α →ᵈ β) α β where
  edist_eq' f := edist_eq' f
@[simp]
theorem toFun_eq_coe {f : α →ᵈ β} : f.toFun = (f : α → β) :=
  rfl
@[simp]
theorem coe_mk (f : α → β) (h) : ⇑(⟨f, h⟩ : α →ᵈ β) = f :=
  rfl
protected theorem congr_fun {f g : α →ᵈ β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
protected theorem congr_arg (f : α →ᵈ β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
@[ext]
theorem ext {f g : α →ᵈ β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
@[simp]
theorem mk_coe (f : α →ᵈ β) (h) : Dilation.mk f h = f :=
  ext fun _ => rfl
@[simps (config := .asFn)]
protected def copy (f : α →ᵈ β) (f' : α → β) (h : f' = ⇑f) : α →ᵈ β where
  toFun := f'
  edist_eq' := h.symm ▸ f.edist_eq'
theorem copy_eq_self (f : α →ᵈ β) {f' : α → β} (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
variable [FunLike F α β]
open Classical in
def ratio [DilationClass F α β] (f : F) : ℝ≥0 :=
  if ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose
theorem ratio_of_trivial [DilationClass F α β] (f : F)
    (h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1 :=
  if_pos h
@[nontriviality]
theorem ratio_of_subsingleton [Subsingleton α] [DilationClass F α β] (f : F) : ratio f = 1 :=
  if_pos fun x y ↦ by simp [Subsingleton.elim x y]
theorem ratio_ne_zero [DilationClass F α β] (f : F) : ratio f ≠ 0 := by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1
theorem ratio_pos [DilationClass F α β] (f : F) : 0 < ratio f :=
  (ratio_ne_zero f).bot_lt
@[simp]
theorem edist_eq [DilationClass F α β] (f : F) (x y : α) :
    edist (f x) (f y) = ratio f * edist x y := by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    cases' key x y with h h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y
@[simp]
theorem nndist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    nndist (f x) (f y) = ratio f * nndist x y := by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]
@[simp]
theorem dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    dist (f x) (f y) = ratio f * dist x y := by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]
theorem ratio_unique [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (h₀ : edist x y ≠ 0)
    (htop : edist x y ≠ ⊤) (hr : edist (f x) (f y) = r * edist x y) : r = ratio f := by
  simpa only [hr, ENNReal.mul_eq_mul_right h₀ htop, ENNReal.coe_inj] using edist_eq f x y
theorem ratio_unique_of_nndist_ne_zero {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : nndist x y ≠ 0)
    (hr : nndist (f x) (f y) = r * nndist x y) : r = ratio f :=
  ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])
theorem ratio_unique_of_dist_ne_zero {α β} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : dist x y ≠ 0)
    (hr : dist (f x) (f y) = r * dist x y) : r = ratio f :=
  ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy) <|
    NNReal.eq <| by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]
def mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, nndist (f x) (f y) = r * nndist x y) : α →ᵈ β where
  toFun := f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, h x y]
@[simp]
theorem coe_mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfNNDistEq f h : α →ᵈ β) = f :=
  rfl
@[simp]
theorem mk_coe_of_nndist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β)
    (h) : Dilation.mkOfNNDistEq f h = f :=
  ext fun _ => rfl
def mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, dist (f x) (f y) = r * dist x y) : α →ᵈ β :=
  mkOfNNDistEq f <|
    h.imp fun r hr =>
      ⟨hr.1, fun x y => NNReal.eq <| by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩
@[simp]
theorem coe_mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfDistEq f h : α →ᵈ β) = f :=
  rfl
@[simp]
theorem mk_coe_of_dist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β) (h) :
    Dilation.mkOfDistEq f h = f :=
  ext fun _ => rfl
end Setup
section PseudoEmetricDilation
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable [FunLike F α β] [DilationClass F α β]
variable (f : F)
@[simps]
def _root_.Isometry.toDilation (f : α → β) (hf : Isometry f) : α →ᵈ β where
  toFun := f
  edist_eq' := ⟨1, one_ne_zero, by simpa using hf⟩
@[simp]
lemma _root_.Isometry.toDilation_ratio {f : α → β} {hf : Isometry f} : ratio hf.toDilation = 1 := by
  by_cases h : ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · push_neg at h
    obtain ⟨x, y, h₁, h₂⟩ := h
    exact ratio_unique h₁ h₂ (by simp [hf x y]) |>.symm
theorem lipschitz : LipschitzWith (ratio f) (f : α → β) := fun x y => (edist_eq f x y).le
theorem antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f : α → β) := fun x y => by
  have hr : ratio f ≠ 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge
protected theorem injective {α : Type*} [EMetricSpace α] [FunLike F α β]  [DilationClass F α β]
    (f : F) :
    Injective f :=
  (antilipschitz f).injective
protected def id (α) [PseudoEMetricSpace α] : α →ᵈ α where
  toFun := id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩
instance : Inhabited (α →ᵈ α) :=
  ⟨Dilation.id α⟩
@[simp]
protected theorem coe_id : ⇑(Dilation.id α) = id :=
  rfl
theorem ratio_id : ratio (Dilation.id α) = 1 := by
  by_cases h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, if_pos h]
  · push_neg at h
    rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp
def comp (g : β →ᵈ γ) (f : α →ᵈ β) : α →ᵈ γ where
  toFun := g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩
theorem comp_assoc {δ : Type*} [PseudoEMetricSpace δ] (f : α →ᵈ β) (g : β →ᵈ γ)
    (h : γ →ᵈ δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
@[simp]
theorem coe_comp (g : β →ᵈ γ) (f : α →ᵈ β) : (g.comp f : α → γ) = g ∘ f :=
  rfl
theorem comp_apply (g : β →ᵈ γ) (f : α →ᵈ β) (x : α) : (g.comp f : α → γ) x = g (f x) :=
  rfl
theorem ratio_comp' {g : β →ᵈ γ} {f : α →ᵈ β}
    (hne : ∃ x y : α, edist x y ≠ 0 ∧ edist x y ≠ ⊤) : ratio (g.comp f) = ratio g * ratio f := by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_eq_mul_right hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]
@[simp]
theorem comp_id (f : α →ᵈ β) : f.comp (Dilation.id α) = f :=
  ext fun _ => rfl
@[simp]
theorem id_comp (f : α →ᵈ β) : (Dilation.id β).comp f = f :=
  ext fun _ => rfl
instance : Monoid (α →ᵈ α) where
  one := Dilation.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
theorem one_def : (1 : α →ᵈ α) = Dilation.id α :=
  rfl
theorem mul_def (f g : α →ᵈ α) : f * g = f.comp g :=
  rfl
@[simp]
theorem coe_one : ⇑(1 : α →ᵈ α) = id :=
  rfl
@[simp]
theorem coe_mul (f g : α →ᵈ α) : ⇑(f * g) = f ∘ g :=
  rfl
@[simp] theorem ratio_one : ratio (1 : α →ᵈ α) = 1 := ratio_id
@[simp]
theorem ratio_mul (f g : α →ᵈ α) : ratio (f * g) = ratio f * ratio g := by
  by_cases h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  push_neg at h
  exact ratio_comp' h
@[simps]
def ratioHom : (α →ᵈ α) →* ℝ≥0 := ⟨⟨ratio, ratio_one⟩, ratio_mul⟩
@[simp]
theorem ratio_pow (f : α →ᵈ α) (n : ℕ) : ratio (f ^ n) = ratio f ^ n :=
  ratioHom.map_pow _ _
@[simp]
theorem cancel_right {g₁ g₂ : β →ᵈ γ} {f : α →ᵈ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => Dilation.ext <| hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩
@[simp]
theorem cancel_left {g : β →ᵈ γ} {f₁ f₂ : α →ᵈ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => Dilation.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩
theorem isUniformInducing : IsUniformInducing (f : α → β) :=
  (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous
@[deprecated (since := "2024-10-05")]
alias uniformInducing := isUniformInducing
theorem tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : Filter ι} {b : α} :
    Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto ((f : α → β) ∘ g) a (𝓝 (f b)) :=
  (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff
theorem toContinuous : Continuous (f : α → β) :=
  (lipschitz f).continuous
theorem ediam_image (s : Set α) : EMetric.diam ((f : α → β) '' s) = ratio f * EMetric.diam s := by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv, mul_comm, ← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]
theorem ediam_range : EMetric.diam (range (f : α → β)) = ratio f * EMetric.diam (univ : Set α) := by
  rw [← image_univ]; exact ediam_image f univ
theorem mapsTo_emetric_ball (x : α) (r : ℝ≥0∞) :
    MapsTo (f : α → β) (EMetric.ball x r) (EMetric.ball (f x) (ratio f * r)) :=
  fun y hy => (edist_eq f y x).trans_lt <|
    (ENNReal.mul_lt_mul_left (ENNReal.coe_ne_zero.2 <| ratio_ne_zero f) ENNReal.coe_ne_top).2 hy
theorem mapsTo_emetric_closedBall (x : α) (r' : ℝ≥0∞) :
    MapsTo (f : α → β) (EMetric.closedBall x r') (EMetric.closedBall (f x) (ratio f * r')) :=
  fun y hy => (edist_eq f y x).trans_le <| mul_le_mul_left' (by exact hy) _
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] {g : γ → α} {s : Set γ} :
    ContinuousOn ((f : α → β) ∘ g) s ↔ ContinuousOn g s :=
  (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm
theorem comp_continuous_iff {γ} [TopologicalSpace γ] {g : γ → α} :
    Continuous ((f : α → β) ∘ g) ↔ Continuous g :=
  (Dilation.isUniformInducing f).isInducing.continuous_iff.symm
end PseudoEmetricDilation
section EmetricDilation
variable [EMetricSpace α]
variable [FunLike F α β]
lemma isUniformEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsUniformEmbedding f :=
  (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous
@[deprecated (since := "2024-10-01")] alias uniformEmbedding := isUniformEmbedding
theorem isEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsEmbedding (f : α → β) :=
  (Dilation.isUniformEmbedding f).isEmbedding
@[deprecated (since := "2024-10-26")]
alias embedding := isEmbedding
lemma isClosedEmbedding [CompleteSpace α] [EMetricSpace β] [DilationClass F α β] (f : F) :
    IsClosedEmbedding f :=
  (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous
@[deprecated (since := "2024-10-20")] alias closedEmbedding := isClosedEmbedding
end EmetricDilation
@[simp]
theorem ratio_comp [MetricSpace α] [Nontrivial α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] {g : β →ᵈ γ} {f : α →ᵈ β} : ratio (g.comp f) = ratio g * ratio f :=
  ratio_comp' <|
    let ⟨x, y, hne⟩ := exists_pair_ne α; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩
section PseudoMetricDilation
variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [DilationClass F α β] (f : F)
theorem diam_image (s : Set α) : Metric.diam ((f : α → β) '' s) = ratio f * Metric.diam s := by
  simp [Metric.diam, ediam_image, ENNReal.toReal_mul]
theorem diam_range : Metric.diam (range (f : α → β)) = ratio f * Metric.diam (univ : Set α) := by
  rw [← image_univ, diam_image]
theorem mapsTo_ball (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.ball x r') (Metric.ball (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_lt <| (mul_lt_mul_left <| NNReal.coe_pos.2 <| ratio_pos f).2 hy
theorem mapsTo_sphere (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.sphere x r') (Metric.sphere (f x) (ratio f * r')) :=
  fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x
theorem mapsTo_closedBall (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.closedBall x r') (Metric.closedBall (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_le <| mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)
lemma tendsto_cobounded : Filter.Tendsto f (cobounded α) (cobounded β) :=
  (Dilation.antilipschitz f).tendsto_cobounded
@[simp]
lemma comap_cobounded : Filter.comap f (cobounded β) = cobounded α :=
  le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap
end PseudoMetricDilation
end Dilation