import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.RestrictGen
noncomputable section
open Filter Set Topology
open scoped Uniformity
section TypeAlias
def UniformFun (α β : Type*) :=
  α → β
@[nolint unusedArguments]
def UniformOnFun (α β : Type*) (_ : Set (Set α)) :=
  α → β
@[inherit_doc] scoped[UniformConvergence] notation:25 α " →ᵤ " β:0 => UniformFun α β
@[inherit_doc] scoped[UniformConvergence] notation:25 α " →ᵤ[" 𝔖 "] " β:0 => UniformOnFun α β 𝔖
open UniformConvergence
variable {α β : Type*} {𝔖 : Set (Set α)}
instance [Nonempty β] : Nonempty (α →ᵤ β) := Pi.instNonempty
instance [Nonempty β] : Nonempty (α →ᵤ[𝔖] β) := Pi.instNonempty
instance [Subsingleton β] : Subsingleton (α →ᵤ β) :=
  inferInstanceAs <| Subsingleton <| α → β
instance [Subsingleton β] : Subsingleton (α →ᵤ[𝔖] β) :=
  inferInstanceAs <| Subsingleton <| α → β
def UniformFun.ofFun : (α → β) ≃ (α →ᵤ β) :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
def UniformOnFun.ofFun (𝔖) : (α → β) ≃ (α →ᵤ[𝔖] β) :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
def UniformFun.toFun : (α →ᵤ β) ≃ (α → β) :=
  UniformFun.ofFun.symm
def UniformOnFun.toFun (𝔖) : (α →ᵤ[𝔖] β) ≃ (α → β) :=
  (UniformOnFun.ofFun 𝔖).symm
@[simp] lemma UniformFun.toFun_ofFun (f : α → β) : toFun (ofFun f) = f := rfl
@[simp] lemma UniformFun.ofFun_toFun (f : α →ᵤ β) : ofFun (toFun f) = f := rfl
@[simp] lemma UniformOnFun.toFun_ofFun (f : α → β) : toFun 𝔖 (ofFun 𝔖 f) = f := rfl
@[simp] lemma UniformOnFun.ofFun_toFun (f : α →ᵤ[𝔖] β) : ofFun 𝔖 (toFun 𝔖 f) = f := rfl
end TypeAlias
open UniformConvergence
namespace UniformFun
variable (α β : Type*) {γ ι : Type*}
variable {p : Filter ι}
protected def gen (V : Set (β × β)) : Set ((α →ᵤ β) × (α →ᵤ β)) :=
  { uv : (α →ᵤ β) × (α →ᵤ β) | ∀ x, (toFun uv.1 x, toFun uv.2 x) ∈ V }
protected theorem isBasis_gen (𝓑 : Filter <| β × β) :
    IsBasis (fun V : Set (β × β) => V ∈ 𝓑) (UniformFun.gen α β) :=
  ⟨⟨univ, univ_mem⟩, @fun U V hU hV =>
    ⟨U ∩ V, inter_mem hU hV, fun _ huv => ⟨fun x => (huv x).left, fun x => (huv x).right⟩⟩⟩
protected def basis (𝓕 : Filter <| β × β) : FilterBasis ((α →ᵤ β) × (α →ᵤ β)) :=
  (UniformFun.isBasis_gen α β 𝓕).filterBasis
protected def filter (𝓕 : Filter <| β × β) : Filter ((α →ᵤ β) × (α →ᵤ β)) :=
  (UniformFun.basis α β 𝓕).filter
protected def phi (α β : Type*) (uvx : ((α →ᵤ β) × (α →ᵤ β)) × α) : β × β :=
  (uvx.fst.fst uvx.2, uvx.1.2 uvx.2)
set_option quotPrecheck false 
local notation "lowerAdjoint" => fun 𝓐 => map (UniformFun.phi α β) (𝓐 ×ˢ ⊤)
protected theorem gc : GaloisConnection lowerAdjoint fun 𝓕 => UniformFun.filter α β 𝓕 := by
  intro 𝓐 𝓕
  symm
  calc
    𝓐 ≤ UniformFun.filter α β 𝓕 ↔ (UniformFun.basis α β 𝓕).sets ⊆ 𝓐.sets := by
      rw [UniformFun.filter, ← FilterBasis.generate, le_generate_iff]
    _ ↔ ∀ U ∈ 𝓕, UniformFun.gen α β U ∈ 𝓐 := image_subset_iff
    _ ↔ ∀ U ∈ 𝓕,
          { uv | ∀ x, (uv, x) ∈ { t : ((α →ᵤ β) × (α →ᵤ β)) × α | (t.1.1 t.2, t.1.2 t.2) ∈ U } } ∈
            𝓐 :=
      Iff.rfl
    _ ↔ ∀ U ∈ 𝓕,
          { uvx : ((α →ᵤ β) × (α →ᵤ β)) × α | (uvx.1.1 uvx.2, uvx.1.2 uvx.2) ∈ U } ∈
            𝓐 ×ˢ (⊤ : Filter α) :=
      forall₂_congr fun U _hU => mem_prod_top.symm
    _ ↔ lowerAdjoint 𝓐 ≤ 𝓕 := Iff.rfl
variable [UniformSpace β]
protected def uniformCore : UniformSpace.Core (α →ᵤ β) :=
  UniformSpace.Core.mkOfBasis (UniformFun.basis α β (𝓤 β))
    (fun _ ⟨_, hV, hVU⟩ _ => hVU ▸ fun _ => refl_mem_uniformity hV)
    (fun _ ⟨V, hV, hVU⟩ =>
      hVU ▸
        ⟨UniformFun.gen α β (Prod.swap ⁻¹' V), ⟨Prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩,
          fun _ huv x => huv x⟩)
    fun _ ⟨_, hV, hVU⟩ =>
    hVU ▸
      let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
      ⟨UniformFun.gen α β W, ⟨W, hW, rfl⟩, fun _ ⟨w, huw, hwv⟩ x => hWV ⟨w x, ⟨huw x, hwv x⟩⟩⟩
instance uniformSpace : UniformSpace (α →ᵤ β) :=
  UniformSpace.ofCore (UniformFun.uniformCore α β)
instance topologicalSpace : TopologicalSpace (α →ᵤ β) :=
  inferInstance
local notation "𝒰(" α ", " β ", " u ")" => @UniformFun.uniformSpace α β u
protected theorem hasBasis_uniformity :
    (𝓤 (α →ᵤ β)).HasBasis (· ∈ 𝓤 β) (UniformFun.gen α β) :=
  (UniformFun.isBasis_gen α β (𝓤 β)).hasBasis
protected theorem hasBasis_uniformity_of_basis {ι : Sort*} {p : ι → Prop} {s : ι → Set (β × β)}
    (h : (𝓤 β).HasBasis p s) : (𝓤 (α →ᵤ β)).HasBasis p (UniformFun.gen α β ∘ s) :=
  (UniformFun.hasBasis_uniformity α β).to_hasBasis
    (fun _ hU =>
      let ⟨i, hi, hiU⟩ := h.mem_iff.mp hU
      ⟨i, hi, fun _ huv x => hiU (huv x)⟩)
    fun i hi => ⟨s i, h.mem_of_mem hi, subset_refl _⟩
protected theorem hasBasis_nhds_of_basis (f) {p : ι → Prop} {s : ι → Set (β × β)}
    (h : HasBasis (𝓤 β) p s) :
    (𝓝 f).HasBasis p fun i => { g | (f, g) ∈ UniformFun.gen α β (s i) } :=
  nhds_basis_uniformity' (UniformFun.hasBasis_uniformity_of_basis α β h)
protected theorem hasBasis_nhds (f) :
    (𝓝 f).HasBasis (fun V => V ∈ 𝓤 β) fun V => { g | (f, g) ∈ UniformFun.gen α β V } :=
  UniformFun.hasBasis_nhds_of_basis α β f (Filter.basis_sets _)
variable {α}
theorem uniformContinuous_eval (x : α) :
    UniformContinuous (Function.eval x ∘ toFun : (α →ᵤ β) → β) := by
  change _ ≤ _
  rw [map_le_iff_le_comap,
    (UniformFun.hasBasis_uniformity α β).le_basis_iff ((𝓤 _).basis_sets.comap _)]
  exact fun U hU => ⟨U, hU, fun uv huv => huv x⟩
variable {β}
@[simp]
protected lemma mem_gen {β} {f g : α →ᵤ β} {V : Set (β × β)} :
    (f, g) ∈ UniformFun.gen α β V ↔ ∀ x, (toFun f x, toFun g x) ∈ V :=
  .rfl
protected theorem mono : Monotone (@UniformFun.uniformSpace α γ) := fun _ _ hu =>
  (UniformFun.gc α γ).monotone_u hu
protected theorem iInf_eq {u : ι → UniformSpace γ} : 𝒰(α, γ, (⨅ i, u i)) = ⨅ i, 𝒰(α, γ, u i) := by
  ext : 1
  change UniformFun.filter α γ 𝓤[⨅ i, u i] = 𝓤[⨅ i, 𝒰(α, γ, u i)]
  rw [iInf_uniformity, iInf_uniformity]
  exact (UniformFun.gc α γ).u_iInf
protected theorem inf_eq {u₁ u₂ : UniformSpace γ} :
    𝒰(α, γ, u₁ ⊓ u₂) = 𝒰(α, γ, u₁) ⊓ 𝒰(α, γ, u₂) := by
  rw [inf_eq_iInf, inf_eq_iInf, UniformFun.iInf_eq]
  refine iInf_congr fun i => ?_
  cases i <;> rfl
lemma postcomp_isUniformInducing [UniformSpace γ] {f : γ → β}
    (hf : IsUniformInducing f) : IsUniformInducing (ofFun ∘ (f ∘ ·) ∘ toFun : (α →ᵤ γ) → α →ᵤ β) :=
  ⟨((UniformFun.hasBasis_uniformity _ _).comap _).eq_of_same_basis <|
    UniformFun.hasBasis_uniformity_of_basis _ _ (hf.basis_uniformity (𝓤 β).basis_sets)⟩
@[deprecated (since := "2024-10-05")]
alias postcomp_uniformInducing := postcomp_isUniformInducing
protected theorem postcomp_isUniformEmbedding [UniformSpace γ] {f : γ → β}
    (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (ofFun ∘ (f ∘ ·) ∘ toFun : (α →ᵤ γ) → α →ᵤ β) where
  toIsUniformInducing := UniformFun.postcomp_isUniformInducing hf.isUniformInducing
  injective _ _ H := funext fun _ ↦ hf.injective (congrFun H _)
@[deprecated (since := "2024-10-01")]
alias postcomp_uniformEmbedding := UniformFun.postcomp_isUniformEmbedding
protected theorem comap_eq {f : γ → β} :
    𝒰(α, γ, ‹UniformSpace β›.comap f) = 𝒰(α, β, _).comap (f ∘ ·) := by
  letI : UniformSpace γ := .comap f ‹_›
  exact (UniformFun.postcomp_isUniformInducing (f := f) ⟨rfl⟩).comap_uniformSpace.symm
protected theorem postcomp_uniformContinuous [UniformSpace γ] {f : γ → β}
    (hf : UniformContinuous f) :
    UniformContinuous (ofFun ∘ (f ∘ ·) ∘ toFun : (α →ᵤ γ) → α →ᵤ β) := by
    refine uniformContinuous_iff.mpr ?_
    exact (UniformFun.mono (uniformContinuous_iff.mp hf)).trans_eq UniformFun.comap_eq
protected def congrRight [UniformSpace γ] (e : γ ≃ᵤ β) : (α →ᵤ γ) ≃ᵤ (α →ᵤ β) :=
  { Equiv.piCongrRight fun _ => e.toEquiv with
    uniformContinuous_toFun := UniformFun.postcomp_uniformContinuous e.uniformContinuous
    uniformContinuous_invFun := UniformFun.postcomp_uniformContinuous e.symm.uniformContinuous }
protected theorem precomp_uniformContinuous {f : γ → α} :
    UniformContinuous fun g : α →ᵤ β => ofFun (toFun g ∘ f) := by
  rw [UniformContinuous,
      (UniformFun.hasBasis_uniformity α β).tendsto_iff (UniformFun.hasBasis_uniformity γ β)]
  exact fun U hU => ⟨U, hU, fun uv huv x => huv (f x)⟩
protected def congrLeft (e : γ ≃ α) : (γ →ᵤ β) ≃ᵤ (α →ᵤ β) where
  toEquiv := e.arrowCongr (.refl _)
  uniformContinuous_toFun := UniformFun.precomp_uniformContinuous
  uniformContinuous_invFun := UniformFun.precomp_uniformContinuous
protected theorem uniformContinuous_toFun : UniformContinuous (toFun : (α →ᵤ β) → α → β) := by
  rw [uniformContinuous_pi]
  intro x
  exact uniformContinuous_eval β x
instance [T2Space β] : T2Space (α →ᵤ β) :=
  .of_injective_continuous toFun.injective UniformFun.uniformContinuous_toFun.continuous
protected theorem tendsto_iff_tendstoUniformly {F : ι → α →ᵤ β} {f : α →ᵤ β} :
    Tendsto F p (𝓝 f) ↔ TendstoUniformly (toFun ∘ F) (toFun f) p := by
  rw [(UniformFun.hasBasis_nhds α β f).tendsto_right_iff, TendstoUniformly]
  simp only [mem_setOf, UniformFun.gen, Function.comp_def]
protected def uniformEquivProdArrow [UniformSpace γ] : (α →ᵤ β × γ) ≃ᵤ (α →ᵤ β) × (α →ᵤ γ) :=
  Equiv.toUniformEquivOfIsUniformInducing (Equiv.arrowProdEquivProdArrow _ _ _) <| by
    constructor
    change
      comap (Prod.map (Equiv.arrowProdEquivProdArrow _ _ _) (Equiv.arrowProdEquivProdArrow _ _ _))
          _ = _
    simp_rw [UniformFun]
    rw [← uniformity_comap]
    congr
    unfold instUniformSpaceProd
    rw [UniformSpace.comap_inf, ← UniformSpace.comap_comap, ← UniformSpace.comap_comap]
    have := (@UniformFun.inf_eq α (β × γ)
      (UniformSpace.comap Prod.fst ‹_›) (UniformSpace.comap Prod.snd ‹_›)).symm
    rwa [UniformFun.comap_eq, UniformFun.comap_eq] at this
variable (α) (δ : ι → Type*) [∀ i, UniformSpace (δ i)]
protected def uniformEquivPiComm : UniformEquiv (α →ᵤ ∀ i, δ i) (∀ i, α →ᵤ δ i) :=
    @Equiv.toUniformEquivOfIsUniformInducing
    _ _ 𝒰(α, ∀ i, δ i, Pi.uniformSpace δ)
    (@Pi.uniformSpace ι (fun i => α → δ i) fun i => 𝒰(α, δ i, _)) (Equiv.piComm _) <| by
      refine @IsUniformInducing.mk ?_ ?_ ?_ ?_ ?_ ?_
      change comap (Prod.map Function.swap Function.swap) _ = _
      rw [← uniformity_comap]
      congr
      unfold Pi.uniformSpace
      rw [UniformSpace.ofCoreEq_toCore, UniformSpace.ofCoreEq_toCore,
        UniformSpace.comap_iInf, UniformFun.iInf_eq]
      refine iInf_congr fun i => ?_
      rw [← UniformSpace.comap_comap, UniformFun.comap_eq]
      rfl
theorem isClosed_setOf_continuous [TopologicalSpace α] :
    IsClosed {f : α →ᵤ β | Continuous (toFun f)} := by
  refine isClosed_iff_forall_filter.2 fun f u _ hu huf ↦ ?_
  rw [← tendsto_id', UniformFun.tendsto_iff_tendstoUniformly] at huf
  exact huf.continuous (le_principal_iff.mp hu)
variable {α} (β) in
theorem uniformSpace_eq_inf_precomp_of_cover {δ₁ δ₂ : Type*} (φ₁ : δ₁ → α) (φ₂ : δ₂ → α)
    (h_cover : range φ₁ ∪ range φ₂ = univ) :
    𝒰(α, β, _) =
      .comap (ofFun ∘ (· ∘ φ₁) ∘ toFun) 𝒰(δ₁, β, _) ⊓
      .comap (ofFun ∘ (· ∘ φ₂) ∘ toFun) 𝒰(δ₂, β, _) := by
  ext : 1
  refine le_antisymm (le_inf ?_ ?_) ?_
  · exact tendsto_iff_comap.mp UniformFun.precomp_uniformContinuous
  · exact tendsto_iff_comap.mp UniformFun.precomp_uniformContinuous
  · refine
      (UniformFun.hasBasis_uniformity δ₁ β |>.comap _).inf
      (UniformFun.hasBasis_uniformity δ₂ β |>.comap _)
        |>.le_basis_iff (UniformFun.hasBasis_uniformity α β) |>.mpr fun U hU ↦
        ⟨⟨U, U⟩, ⟨hU, hU⟩, fun ⟨f, g⟩ hfg x ↦ ?_⟩
    rcases h_cover.ge <| mem_univ x with (⟨y, rfl⟩|⟨y, rfl⟩)
    · exact hfg.1 y
    · exact hfg.2 y
variable {α} (β) in
theorem uniformSpace_eq_iInf_precomp_of_cover {δ : ι → Type*} (φ : Π i, δ i → α)
    (h_cover : ∃ I : Set ι, I.Finite ∧ ⋃ i ∈ I, range (φ i) = univ) :
    𝒰(α, β, _) = ⨅ i, .comap (ofFun ∘ (· ∘ φ i) ∘ toFun) 𝒰(δ i, β, _) := by
  ext : 1
  simp_rw [iInf_uniformity, uniformity_comap]
  refine le_antisymm (le_iInf fun i ↦ tendsto_iff_comap.mp UniformFun.precomp_uniformContinuous) ?_
  rcases h_cover with ⟨I, I_finite, I_cover⟩
  refine Filter.hasBasis_iInf (fun i : ι ↦ UniformFun.hasBasis_uniformity (δ i) β |>.comap _)
      |>.le_basis_iff (UniformFun.hasBasis_uniformity α β) |>.mpr fun U hU ↦
    ⟨⟨I, fun _ ↦ U⟩, ⟨I_finite, fun _ ↦ hU⟩, fun ⟨f, g⟩ hfg x ↦ ?_⟩
  rcases mem_iUnion₂.mp <| I_cover.ge <| mem_univ x with ⟨i, hi, y, rfl⟩
  exact mem_iInter.mp hfg ⟨i, hi⟩ y
end UniformFun
namespace UniformOnFun
variable {α β : Type*} {γ ι : Type*}
variable {s : Set α} {p : Filter ι}
local notation "𝒰(" α ", " β ", " u ")" => @UniformFun.uniformSpace α β u
protected def gen (𝔖) (S : Set α) (V : Set (β × β)) : Set ((α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] β)) :=
  { uv : (α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] β) | ∀ x ∈ S, (toFun 𝔖 uv.1 x, toFun 𝔖 uv.2 x) ∈ V }
protected theorem gen_eq_preimage_restrict {𝔖} (S : Set α) (V : Set (β × β)) :
    UniformOnFun.gen 𝔖 S V =
      Prod.map (S.restrict ∘ UniformFun.toFun) (S.restrict ∘ UniformFun.toFun) ⁻¹'
        UniformFun.gen S β V := by
  ext uv
  exact ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩
protected theorem gen_mono {𝔖} {S S' : Set α} {V V' : Set (β × β)} (hS : S' ⊆ S) (hV : V ⊆ V') :
    UniformOnFun.gen 𝔖 S V ⊆ UniformOnFun.gen 𝔖 S' V' := fun _uv h x hx => hV (h x <| hS hx)
protected theorem isBasis_gen (𝔖 : Set (Set α)) (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖)
    (𝓑 : FilterBasis <| β × β) :
    IsBasis (fun SV : Set α × Set (β × β) => SV.1 ∈ 𝔖 ∧ SV.2 ∈ 𝓑) fun SV =>
      UniformOnFun.gen 𝔖 SV.1 SV.2 :=
  ⟨h.prod 𝓑.nonempty, fun {U₁V₁ U₂V₂} h₁ h₂ =>
    let ⟨U₃, hU₃, hU₁₃, hU₂₃⟩ := h' U₁V₁.1 h₁.1 U₂V₂.1 h₂.1
    let ⟨V₃, hV₃, hV₁₂₃⟩ := 𝓑.inter_sets h₁.2 h₂.2
    ⟨⟨U₃, V₃⟩,
      ⟨⟨hU₃, hV₃⟩, fun _ H =>
        ⟨fun x hx => (hV₁₂₃ <| H x <| hU₁₃ hx).1, fun x hx => (hV₁₂₃ <| H x <| hU₂₃ hx).2⟩⟩⟩⟩
variable (α β) [UniformSpace β] (𝔖 : Set (Set α))
instance uniformSpace : UniformSpace (α →ᵤ[𝔖] β) :=
  ⨅ (s : Set α) (_ : s ∈ 𝔖),
    .comap (UniformFun.ofFun ∘ s.restrict ∘ UniformOnFun.toFun 𝔖) 𝒰(s, β, _)
local notation "𝒱(" α ", " β ", " 𝔖 ", " u ")" => @UniformOnFun.uniformSpace α β u 𝔖
instance topologicalSpace : TopologicalSpace (α →ᵤ[𝔖] β) :=
  𝒱(α, β, 𝔖, _).toTopologicalSpace
protected theorem topologicalSpace_eq :
    UniformOnFun.topologicalSpace α β 𝔖 =
      ⨅ (s : Set α) (_ : s ∈ 𝔖), TopologicalSpace.induced
        (UniformFun.ofFun ∘ s.restrict ∘ toFun 𝔖) (UniformFun.topologicalSpace s β) := by
  simp only [UniformOnFun.topologicalSpace, UniformSpace.toTopologicalSpace_iInf]
  rfl
protected theorem hasBasis_uniformity_of_basis_aux₁ {p : ι → Prop} {s : ι → Set (β × β)}
    (hb : HasBasis (𝓤 β) p s) (S : Set α) :
    (@uniformity (α →ᵤ[𝔖] β) ((UniformFun.uniformSpace S β).comap S.restrict)).HasBasis p fun i =>
      UniformOnFun.gen 𝔖 S (s i) := by
  simp_rw [UniformOnFun.gen_eq_preimage_restrict, uniformity_comap]
  exact (UniformFun.hasBasis_uniformity_of_basis S β hb).comap _
protected theorem hasBasis_uniformity_of_basis_aux₂ (h : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {s : ι → Set (β × β)} (hb : HasBasis (𝓤 β) p s) :
    DirectedOn
      ((fun s : Set α => (UniformFun.uniformSpace s β).comap (s.restrict : (α →ᵤ β) → s →ᵤ β)) ⁻¹'o
        GE.ge)
      𝔖 :=
  h.mono fun _ _ hst =>
    ((UniformOnFun.hasBasis_uniformity_of_basis_aux₁ α β 𝔖 hb _).le_basis_iff
          (UniformOnFun.hasBasis_uniformity_of_basis_aux₁ α β 𝔖 hb _)).mpr
      fun V hV => ⟨V, hV, UniformOnFun.gen_mono hst subset_rfl⟩
protected theorem hasBasis_uniformity_of_basis (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖)
    {p : ι → Prop} {s : ι → Set (β × β)} (hb : HasBasis (𝓤 β) p s) :
    (𝓤 (α →ᵤ[𝔖] β)).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2) fun Si =>
      UniformOnFun.gen 𝔖 Si.1 (s Si.2) := by
  simp only [iInf_uniformity]
  exact
    hasBasis_biInf_of_directed h (fun S => UniformOnFun.gen 𝔖 S ∘ s) _
      (fun S _hS => UniformOnFun.hasBasis_uniformity_of_basis_aux₁ α β 𝔖 hb S)
      (UniformOnFun.hasBasis_uniformity_of_basis_aux₂ α β 𝔖 h' hb)
protected theorem hasBasis_uniformity (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓤 (α →ᵤ[𝔖] β)).HasBasis (fun SV : Set α × Set (β × β) => SV.1 ∈ 𝔖 ∧ SV.2 ∈ 𝓤 β) fun SV =>
      UniformOnFun.gen 𝔖 SV.1 SV.2 :=
  UniformOnFun.hasBasis_uniformity_of_basis α β 𝔖 h h' (𝓤 β).basis_sets
variable {α β}
protected theorem hasBasis_uniformity_of_covering_of_basis {ι ι' : Type*} [Nonempty ι]
    {t : ι → Set α} {p : ι' → Prop} {V : ι' → Set (β × β)} (ht : ∀ i, t i ∈ 𝔖)
    (hdir : Directed (· ⊆ ·) t) (hex : ∀ s ∈ 𝔖, ∃ i, s ⊆ t i) (hb : HasBasis (𝓤 β) p V) :
    (𝓤 (α →ᵤ[𝔖] β)).HasBasis (fun i : ι × ι' ↦ p i.2) fun i ↦
      UniformOnFun.gen 𝔖 (t i.1) (V i.2) := by
  have hne : 𝔖.Nonempty := (range_nonempty t).mono (range_subset_iff.2 ht)
  have hd : DirectedOn (· ⊆ ·) 𝔖 := fun s₁ hs₁ s₂ hs₂ ↦ by
    rcases hex s₁ hs₁, hex s₂ hs₂ with ⟨⟨i₁, his₁⟩, i₂, his₂⟩
    rcases hdir i₁ i₂ with ⟨i, hi₁, hi₂⟩
    exact ⟨t i, ht _, his₁.trans hi₁, his₂.trans hi₂⟩
  refine (UniformOnFun.hasBasis_uniformity_of_basis α β 𝔖 hne hd hb).to_hasBasis
    (fun ⟨s, i'⟩ ⟨hs, hi'⟩ ↦ ?_) fun ⟨i, i'⟩ hi' ↦ ⟨(t i, i'), ⟨ht i, hi'⟩, Subset.rfl⟩
  rcases hex s hs with ⟨i, hi⟩
  exact ⟨(i, i'), hi', UniformOnFun.gen_mono hi Subset.rfl⟩
protected theorem hasAntitoneBasis_uniformity {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {t : ι → Set α} {V : ι → Set (β × β)}
    (ht : ∀ n, t n ∈ 𝔖) (hmono : Monotone t) (hex : ∀ s ∈ 𝔖, ∃ n, s ⊆ t n)
    (hb : HasAntitoneBasis (𝓤 β) V) :
    (𝓤 (α →ᵤ[𝔖] β)).HasAntitoneBasis fun n ↦ UniformOnFun.gen 𝔖 (t n) (V n) := by
  have := hb.nonempty
  refine ⟨(UniformOnFun.hasBasis_uniformity_of_covering_of_basis 𝔖
    ht hmono.directed_le hex hb.1).to_hasBasis ?_ fun i _ ↦ ⟨(i, i), trivial, Subset.rfl⟩, ?_⟩
  · rintro ⟨k, l⟩ -
    rcases directed_of (· ≤ ·) k l with ⟨n, hkn, hln⟩
    exact ⟨n, trivial, UniformOnFun.gen_mono (hmono hkn) (hb.2 <| hln)⟩
  · exact fun k l h ↦ UniformOnFun.gen_mono (hmono h) (hb.2 h)
protected theorem isCountablyGenerated_uniformity [IsCountablyGenerated (𝓤 β)] {t : ℕ → Set α}
    (ht : ∀ n, t n ∈ 𝔖) (hmono : Monotone t) (hex : ∀ s ∈ 𝔖, ∃ n, s ⊆ t n) :
    IsCountablyGenerated (𝓤 (α →ᵤ[𝔖] β)) :=
  let ⟨_V, hV⟩ := exists_antitone_basis (𝓤 β)
  (UniformOnFun.hasAntitoneBasis_uniformity 𝔖 ht hmono hex hV).isCountablyGenerated
variable (α β)
protected theorem hasBasis_nhds_of_basis (f : α →ᵤ[𝔖] β) (h : 𝔖.Nonempty)
    (h' : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop} {s : ι → Set (β × β)} (hb : HasBasis (𝓤 β) p s) :
    (𝓝 f).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2) fun Si =>
      { g | (g, f) ∈ UniformOnFun.gen 𝔖 Si.1 (s Si.2) } :=
  letI : UniformSpace (α → β) := UniformOnFun.uniformSpace α β 𝔖
  nhds_basis_uniformity (UniformOnFun.hasBasis_uniformity_of_basis α β 𝔖 h h' hb)
protected theorem hasBasis_nhds (f : α →ᵤ[𝔖] β) (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 f).HasBasis (fun SV : Set α × Set (β × β) => SV.1 ∈ 𝔖 ∧ SV.2 ∈ 𝓤 β) fun SV =>
      { g | (g, f) ∈ UniformOnFun.gen 𝔖 SV.1 SV.2 } :=
  UniformOnFun.hasBasis_nhds_of_basis α β 𝔖 f h h' (Filter.basis_sets _)
protected theorem uniformContinuous_restrict (h : s ∈ 𝔖) :
    UniformContinuous (UniformFun.ofFun ∘ (s.restrict : (α → β) → s → β) ∘ toFun 𝔖) := by
  change _ ≤ _
  simp only [UniformOnFun.uniformSpace, map_le_iff_le_comap, iInf_uniformity]
  exact iInf₂_le s h
variable {α}
protected theorem uniformity_eq_of_basis {ι : Sort*} {p : ι → Prop} {V : ι → Set (β × β)}
    (h : (𝓤 β).HasBasis p V) :
    𝓤 (α →ᵤ[𝔖] β) = ⨅ s ∈ 𝔖, ⨅ (i) (_ : p i), 𝓟 (UniformOnFun.gen 𝔖 s (V i)) := by
  simp_rw [iInf_uniformity, uniformity_comap,
    (UniformFun.hasBasis_uniformity_of_basis _ _ h).eq_biInf, comap_iInf, comap_principal,
    Function.comp_apply, UniformFun.gen, Subtype.forall, UniformOnFun.gen, preimage_setOf_eq,
    Prod.map_fst, Prod.map_snd, Function.comp_apply, UniformFun.toFun_ofFun, restrict_apply]
protected theorem uniformity_eq : 𝓤 (α →ᵤ[𝔖] β) = ⨅ s ∈ 𝔖, ⨅ V ∈ 𝓤 β, 𝓟 (UniformOnFun.gen 𝔖 s V) :=
  UniformOnFun.uniformity_eq_of_basis _ _ (𝓤 β).basis_sets
protected theorem gen_mem_uniformity (hs : s ∈ 𝔖) {V : Set (β × β)} (hV : V ∈ 𝓤 β) :
    UniformOnFun.gen 𝔖 s V ∈ 𝓤 (α →ᵤ[𝔖] β) := by
  rw [UniformOnFun.uniformity_eq]
  apply_rules [mem_iInf_of_mem, mem_principal_self]
protected theorem nhds_eq_of_basis {ι : Sort*} {p : ι → Prop} {V : ι → Set (β × β)}
    (h : (𝓤 β).HasBasis p V) (f : α →ᵤ[𝔖] β) :
    𝓝 f = ⨅ s ∈ 𝔖, ⨅ (i) (_ : p i), 𝓟 {g | ∀ x ∈ s, (toFun 𝔖 f x, toFun 𝔖 g x) ∈ V i} := by
  simp_rw [nhds_eq_comap_uniformity, UniformOnFun.uniformity_eq_of_basis _ _ h, comap_iInf,
    comap_principal, UniformOnFun.gen, preimage_setOf_eq]
protected theorem nhds_eq (f : α →ᵤ[𝔖] β) :
    𝓝 f = ⨅ s ∈ 𝔖, ⨅ V ∈ 𝓤 β, 𝓟 {g | ∀ x ∈ s, (toFun 𝔖 f x, toFun 𝔖 g x) ∈ V} :=
  UniformOnFun.nhds_eq_of_basis _ _ (𝓤 β).basis_sets f
protected theorem gen_mem_nhds (f : α →ᵤ[𝔖] β) (hs : s ∈ 𝔖) {V : Set (β × β)} (hV : V ∈ 𝓤 β) :
    {g | ∀ x ∈ s, (toFun 𝔖 f x, toFun 𝔖 g x) ∈ V} ∈ 𝓝 f := by
  rw [UniformOnFun.nhds_eq]
  apply_rules [mem_iInf_of_mem, mem_principal_self]
theorem uniformContinuous_ofUniformFun :
    UniformContinuous fun f : α →ᵤ β ↦ ofFun 𝔖 (UniformFun.toFun f) := by
  simp only [UniformContinuous, UniformOnFun.uniformity_eq, tendsto_iInf, tendsto_principal,
    (UniformFun.hasBasis_uniformity _ _).eventually_iff]
  exact fun _ _ U hU ↦ ⟨U, hU, fun f hf x _ ↦ hf x⟩
def uniformEquivUniformFun (h : univ ∈ 𝔖) : (α →ᵤ[𝔖] β) ≃ᵤ (α →ᵤ β) where
  toFun f := UniformFun.ofFun <| toFun _ f
  invFun f := ofFun _ <| UniformFun.toFun f
  left_inv _ := rfl
  right_inv _ := rfl
  uniformContinuous_toFun := by
    simp only [UniformContinuous, (UniformFun.hasBasis_uniformity _ _).tendsto_right_iff]
    intro U hU
    filter_upwards [UniformOnFun.gen_mem_uniformity _ _ h hU] with f hf x using hf x (mem_univ _)
  uniformContinuous_invFun := uniformContinuous_ofUniformFun _ _
protected theorem mono ⦃u₁ u₂ : UniformSpace γ⦄ (hu : u₁ ≤ u₂) ⦃𝔖₁ 𝔖₂ : Set (Set α)⦄
    (h𝔖 : 𝔖₂ ⊆ 𝔖₁) : 𝒱(α, γ, 𝔖₁, u₁) ≤ 𝒱(α, γ, 𝔖₂, u₂) :=
  calc
    𝒱(α, γ, 𝔖₁, u₁) ≤ 𝒱(α, γ, 𝔖₂, u₁) := iInf_le_iInf_of_subset h𝔖
    _ ≤ 𝒱(α, γ, 𝔖₂, u₂) := iInf₂_mono fun _i _hi => UniformSpace.comap_mono <| UniformFun.mono hu
theorem uniformContinuous_eval_of_mem {x : α} (hxs : x ∈ s) (hs : s ∈ 𝔖) :
    UniformContinuous ((Function.eval x : (α → β) → β) ∘ toFun 𝔖) :=
  (UniformFun.uniformContinuous_eval β (⟨x, hxs⟩ : s)).comp
    (UniformOnFun.uniformContinuous_restrict α β 𝔖 hs)
theorem uniformContinuous_eval_of_mem_sUnion {x : α} (hx : x ∈ ⋃₀ 𝔖) :
    UniformContinuous ((Function.eval x : (α → β) → β) ∘ toFun 𝔖) :=
  let ⟨_s, hs, hxs⟩ := hx
  uniformContinuous_eval_of_mem _ _ hxs hs
variable {β} {𝔖}
theorem uniformContinuous_eval (h : ⋃₀ 𝔖 = univ) (x : α) :
    UniformContinuous ((Function.eval x : (α → β) → β) ∘ toFun 𝔖) :=
  uniformContinuous_eval_of_mem_sUnion _ _ <| h.symm ▸ mem_univ _
protected theorem iInf_eq {u : ι → UniformSpace γ} :
    𝒱(α, γ, 𝔖, ⨅ i, u i) = ⨅ i, 𝒱(α, γ, 𝔖, u i) := by
  simp_rw [UniformOnFun.uniformSpace, UniformFun.iInf_eq, UniformSpace.comap_iInf]
  rw [iInf_comm]
  exact iInf_congr fun s => iInf_comm
protected theorem inf_eq {u₁ u₂ : UniformSpace γ} :
    𝒱(α, γ, 𝔖, u₁ ⊓ u₂) = 𝒱(α, γ, 𝔖, u₁) ⊓ 𝒱(α, γ, 𝔖, u₂) := by
  rw [inf_eq_iInf, inf_eq_iInf, UniformOnFun.iInf_eq]
  refine iInf_congr fun i => ?_
  cases i <;> rfl
protected theorem comap_eq {f : γ → β} :
    𝒱(α, γ, 𝔖, ‹UniformSpace β›.comap f) = 𝒱(α, β, 𝔖, _).comap (f ∘ ·) := by
  simp_rw [UniformOnFun.uniformSpace, UniformSpace.comap_iInf, UniformFun.comap_eq, ←
    UniformSpace.comap_comap]
  rfl
protected theorem postcomp_uniformContinuous [UniformSpace γ] {f : γ → β}
    (hf : UniformContinuous f) : UniformContinuous (ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖) := by
  rw [uniformContinuous_iff]
  exact (UniformOnFun.mono (uniformContinuous_iff.mp hf) subset_rfl).trans_eq UniformOnFun.comap_eq
lemma postcomp_isUniformInducing [UniformSpace γ] {f : γ → β}
    (hf : IsUniformInducing f) : IsUniformInducing (ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖) := by
  constructor
  replace hf : (𝓤 β).comap (Prod.map f f) = _ := hf.comap_uniformity
  change comap (Prod.map (ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖) (ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖)) _ = _
  rw [← uniformity_comap] at hf ⊢
  congr
  rw [← UniformSpace.ext hf, UniformOnFun.comap_eq]
  rfl
@[deprecated (since := "2024-10-05")]
alias postcomp_uniformInducing := postcomp_isUniformInducing
protected theorem postcomp_isUniformEmbedding [UniformSpace γ] {f : γ → β}
    (hf : IsUniformEmbedding f) : IsUniformEmbedding (ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖) where
  toIsUniformInducing := UniformOnFun.postcomp_isUniformInducing hf.isUniformInducing
  injective _ _ H := funext fun _ ↦ hf.injective (congrFun H _)
@[deprecated (since := "2024-10-01")]
alias postcomp_uniformEmbedding := UniformOnFun.postcomp_isUniformEmbedding
protected def congrRight [UniformSpace γ] (e : γ ≃ᵤ β) : (α →ᵤ[𝔖] γ) ≃ᵤ (α →ᵤ[𝔖] β) :=
  { Equiv.piCongrRight fun _a => e.toEquiv with
    uniformContinuous_toFun := UniformOnFun.postcomp_uniformContinuous e.uniformContinuous
    uniformContinuous_invFun := UniformOnFun.postcomp_uniformContinuous e.symm.uniformContinuous }
protected theorem precomp_uniformContinuous {𝔗 : Set (Set γ)} {f : γ → α}
    (hf : MapsTo (f '' ·) 𝔗 𝔖) :
    UniformContinuous fun g : α →ᵤ[𝔖] β => ofFun 𝔗 (toFun 𝔖 g ∘ f) := by
  simp_rw [UniformContinuous, UniformOnFun.uniformity_eq, tendsto_iInf]
  refine fun t ht V hV ↦ tendsto_iInf' (f '' t) <| tendsto_iInf' (hf ht) <|
    tendsto_iInf' V <| tendsto_iInf' hV ?_
  simpa only [tendsto_principal_principal, UniformOnFun.gen] using fun _ ↦ forall_mem_image.1
protected def congrLeft {𝔗 : Set (Set γ)} (e : γ ≃ α) (he : 𝔗 ⊆ image e ⁻¹' 𝔖)
    (he' : 𝔖 ⊆ preimage e ⁻¹' 𝔗) : (γ →ᵤ[𝔗] β) ≃ᵤ (α →ᵤ[𝔖] β) :=
  { Equiv.arrowCongr e (Equiv.refl _) with
    uniformContinuous_toFun := UniformOnFun.precomp_uniformContinuous fun s hs ↦ by
      change e.symm '' s ∈ 𝔗
      rw [← preimage_equiv_eq_image_symm]
      exact he' hs
    uniformContinuous_invFun := UniformOnFun.precomp_uniformContinuous he }
theorem t2Space_of_covering [T2Space β] (h : ⋃₀ 𝔖 = univ) : T2Space (α →ᵤ[𝔖] β) where
  t2 f g hfg := by
    obtain ⟨x, hx⟩ := not_forall.mp (mt funext hfg)
    obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ True.intro)
    exact separated_by_continuous (uniformContinuous_eval_of_mem β 𝔖 hxs hs).continuous hx
theorem uniformContinuous_restrict_toFun :
    UniformContinuous ((⋃₀ 𝔖).restrict ∘ toFun 𝔖 : (α →ᵤ[𝔖] β) → ⋃₀ 𝔖 → β) := by
  rw [uniformContinuous_pi]
  intro ⟨x, hx⟩
  obtain ⟨s : Set α, hs : s ∈ 𝔖, hxs : x ∈ s⟩ := mem_sUnion.mpr hx
  exact uniformContinuous_eval_of_mem β 𝔖 hxs hs
protected theorem uniformContinuous_toFun (h : ⋃₀ 𝔖 = univ) :
    UniformContinuous (toFun 𝔖 : (α →ᵤ[𝔖] β) → α → β) := by
  rw [uniformContinuous_pi]
  exact uniformContinuous_eval h
protected theorem continuousAt_eval₂ [TopologicalSpace α] {f : α →ᵤ[𝔖] β} {x : α}
    (h𝔖 : ∃ V ∈ 𝔖, V ∈ 𝓝 x) (hc : ContinuousAt (toFun 𝔖 f) x) :
    ContinuousAt (fun fx : (α →ᵤ[𝔖] β) × α ↦ toFun 𝔖 fx.1 fx.2) (f, x) := by
  rw [ContinuousAt, nhds_eq_comap_uniformity, tendsto_comap_iff, ← lift'_comp_uniformity,
    tendsto_lift']
  intro U hU
  rcases h𝔖 with ⟨V, hV, hVx⟩
  filter_upwards [prod_mem_nhds (UniformOnFun.gen_mem_nhds _ _ _ hV hU)
    (inter_mem hVx <| hc <| UniformSpace.ball_mem_nhds _ hU)]
    with ⟨g, y⟩ ⟨hg, hyV, hy⟩ using ⟨toFun 𝔖 f y, hy, hg y hyV⟩
protected theorem continuousOn_eval₂ [TopologicalSpace α] (h𝔖 : ∀ x, ∃ V ∈ 𝔖, V ∈ 𝓝 x) :
    ContinuousOn (fun fx : (α →ᵤ[𝔖] β) × α ↦ toFun 𝔖 fx.1 fx.2)
      {fx | ContinuousAt (toFun 𝔖 fx.1) fx.2} := fun (_f, x) hc ↦
  (UniformOnFun.continuousAt_eval₂ (h𝔖 x) hc).continuousWithinAt
protected theorem tendsto_iff_tendstoUniformlyOn {F : ι → α →ᵤ[𝔖] β} {f : α →ᵤ[𝔖] β} :
    Tendsto F p (𝓝 f) ↔ ∀ s ∈ 𝔖, TendstoUniformlyOn (toFun 𝔖 ∘ F) (toFun 𝔖 f) p s := by
  simp only [UniformOnFun.nhds_eq, tendsto_iInf, tendsto_principal, TendstoUniformlyOn,
    Function.comp_apply, mem_setOf]
protected lemma continuous_rng_iff {X : Type*} [TopologicalSpace X] {f : X → (α →ᵤ[𝔖] β)} :
    Continuous f ↔ ∀ s ∈ 𝔖,
      Continuous (UniformFun.ofFun ∘ s.restrict ∘ UniformOnFun.toFun 𝔖 ∘ f) := by
  simp only [continuous_iff_continuousAt, ContinuousAt,
    UniformOnFun.tendsto_iff_tendstoUniformlyOn, UniformFun.tendsto_iff_tendstoUniformly,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, @forall_swap X, Function.comp_apply,
    Function.comp_def, restrict_eq, UniformFun.toFun_ofFun]
instance [CompleteSpace β] : CompleteSpace (α →ᵤ[𝔖] β) := by
  rcases isEmpty_or_nonempty β
  · infer_instance
  · refine ⟨fun {F} hF ↦ ?_⟩
    have := hF.1
    have : ∀ x ∈ ⋃₀ 𝔖, ∃ y : β, Tendsto (toFun 𝔖 · x) F (𝓝 y) := fun x hx ↦
      CompleteSpace.complete (hF.map (uniformContinuous_eval_of_mem_sUnion _ _ hx))
    choose! g hg using this
    use ofFun 𝔖 g
    simp_rw [UniformOnFun.nhds_eq_of_basis _ _ uniformity_hasBasis_closed, le_iInf₂_iff,
      le_principal_iff]
    intro s hs U ⟨hU, hUc⟩
    rcases cauchy_iff.mp hF |>.2 _ <| UniformOnFun.gen_mem_uniformity _ _ hs hU
      with ⟨V, hV, hVU⟩
    filter_upwards [hV] with f hf x hx
    refine hUc.mem_of_tendsto ((hg x ⟨s, hs, hx⟩).prod_mk_nhds tendsto_const_nhds) ?_
    filter_upwards [hV] with g' hg' using hVU (mk_mem_prod hg' hf) _ hx
protected def uniformEquivProdArrow [UniformSpace γ] :
    (α →ᵤ[𝔖] β × γ) ≃ᵤ (α →ᵤ[𝔖] β) × (α →ᵤ[𝔖] γ) :=
  ((UniformOnFun.ofFun 𝔖).symm.trans <| (Equiv.arrowProdEquivProdArrow _ _ _).trans <|
    (UniformOnFun.ofFun 𝔖).prodCongr (UniformOnFun.ofFun 𝔖)).toUniformEquivOfIsUniformInducing <| by
      constructor
      rw [uniformity_prod, comap_inf, comap_comap, comap_comap]
      have H := @UniformOnFun.inf_eq α (β × γ) 𝔖
        (UniformSpace.comap Prod.fst ‹_›) (UniformSpace.comap Prod.snd ‹_›)
      apply_fun (fun u ↦ @uniformity (α →ᵤ[𝔖] β × γ) u) at H
      convert H.symm using 1
      rw [UniformOnFun.comap_eq, UniformOnFun.comap_eq]
      erw [inf_uniformity]
      rw [uniformity_comap, uniformity_comap]
      rfl
variable (𝔖) (δ : ι → Type*) [∀ i, UniformSpace (δ i)] in
protected def uniformEquivPiComm : (α →ᵤ[𝔖] ((i : ι) → δ i)) ≃ᵤ ((i : ι) → α →ᵤ[𝔖] δ i) :=
  @Equiv.toUniformEquivOfIsUniformInducing (α →ᵤ[𝔖] ((i : ι) → δ i)) ((i : ι) → α →ᵤ[𝔖] δ i)
      _ _ (Equiv.piComm _) <| by
    constructor
    change comap (Prod.map Function.swap Function.swap) _ = _
    erw [← uniformity_comap]
    congr
    rw [Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, Pi.uniformSpace,
      UniformSpace.ofCoreEq_toCore, UniformSpace.comap_iInf, UniformOnFun.iInf_eq]
    refine iInf_congr fun i => ?_
    rw [← UniformSpace.comap_comap, UniformOnFun.comap_eq]
    rfl
theorem isClosed_setOf_continuous [TopologicalSpace α] (h : RestrictGenTopology 𝔖) :
    IsClosed {f : α →ᵤ[𝔖] β | Continuous (toFun 𝔖 f)} := by
  refine isClosed_iff_forall_filter.2 fun f u _ hu huf ↦ h.continuous_iff.2 fun s hs ↦ ?_
  rw [← tendsto_id', UniformOnFun.tendsto_iff_tendstoUniformlyOn] at huf
  exact (huf s hs).continuousOn <| hu fun _ ↦ Continuous.continuousOn
@[deprecated isClosed_setOf_continuous (since := "2024-06-29")]
theorem isClosed_setOf_continuous_of_le [t : TopologicalSpace α]
    (h : t ≤ ⨆ s ∈ 𝔖, .coinduced (Subtype.val : s → α) inferInstance) :
    IsClosed {f : α →ᵤ[𝔖] β | Continuous (toFun 𝔖 f)} :=
  isClosed_setOf_continuous ⟨fun u hu ↦ h _ <| by simpa only [isOpen_iSup_iff, isOpen_coinduced]⟩
variable (𝔖) in
theorem uniformSpace_eq_inf_precomp_of_cover {δ₁ δ₂ : Type*} (φ₁ : δ₁ → α) (φ₂ : δ₂ → α)
    (𝔗₁ : Set (Set δ₁)) (𝔗₂ : Set (Set δ₂))
    (h_image₁ : MapsTo (φ₁ '' ·) 𝔗₁ 𝔖) (h_image₂ : MapsTo (φ₂ '' ·) 𝔗₂ 𝔖)
    (h_preimage₁ : MapsTo (φ₁ ⁻¹' ·) 𝔖 𝔗₁) (h_preimage₂ : MapsTo (φ₂ ⁻¹' ·) 𝔖 𝔗₂)
    (h_cover : ∀ S ∈ 𝔖, S ⊆ range φ₁ ∪ range φ₂) :
    𝒱(α, β, 𝔖, _) =
      .comap (ofFun 𝔗₁ ∘ (· ∘ φ₁) ∘ toFun 𝔖) 𝒱(δ₁, β, 𝔗₁, _) ⊓
      .comap (ofFun 𝔗₂ ∘ (· ∘ φ₂) ∘ toFun 𝔖) 𝒱(δ₂, β, 𝔗₂, _) := by
  set ψ₁ : Π S : Set α, φ₁ ⁻¹' S → S := fun S ↦ S.restrictPreimage φ₁
  set ψ₂ : Π S : Set α, φ₂ ⁻¹' S → S := fun S ↦ S.restrictPreimage φ₂
  have : ∀ S ∈ 𝔖, 𝒰(S, β, _) = .comap (· ∘ ψ₁ S) 𝒰(_, β, _) ⊓ .comap (· ∘ ψ₂ S) 𝒰(_, β, _) := by
    refine fun S hS ↦ UniformFun.uniformSpace_eq_inf_precomp_of_cover β _ _ ?_
    simpa only [← univ_subset_iff, ψ₁, ψ₂, range_restrictPreimage, ← preimage_union,
      ← image_subset_iff, image_univ, Subtype.range_val] using h_cover S hS
  refine le_antisymm (le_inf ?_ ?_) (le_iInf₂ fun S hS ↦ ?_)
  · rw [← uniformContinuous_iff]
    exact UniformOnFun.precomp_uniformContinuous h_image₁
  · rw [← uniformContinuous_iff]
    exact UniformOnFun.precomp_uniformContinuous h_image₂
  · simp_rw [this S hS, UniformSpace.comap_iInf, UniformSpace.comap_inf, ← UniformSpace.comap_comap]
    exact inf_le_inf
      (iInf₂_le_of_le _ (h_preimage₁ hS) le_rfl)
      (iInf₂_le_of_le _ (h_preimage₂ hS) le_rfl)
variable (𝔖) in
theorem uniformSpace_eq_iInf_precomp_of_cover {δ : ι → Type*} (φ : Π i, δ i → α)
    (𝔗 : ∀ i, Set (Set (δ i))) (h_image : ∀ i, MapsTo (φ i '' ·) (𝔗 i) 𝔖)
    (h_preimage : ∀ i, MapsTo (φ i ⁻¹' ·) 𝔖 (𝔗 i))
    (h_cover : ∀ S ∈ 𝔖, ∃ I : Set ι, I.Finite ∧ S ⊆ ⋃ i ∈ I, range (φ i)) :
    𝒱(α, β, 𝔖, _) = ⨅ i, .comap (ofFun (𝔗 i) ∘ (· ∘ φ i) ∘ toFun 𝔖) 𝒱(δ i, β, 𝔗 i, _) := by
  set ψ : Π S : Set α, Π i : ι, (φ i) ⁻¹' S → S := fun S i ↦ S.restrictPreimage (φ i)
  have : ∀ S ∈ 𝔖, 𝒰(S, β, _) = ⨅ i, .comap (· ∘ ψ S i) 𝒰(_, β, _) := fun S hS ↦ by
    rcases h_cover S hS with ⟨I, I_finite, I_cover⟩
    refine UniformFun.uniformSpace_eq_iInf_precomp_of_cover β _ ⟨I, I_finite, ?_⟩
    simpa only [← univ_subset_iff, ψ, range_restrictPreimage, ← preimage_iUnion₂,
      ← image_subset_iff, image_univ, Subtype.range_val] using I_cover
  refine le_antisymm (le_iInf fun i ↦ ?_) (le_iInf₂ fun S hS ↦ ?_)
  · rw [← uniformContinuous_iff]
    exact UniformOnFun.precomp_uniformContinuous (h_image i)
  · simp_rw [this S hS, UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
    exact iInf_mono fun i ↦ iInf₂_le_of_le _ (h_preimage i hS) le_rfl
end UniformOnFun
namespace UniformFun
instance {α β : Type*} [UniformSpace β] [CompleteSpace β] : CompleteSpace (α →ᵤ β) :=
  (UniformOnFun.uniformEquivUniformFun β {univ} (mem_singleton _)).completeSpace_iff.1 inferInstance
end UniformFun
section UniformComposition
variable {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ] {p : Filter ι}
theorem UniformContinuousOn.comp_tendstoUniformly (s : Set β) (F : ι → α → β) (f : α → β)
    (hF : ∀ i x, F i x ∈ s) (hf : ∀ x, f x ∈ s)
    {g : β → γ} (hg : UniformContinuousOn g s) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i x => g (F i x)) (fun x => g (f x)) p := by
  rw [uniformContinuousOn_iff_restrict] at hg
  lift F to ι → α → s using hF with F' hF'
  lift f to α → s using hf with f' hf'
  rw [tendstoUniformly_iff_tendsto] at h
  have : Tendsto (fun q : ι × α ↦ (f' q.2, (F' q.1 q.2))) (p ×ˢ ⊤) (𝓤 s) :=
    h.of_tendsto_comp isUniformEmbedding_subtype_val.comap_uniformity.le
  apply UniformContinuous.comp_tendstoUniformly hg ?_
  rwa [← tendstoUniformly_iff_tendsto] at this
theorem UniformContinuousOn.comp_tendstoUniformly_eventually (s : Set β) (F : ι → α → β) (f : α → β)
    (hF : ∀ᶠ i in p, ∀ x, F i x ∈ s) (hf : ∀ x, f x ∈ s)
    {g : β → γ} (hg : UniformContinuousOn g s) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i => fun x => g (F i x)) (fun x => g (f x)) p := by
  classical
  rw [eventually_iff_exists_mem] at hF
  obtain ⟨s', hs', hs⟩ := hF
  let F' : ι → α → β := fun (i : ι) x => if i ∈ s' then F i x else f x
  have hF : F =ᶠ[p] F' :=  by
    rw [eventuallyEq_iff_exists_mem]
    refine ⟨s', hs', fun y hy => by aesop⟩
  have h' : TendstoUniformly F' f p := by
    rwa [tendstoUniformly_congr hF] at h
  apply (tendstoUniformly_congr _).mpr
    (UniformContinuousOn.comp_tendstoUniformly s F' f (by aesop) hf hg h')
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨s', hs', fun i hi => by aesop⟩
end UniformComposition