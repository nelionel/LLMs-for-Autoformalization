import Mathlib.Tactic.ApplyFun
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.UniformSpace.Basic
open Filter Set Function Topology Uniformity UniformSpace
noncomputable section
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]
instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .of_hasBasis
    (fun _ ↦ nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun a _V hV ↦ isClosed_ball a hV.2
theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ ∀ i, p i → (x, y) ∈ s i :=
  (nhds_basis_uniformity h).specializes_iff
theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ ∀ i, p i → (x, y) ∈ s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity
theorem inseparable_iff_ker_uniformity {x y : α} : Inseparable x y ↔ (x, y) ∈ (𝓤 α).ker :=
  (𝓤 α).basis_sets.inseparable_iff_uniformity
protected theorem Inseparable.nhds_le_uniformity {x y : α} (h : Inseparable x y) :
    𝓝 (x, y) ≤ 𝓤 α := by
  rw [h.prod rfl]
  apply nhds_le_uniformity
theorem inseparable_iff_clusterPt_uniformity {x y : α} :
    Inseparable x y ↔ ClusterPt (x, y) (𝓤 α) := by
  refine ⟨fun h ↦ .of_nhds_le h.nhds_le_uniformity, fun h ↦ ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
  exact fun U ⟨hU, hUc⟩ ↦ hUc _ <| h.mono <| le_principal_iff.2 hU
theorem t0Space_iff_uniformity :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker, id]
theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y ↦ ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]
theorem t0Space_iff_ker_uniformity : T0Space α ↔ (𝓤 α).ker = diagonal α := by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs ↦ refl_mem_uniformity hs
theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h
theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq
theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)
theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  (inseparable_iff_clusterPt_uniformity.2 h).eq
theorem Filter.Tendsto.inseparable_iff_uniformity {β} {l : Filter β} [NeBot l] {f g : β → α}
    {a b : α} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) :
    Inseparable a b ↔ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α) := by
  refine ⟨fun h ↦ (ha.prod_mk_nhds hb).mono_right h.nhds_le_uniformity, fun h ↦ ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prod_mk_nhds hb)).mono h
theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)
namespace SeparationQuotient
theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU ↦ ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ ↦ ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU
instance instUniformSpace : UniformSpace (SeparationQuotient α) where
  uniformity := map (Prod.map mk mk) (𝓤 α)
  symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht ↦ by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, mem_compRel, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
  nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x ↦ comap_injective surjective_mk <| by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]
theorem uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk) := rfl
theorem uniformContinuous_mk : UniformContinuous (mk : α → SeparationQuotient α) :=
  le_rfl
theorem uniformContinuous_dom {f : SeparationQuotient α → β} :
    UniformContinuous f ↔ UniformContinuous (f ∘ mk) :=
  .rfl
theorem uniformContinuous_dom₂ {f : SeparationQuotient α × SeparationQuotient β → γ} :
    UniformContinuous f ↔ UniformContinuous fun p : α × β ↦ f (mk p.1, mk p.2) := by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl
theorem uniformContinuous_lift {f : α → β} (h : ∀ a b, Inseparable a b → f a = f b) :
    UniformContinuous (lift f h) ↔ UniformContinuous f :=
  .rfl
theorem uniformContinuous_uncurry_lift₂ {f : α → β → γ}
    (h : ∀ a c b d, Inseparable a b → Inseparable c d → f a c = f b d) :
    UniformContinuous (uncurry <| lift₂ f h) ↔ UniformContinuous (uncurry f) :=
  uniformContinuous_dom₂
theorem comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α :=
  comap_map_mk_uniformity
open Classical in
def lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)
theorem lift'_mk [T0Space β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift' f (mk a) = f a := by rw [lift', dif_pos h, lift_mk]
theorem uniformContinuous_lift' [T0Space β] (f : α → β) : UniformContinuous (lift' f) := by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β := lift' (mk ∘ f)
theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk (f a) := by
  rw [map, lift'_mk (uniformContinuous_mk.comp h)]; rfl
theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift' _
theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a
@[simp]
theorem map_id : map (@id α) = id := map_unique uniformContinuous_id rfl
theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm
end SeparationQuotient