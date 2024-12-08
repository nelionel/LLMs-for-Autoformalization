import Mathlib.Topology.Hom.ContinuousEval
import Mathlib.Topology.ContinuousMap.Basic
open Set Filter TopologicalSpace Topology
namespace ContinuousMap
section CompactOpen
variable {α X Y Z T : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
variable {K : Set X} {U : Set Y}
instance compactOpen : TopologicalSpace C(X, Y) :=
  .generateFrom <| image2 (fun K U ↦ {f | MapsTo f K U}) {K | IsCompact K} {U | IsOpen U}
theorem compactOpen_eq : @compactOpen X Y _ _ =
    .generateFrom (image2 (fun K U ↦ {f | MapsTo f K U}) {K | IsCompact K} {t | IsOpen t}) :=
   rfl
theorem isOpen_setOf_mapsTo (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | MapsTo f K U} :=
  isOpen_generateFrom_of_mem <| mem_image2_of_mem hK hU
lemma eventually_mapsTo {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U) :
    ∀ᶠ g : C(X, Y) in 𝓝 f, MapsTo g K U :=
  (isOpen_setOf_mapsTo hK hU).mem_nhds h
lemma nhds_compactOpen (f : C(X, Y)) :
    𝓝 f = ⨅ (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U),
      𝓟 {g : C(X, Y) | MapsTo g K U} := by
  simp_rw [compactOpen_eq, nhds_generateFrom, mem_setOf_eq, @and_comm (f ∈ _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_setOf_eq]
lemma tendsto_nhds_compactOpen {l : Filter α} {f : α → C(Y, Z)} {g : C(Y, Z)} :
    Tendsto f l (𝓝 g) ↔
      ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → ∀ᶠ a in l, MapsTo (f a) K U := by
  simp [nhds_compactOpen]
lemma continuous_compactOpen {f : X → C(Y, Z)} :
    Continuous f ↔ ∀ K, IsCompact K → ∀ U, IsOpen U → IsOpen {x | MapsTo (f x) K U} :=
  continuous_generateFrom_iff.trans forall_image2_iff
section Functorial
theorem continuous_postcomp (g : C(Y, Z)) : Continuous (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  continuous_compactOpen.2 fun _K hK _U hU ↦ isOpen_setOf_mapsTo hK (hU.preimage g.2)
@[deprecated (since := "2024-10-19")] alias continuous_comp := continuous_postcomp
theorem isInducing_postcomp (g : C(Y, Z)) (hg : IsInducing g) :
    IsInducing (g.comp : C(X, Y) → C(X, Z)) where
  eq_induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOf_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_setOf_eq, comp_apply]
@[deprecated (since := "2024-10-28")] alias inducing_postcomp := isInducing_postcomp
@[deprecated (since := "2024-10-19")] alias inducing_comp := isInducing_postcomp
theorem isEmbedding_postcomp (g : C(Y, Z)) (hg : IsEmbedding g) :
    IsEmbedding (g.comp : C(X, Y) → C(X, Z)) :=
  ⟨isInducing_postcomp g hg.1, fun _ _ ↦ (cancel_left hg.2).1⟩
@[deprecated (since := "2024-10-26")]
alias embedding_postcomp := isEmbedding_postcomp
@[deprecated (since := "2024-10-19")] alias embedding_comp := isEmbedding_postcomp
@[continuity, fun_prop]
theorem continuous_precomp (f : C(X, Y)) : Continuous (fun g => g.comp f : C(Y, Z) → C(X, Z)) :=
  continuous_compactOpen.2 fun K hK U hU ↦ by
    simpa only [mapsTo_image_iff] using isOpen_setOf_mapsTo (hK.image f.2) hU
@[deprecated (since := "2024-10-19")] alias continuous_comp_left := continuous_precomp
variable (Z) in
@[simps apply]
def compRightContinuousMap (f : C(X, Y)) :
    C(C(Y, Z), C(X, Z)) where
  toFun g := g.comp f
protected def _root_.Homeomorph.arrowCongr (φ : X ≃ₜ Z) (ψ : Y ≃ₜ T) :
    C(X, Y) ≃ₜ C(Z, T) where
  toFun f := .comp ψ <| f.comp φ.symm
  invFun f := .comp ψ.symm <| f.comp φ
  left_inv f := ext fun _ ↦ ψ.left_inv (f _) |>.trans <| congrArg f <| φ.left_inv _
  right_inv f := ext fun _ ↦ ψ.right_inv (f _) |>.trans <| congrArg f <| φ.right_inv _
  continuous_toFun := continuous_postcomp _ |>.comp <| continuous_precomp _
  continuous_invFun := continuous_postcomp _ |>.comp <| continuous_precomp _
variable (Z) in
@[deprecated Homeomorph.arrowCongr (since := "2024-10-19")]
def compRightHomeomorph (f : X ≃ₜ Y) :
    C(Y, Z) ≃ₜ C(X, Z) :=
  .arrowCongr f.symm (.refl _)
variable [LocallyCompactPair Y Z]
theorem continuous_comp' : Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : ∃ L ∈ 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet, ← mapsTo'] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ ↦
      hg'.comp <| hf'.mono_right interior_subset
lemma _root_.Filter.Tendsto.compCM {α : Type*} {l : Filter α} {g : α → C(Y, Z)} {g₀ : C(Y, Z)}
    {f : α → C(X, Y)} {f₀ : C(X, Y)} (hg : Tendsto g l (𝓝 g₀)) (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun a ↦ (g a).comp (f a)) l (𝓝 (g₀.comp f₀)) :=
  (continuous_comp'.tendsto (f₀, g₀)).comp (hf.prod_mk_nhds hg)
variable {X' : Type*} [TopologicalSpace X'] {a : X'} {g : X' → C(Y, Z)} {f : X' → C(X, Y)}
  {s : Set X'}
nonrec lemma _root_.ContinuousAt.compCM (hg : ContinuousAt g a) (hf : ContinuousAt f a) :
    ContinuousAt (fun x ↦ (g x).comp (f x)) a :=
  hg.compCM hf
nonrec lemma _root_.ContinuousWithinAt.compCM (hg : ContinuousWithinAt g s a)
    (hf : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x ↦ (g x).comp (f x)) s a :=
  hg.compCM hf
lemma _root_.ContinuousOn.compCM (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ (g x).comp (f x)) s := fun a ha ↦
  (hg a ha).compCM (hf a ha)
lemma _root_.Continuous.compCM (hg : Continuous g) (hf : Continuous f) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prod_mk hg)
end Functorial
section Ev
instance [LocallyCompactPair X Y] : ContinuousEval C(X, Y) X Y where
  continuous_eval := by
    simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro ⟨f, x⟩ U ⟨hx : f x ∈ U, hU : IsOpen U⟩
    rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
    filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h ↦ h.1 h.2
@[deprecated (since := "2024-10-01")] protected alias continuous_eval := continuous_eval
instance : ContinuousEvalConst C(X, Y) X Y where
  continuous_eval_const x :=
    continuous_def.2 fun U hU ↦ by simpa using isOpen_setOf_mapsTo isCompact_singleton hU
@[deprecated (since := "2024-10-01")] protected alias continuous_eval_const := continuous_eval_const
@[deprecated continuous_coeFun (since := "2024-10-01")]
theorem continuous_coe : Continuous ((⇑) : C(X, Y) → (X → Y)) :=
  continuous_coeFun
lemma isClosed_setOf_mapsTo {t : Set Y} (ht : IsClosed t) (s : Set X) :
    IsClosed {f : C(X, Y) | MapsTo f s t} :=
  ht.setOf_mapsTo fun _ _ ↦ continuous_eval_const _
lemma isClopen_setOf_mapsTo (hK : IsCompact K) (hU : IsClopen U) :
    IsClopen {f : C(X, Y) | MapsTo f K U} :=
  ⟨isClosed_setOf_mapsTo hU.isClosed K, isOpen_setOf_mapsTo hK hU.isOpen⟩
@[norm_cast]
lemma specializes_coe {f g : C(X, Y)} : ⇑f ⤳ ⇑g ↔ f ⤳ g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map continuous_coeFun⟩
  suffices ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → MapsTo f K U by
    simpa [specializes_iff_pure, nhds_compactOpen]
  exact fun K _ U hU hg x hx ↦ (h.map (continuous_apply x)).mem_open hU (hg hx)
@[norm_cast]
lemma inseparable_coe {f g : C(X, Y)} : Inseparable (f : X → Y) g ↔ Inseparable f g := by
  simp only [inseparable_iff_specializes_and, specializes_coe]
instance [T0Space Y] : T0Space C(X, Y) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun
instance [R0Space Y] : R0Space C(X, Y) where
  specializes_symmetric f g h := by
    rw [← specializes_coe] at h ⊢
    exact h.symm
instance [T1Space Y] : T1Space C(X, Y) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun
instance [R1Space Y] : R1Space C(X, Y) :=
  .of_continuous_specializes_imp continuous_coeFun fun _ _ ↦ specializes_coe.1
instance [T2Space Y] : T2Space C(X, Y) := inferInstance
instance [RegularSpace Y] : RegularSpace C(X, Y) :=
  .of_lift'_closure_le fun f ↦ by
    rw [← tendsto_id', tendsto_nhds_compactOpen]
    intro K hK U hU hf
    rcases (hK.image f.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 hf.image_subset)
      with ⟨V, hVo, hKV, hVU⟩
    filter_upwards [mem_lift' (eventually_mapsTo hK hVo (mapsTo'.2 hKV))] with g hg
    refine ((isClosed_setOf_mapsTo isClosed_closure K).closure_subset ?_).mono_right hVU
    exact closure_mono (fun _ h ↦ h.mono_right subset_closure) hg
instance [T3Space Y] : T3Space C(X, Y) := inferInstance
end Ev
section InfInduced
theorem continuous_restrict (s : Set X) : Continuous fun F : C(X, Y) => F.restrict s :=
  continuous_precomp <| restrict s <| .id X
theorem compactOpen_le_induced (s : Set X) :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) ≤
      .induced (restrict s) ContinuousMap.compactOpen :=
  (continuous_restrict s).le_induced
theorem compactOpen_eq_iInf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) =
      ⨅ (K : Set X) (_ : IsCompact K), .induced (.restrict K) ContinuousMap.compactOpen := by
  refine le_antisymm (le_iInf₂ fun s _ ↦ compactOpen_le_induced s) ?_
  refine le_generateFrom <| forall_image2_iff.2 fun K (hK : IsCompact K) U hU ↦ ?_
  refine TopologicalSpace.le_def.1 (iInf₂_le K hK) _ ?_
  convert isOpen_induced (isOpen_setOf_mapsTo (isCompact_iff_isCompact_univ.1 hK) hU)
  simp [mapsTo_univ_iff, Subtype.forall, MapsTo]
@[deprecated (since := "2024-03-05")]
alias compactOpen_eq_sInf_induced := compactOpen_eq_iInf_induced
theorem nhds_compactOpen_eq_iInf_nhds_induced (f : C(X, Y)) :
    𝓝 f = ⨅ (s) (_ : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compactOpen_eq_iInf_induced]
  simp only [nhds_iInf, nhds_induced]
@[deprecated (since := "2024-03-05")]
alias nhds_compactOpen_eq_sInf_nhds_induced := nhds_compactOpen_eq_iInf_nhds_induced
theorem tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι → C(X, Y)} {f : C(X, Y)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set X) :
    Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).continuousAt.tendsto.comp hFf
theorem tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι → C(X, Y)) (f : C(X, Y)) :
    Tendsto F l (𝓝 f) ↔
      ∀ K, IsCompact K → Tendsto (fun i => (F i).restrict K) l (𝓝 (f.restrict K)) := by
  rw [compactOpen_eq_iInf_induced]
  simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp_def]
theorem exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Space Y]
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι → C(X, Y)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
      ∀ s : Set X, IsCompact s → ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) := by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      haveI := isCompact_iff_compactSpace.mp hs₁
      haveI := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs
end InfInduced
section Coev
variable (X Y)
@[simps (config := .asFn)]
def coev (b : Y) : C(X, Y × X) :=
  { toFun := Prod.mk b }
variable {X Y}
theorem image_coev {y : Y} (s : Set X) : coev X Y y '' s = {y} ×ˢ s := by simp
theorem continuous_coev : Continuous (coev X Y) := by
  have : ∀ {a K U}, MapsTo (coev X Y a) K U ↔ {a} ×ˢ K ⊆ U := by simp [mapsTo']
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen, this]
  intro x K hK U hU hKU
  rcases generalized_tube_lemma isCompact_singleton hK hU hKU with ⟨V, W, hV, -, hxV, hKW, hVWU⟩
  filter_upwards [hV.mem_nhds (hxV rfl)] with a ha
  exact (prod_mono (singleton_subset_iff.mpr ha) hKW).trans hVWU
end Coev
section Curry
def curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) where
  toFun a := ⟨Function.curry f a, f.continuous.comp <| by fun_prop⟩
  continuous_toFun := (continuous_postcomp f).comp continuous_coev
@[simp]
theorem curry_apply (f : C(X × Y, Z)) (a : X) (b : Y) : f.curry a b = f (a, b) :=
  rfl
@[deprecated ContinuousMap.curry (since := "2024-03-05")]
def curry' (f : C(X × Y, Z)) (a : X) : C(Y, Z) := curry f a
set_option linter.deprecated false in
@[deprecated ContinuousMap.curry (since := "2024-03-05")]
theorem continuous_curry' (f : C(X × Y, Z)) : Continuous (curry' f) := (curry f).continuous
theorem continuous_of_continuous_uncurry (f : X → C(Y, Z))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  (curry ⟨_, h⟩).2
theorem continuous_curry [LocallyCompactSpace (X × Y)] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval.comp <| f.continuous.prodMap continuous_id
@[simps]
def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  dsimp [Function.comp_def]
  exact (continuous_fst.fst.eval continuous_fst.snd).eval continuous_snd
def const' : C(Y, C(X, Y)) :=
  curry ContinuousMap.fst
@[simp]
theorem coe_const' : (const' : Y → C(X, Y)) = const X :=
  rfl
theorem continuous_const' : Continuous (const X : Y → C(X, Y)) :=
  const'.continuous
end Curry
end CompactOpen
end ContinuousMap
open ContinuousMap
namespace Homeomorph
variable {X : Type*} {Y : Type*} {Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
def curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩
def continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where
  toFun := const X
  invFun f := f default
  left_inv _ := rfl
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _
@[simp]
theorem continuousMapOfUnique_apply [Unique X] (y : Y) (x : X) : continuousMapOfUnique y x = y :=
  rfl
@[simp]
theorem continuousMapOfUnique_symm_apply [Unique X] (f : C(X, Y)) :
    continuousMapOfUnique.symm f = f default :=
  rfl
end Homeomorph
section IsQuotientMap
variable {X₀ X Y Z : Type*} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ → X}
theorem Topology.IsQuotientMap.continuous_lift_prod_left (hf : IsQuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
@[deprecated (since := "2024-10-22")]
alias QuotientMap.continuous_lift_prod_left := IsQuotientMap.continuous_lift_prod_left
theorem Topology.IsQuotientMap.continuous_lift_prod_right (hf : IsQuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap
@[deprecated (since := "2024-10-22")]
alias QuotientMap.continuous_lift_prod_right := IsQuotientMap.continuous_lift_prod_right
end IsQuotientMap