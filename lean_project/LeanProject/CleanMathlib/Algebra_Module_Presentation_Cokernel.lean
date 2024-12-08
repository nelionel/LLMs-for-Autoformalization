import Mathlib.Algebra.Module.Presentation.Basic
universe w w₁ w₂₀ w₂₁ v₁ v₂ v₃ u
namespace Module
variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]
namespace Presentation
section Cokernel
variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)
structure CokernelData where
  lift (i : ι) : pres₂.G →₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)
@[simps]
def CokernelData.ofSection (s : M₂ → (pres₂.G →₀ A))
    (hs : ∀ (m₂ : M₂), pres₂.π (s m₂) = m₂) :
    pres₂.CokernelData f g₁ where
  lift i := s (f (g₁ i))
  π_lift i := by simp [hs]
instance nonempty_cokernelData :
    Nonempty (pres₂.CokernelData f g₁) := by
  obtain ⟨s, hs⟩ := pres₂.surjective_π.hasRightInverse
  exact ⟨CokernelData.ofSection _ _ _ s hs⟩
variable {g₁ f} (data : pres₂.CokernelData f g₁)
@[simps]
def cokernelRelations : Relations A where
  G := pres₂.G
  R := Sum pres₂.R ι
  relation x := match x with
    | .inl r => pres₂.relation r
    | .inr i => data.lift i
@[simps]
def cokernelSolution :
    (pres₂.cokernelRelations data).Solution (M₂ ⧸ LinearMap.range f) where
  var g := Submodule.mkQ _ (pres₂.var g)
  linearCombination_var_relation := by
    intro x
    erw [← Finsupp.apply_linearCombination]
    obtain (r | i) := x
    · erw [pres₂.linearCombination_var_relation]
      dsimp
    · erw [data.π_lift]
      simp
variable (hg₁ : Submodule.span A (Set.range g₁) = ⊤)
namespace cokernelSolution
noncomputable def isPresentationCore :
    Relations.Solution.IsPresentationCore.{w}
      (pres₂.cokernelSolution data) where
  desc s := (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r ↦ s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map, ← hg₁, Submodule.map_span, Submodule.span_le,
            Set.image_subset_iff]
          rintro _ ⟨i, rfl⟩
          rw [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, ← data.π_lift,
            Relations.Solution.IsPresentation.π_desc_apply]
          exact s.linearCombination_var_relation (.inr i))
  postcomp_desc s := by aesop
  postcomp_injective h := by
    ext : 1
    apply pres₂.toIsPresentation.postcomp_injective
    ext g
    exact Relations.Solution.congr_var h g
include hg₁ in
lemma isPresentation : (pres₂.cokernelSolution data).IsPresentation :=
  (isPresentationCore pres₂ data hg₁).isPresentation
end cokernelSolution
@[simps!]
def cokernel : Presentation A (M₂ ⧸ LinearMap.range f) :=
  ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)
end Cokernel
@[simps!]
noncomputable def ofExact {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}
    (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) {ι : Type w₁} {g₁ : ι → M₁}
    (data : pres₂.CokernelData f g₁)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hg₁ : Submodule.span A (Set.range g₁) = ⊤) :
    Presentation A M₃ :=
  (pres₂.cokernel data hg₁).ofLinearEquiv (hfg.linearEquivOfSurjective hg)
end Presentation
end Module