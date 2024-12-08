import Mathlib.CategoryTheory.FiberedCategory.Cartesian
universe v₁ v₂ u₁ u₂
open CategoryTheory Functor Category IsHomLift
namespace CategoryTheory
variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCartesian' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ
protected lemma IsPreFibered.exists_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.exists_isCartesian' f
class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) extends IsPreFibered p : Prop where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)
instance (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ) :=
  IsFibered.comp f g φ ψ
namespace Functor.IsPreFibered
open IsCartesian
variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)
noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreFibered.exists_isCartesian p ha f)
noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))
instance pullbackMap.IsCartesian : IsCartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))
lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)
end Functor.IsPreFibered
namespace Functor.IsFibered
open IsCartesian IsPreFibered
instance isStronglyCartesian_of_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ where
  universal_property' g φ' hφ' := by
    let ψ := pullbackMap (domain_eq p f φ) g
    let τ := IsCartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    refine ⟨⟨inferInstance, by simp only [assoc, IsCartesian.fac, τ]⟩, ?_⟩
    intro π ⟨hπ, hπ_comp⟩
    rw [← fac p g ψ π]
    congr 1
    apply map_uniq
    rwa [← assoc, IsCartesian.fac]
lemma isStronglyCartesian_of_exists_isCartesian (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (R : 𝒮)
    (f : R ⟶ p.obj a), ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) {R S : 𝒮} (f : R ⟶ S)
      {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  let τ' := IsStronglyCartesian.map p (p.map φ) ψ (f':= g ≫ p.map φ) rfl φ'
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  use τ' ≫ Φ.hom
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ, IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ']
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]
lemma of_exists_isStronglyCartesian {p : 𝒳 ⥤ 𝒮}
    (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
      ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) :
    IsFibered p where
  exists_isCartesian' := by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCartesian f φ := isStronglyCartesian_of_exists_isCartesian p h _ _
    have : p.IsStronglyCartesian g ψ := isStronglyCartesian_of_exists_isCartesian p h _ _
    inferInstance
noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p]
    {R S T : 𝒮}  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))
end Functor.IsFibered
end CategoryTheory