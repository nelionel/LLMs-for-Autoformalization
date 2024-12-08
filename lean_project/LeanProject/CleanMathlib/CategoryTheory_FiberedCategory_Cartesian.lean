import Mathlib.CategoryTheory.FiberedCategory.HomLift
universe v₁ v₂ u₁ u₂
open CategoryTheory Functor Category IsHomLift
namespace CategoryTheory.Functor
variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
section
variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
class IsCartesian extends IsHomLift p f φ : Prop where
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'
class IsStronglyCartesian extends IsHomLift p f φ : Prop where
  universal_property' {a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'
end
namespace IsCartesian
variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]
section
variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']
protected noncomputable def map : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'
instance map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1
@[reassoc (attr := simp)]
lemma fac : IsCartesian.map p f φ φ' ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = IsCartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩
end
protected lemma ext (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl, map_uniq p f φ (ψ ≫ φ) ψ' h.symm]
@[simp]
lemma map_self : IsCartesian.map p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]
@[simps]
noncomputable def domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a where
  hom := IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp]
instance domainUniqueUpToIso_inv_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').hom :=
  domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'
instance domainUniqueUpToIso_hom_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').inv :=
  domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_comp_inv, assoc, hτ₂]
end IsCartesian
namespace IsStronglyCartesian
section
variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCartesian p f φ]
lemma universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f
instance isCartesian_of_isStronglyCartesian [p.IsStronglyCartesian f φ] : p.IsCartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'
section
variable {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f) (φ' : a' ⟶ b)
  [IsHomLift p f' φ']
noncomputable def map : a' ⟶ a :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'
instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1
@[reassoc (attr := simp)]
lemma fac : (map p f φ hf' φ') ≫ φ = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩
end
protected lemma ext (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
    {ψ ψ' : a' ⟶ a} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl, map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]
@[simp]
lemma map_self : map p f φ (id_comp f).symm φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]
@[reassoc (attr := simp)]
lemma map_comp_map {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
    {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ'' : a'' ⟶ b)
    [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f' φ' H' φ'' ≫ map p f φ H φ' =
      map p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [assoc, fac]
end
section
variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}
instance comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
    IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]
protected lemma of_comp [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p f φ] : IsStronglyCartesian p f φ where
  universal_property' := by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    use map p (f ≫ g) (φ ≫ ψ) (f' := h ≫ f ≫ g) rfl (τ ≫ ψ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · apply IsStronglyCartesian.ext p g ψ (h ≫ f) (by simp)
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]
end
section
variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)
instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom where
  universal_property' := by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by aesop_cat⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)
instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f φ :=
  @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  have inv_hom : φ' ≫ φ = 𝟙 b := fac p (p.map φ) φ _ (𝟙 b)
  refine ⟨?_, inv_hom⟩
  have h₁ : IsHomLift p (𝟙 (p.obj a)) (φ  ≫ φ') := by
    rw [← IsIso.hom_inv_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCartesian.ext p (p.map φ) φ (𝟙 (p.obj a))
  simp only [assoc, inv_hom, comp_id, id_comp]
end
section
variable {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
@[simps]
noncomputable def domainIsoOfBaseIso (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : a' ≅ a where
  hom := map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ
instance domainUniqueUpToIso_inv_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.hom (domainIsoOfBaseIso p h φ φ').hom :=
  domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'
instance domainUniqueUpToIso_hom_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.inv (domainIsoOfBaseIso p h φ φ').inv := by
  haveI : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ
end
end IsStronglyCartesian
end CategoryTheory.Functor