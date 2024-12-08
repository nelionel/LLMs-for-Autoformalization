import Mathlib.CategoryTheory.Sites.Sheaf
universe v u
namespace CategoryTheory
open scoped Classical
open CategoryTheory Category Limits Sieve
variable {C : Type u} [Category.{v} C]
namespace Sheaf
variable {P : Cᵒᵖ ⥤ Type v} {X : C} (J : GrothendieckTopology C)
theorem isSheafFor_bind (P : Cᵒᵖ ⥤ Type v) (U : Sieve X) (B : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → Sieve Y)
    (hU : Presieve.IsSheafFor P (U : Presieve X))
    (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf : Presieve Y))
    (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y),
      Presieve.IsSeparatedFor P (((B h).pullback g) : Presieve Z)) :
    Presieve.IsSheafFor P (Sieve.bind (U : Presieve X) B : Presieve X) := by
  intro s hs
  let y : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply hs
    apply reassoc_of% comm
  let t : Presieve.FamilyOfElements P (U : Presieve X) :=
    fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).IsAmalgamation (t f hf) := fun Y f hf =>
    (hB hf).isAmalgamation _
  have hT : t.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W f h hf
    apply (hB (U.downward_closed hf h)).isSeparatedFor.ext
    intro Y l hl
    apply (hB' hf (l ≫ h)).ext
    intro M m hm
    have : bind U B (m ≫ l ≫ h ≫ f) := by simpa using (Presieve.bind_comp f hf hm : bind U B _)
    trans s (m ≫ l ≫ h ≫ f) this
    · have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
      rw [op_comp, FunctorToTypes.map_comp_apply] at this
      rw [this]
      change s _ _ = s _ _
      congr 1
      simp only [assoc]
    · have h : s _ _ = _ := (ht hf _ hm).symm
      conv_lhs at h => congr; rw [assoc, assoc]
      rw [h]
      simp only [op_comp, assoc, FunctorToTypes.map_comp_apply]
  refine ⟨hU.amalgamate t hT, ?_, ?_⟩
  · rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
    rw [op_comp, FunctorToTypes.map_comp_apply, Presieve.IsSheafFor.valid_glue _ _ _ hg]
    apply ht hg _ hf
  · intro y hy
    apply hU.isSeparatedFor.ext
    intro Y f hf
    apply (hB hf).isSeparatedFor.ext
    intro Z g hg
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hy _ (Presieve.bind_comp _ _ hg),
      hU.valid_glue _ _ hf, ht hf _ hg]
theorem isSheafFor_trans (P : Cᵒᵖ ⥤ Type v) (R S : Sieve X)
    (hR : Presieve.IsSheafFor P (R : Presieve X))
    (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSeparatedFor P (R.pullback f : Presieve Y))
    (hS : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), Presieve.IsSheafFor P (S.pullback f : Presieve Y)) :
    Presieve.IsSheafFor P (S : Presieve X) := by
  have : (bind R fun Y f _ => S.pullback f : Presieve X) ≤ S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← pullback_comp]
    apply (hS (R.downward_closed hf _)).isSeparatedFor
  · intro Y f hf
    have : Sieve.pullback f (bind R fun T (k : T ⟶ X) (_ : R k) => pullback k S) =
        R.pullback f := by
      ext Z g
      constructor
      · rintro ⟨W, k, l, hl, _, comm⟩
        rw [pullback_apply, ← comm]
        simp [hl]
      · intro a
        refine ⟨Z, 𝟙 Z, _, a, ?_⟩
        simp [hf]
    rw [this]
    apply hR' hf
def finestTopologySingle (P : Cᵒᵖ ⥤ Type v) : GrothendieckTopology C where
  sieves X S := ∀ (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top_sieve P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    refine isSheafFor_trans P (pullback g S) _ (hS Z g) ?_ ?_
    · intro Y f _
      rw [← pullback_comp]
      apply (hS _ _).isSeparatedFor
    · intro Y f hf
      have := hR hf _ (𝟙 _)
      rw [pullback_id, pullback_comp] at this
      apply this
def finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) : GrothendieckTopology C :=
  sInf (finestTopologySingle '' Ps)
theorem sheaf_for_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (h : P ∈ Ps) :
    Presieve.IsSheaf (finestTopology Ps) P := fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)
theorem le_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (J : GrothendieckTopology C)
    (hJ : ∀ P ∈ Ps, Presieve.IsSheaf J P) : J ≤ finestTopology Ps := by
  rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
  intro Y f
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS)
def canonicalTopology (C : Type u) [Category.{v} C] : GrothendieckTopology C :=
  finestTopology (Set.range yoneda.obj)
theorem isSheaf_yoneda_obj (X : C) : Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  fun _ _ hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS
theorem isSheaf_of_isRepresentable (P : Cᵒᵖ ⥤ Type v) [P.IsRepresentable] :
    Presieve.IsSheaf (canonicalTopology C) P :=
  Presieve.isSheaf_iso (canonicalTopology C) P.reprW (isSheaf_yoneda_obj _)
end Sheaf
namespace GrothendieckTopology
open Sheaf
class Subcanonical (J : GrothendieckTopology C) : Prop where
  le_canonical : J ≤ canonicalTopology C
lemma le_canonical (J : GrothendieckTopology C) [Subcanonical J] : J ≤ canonicalTopology C :=
  Subcanonical.le_canonical
instance : (canonicalTopology C).Subcanonical where
  le_canonical := le_rfl
namespace Subcanonical
theorem of_isSheaf_yoneda_obj (J : GrothendieckTopology C)
    (h : ∀ X, Presieve.IsSheaf J (yoneda.obj X)) : Subcanonical J where
  le_canonical := le_finestTopology _ _ (by rintro P ⟨X, rfl⟩; apply h)
theorem isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J]
    (P : Cᵒᵖ ⥤ Type v) [P.IsRepresentable] : Presieve.IsSheaf J P :=
  Presieve.isSheaf_of_le _ J.le_canonical (Sheaf.isSheaf_of_isRepresentable P)
variable {J : GrothendieckTopology C}
end Subcanonical
variable (J : GrothendieckTopology C)
@[simps]
def yoneda [J.Subcanonical] : C ⥤ Sheaf J (Type v) where
  obj X := ⟨CategoryTheory.yoneda.obj X, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subcanonical.isSheaf_of_isRepresentable⟩
  map f := ⟨CategoryTheory.yoneda.map f⟩
variable [Subcanonical J]
def yonedaCompSheafToPresheaf :
    J.yoneda ⋙ sheafToPresheaf J (Type v) ≅ CategoryTheory.yoneda :=
  Iso.refl _
def yonedaFullyFaithful : (J.yoneda).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (Type v)) Yoneda.fullyFaithful
instance : (J.yoneda).Full := (J.yonedaFullyFaithful).full
instance : (J.yoneda).Faithful := (J.yonedaFullyFaithful).faithful
end GrothendieckTopology
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical := GrothendieckTopology.Subcanonical
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical.of_isSheaf_yoneda_obj :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical.isSheaf_of_isRepresentable :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical.yoneda :=
  GrothendieckTopology.yoneda
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical.yonedaCompSheafToPresheaf :=
  GrothendieckTopology.yonedaCompSheafToPresheaf
@[deprecated (since := "2024-10-29")] alias Sheaf.Subcanonical.yonedaFullyFaithful :=
  GrothendieckTopology.yonedaFullyFaithful
end CategoryTheory