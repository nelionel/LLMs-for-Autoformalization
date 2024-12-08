import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.IsSheafFor
universe w v u
namespace CategoryTheory
open Opposite CategoryTheory Category Limits Sieve
namespace Presieve
variable {C : Type u} [Category.{v} C]
variable {P : Cᵒᵖ ⥤ Type w}
variable {X : C}
variable (J J₂ : GrothendieckTopology C)
def IsSeparated (P : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ {X} (S : Sieve X), S ∈ J X → IsSeparatedFor P (S : Presieve X)
def IsSheaf (P : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃X⦄ (S : Sieve X), S ∈ J X → IsSheafFor P (S : Presieve X)
theorem IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ Type w} (hp : IsSheaf J P) (R : Presieve X)
    (hr : generate R ∈ J X) : IsSheafFor P R :=
  (isSheafFor_iff_generate R).2 <| hp _ hr
theorem isSheaf_of_le (P : Cᵒᵖ ⥤ Type w) {J₁ J₂ : GrothendieckTopology C} :
    J₁ ≤ J₂ → IsSheaf J₂ P → IsSheaf J₁ P := fun h t _ S hS => t S (h _ hS)
theorem isSeparated_of_isSheaf (P : Cᵒᵖ ⥤ Type w) (h : IsSheaf J P) : IsSeparated J P :=
  fun S hS => (h S hS).isSeparatedFor
theorem isSheaf_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (h : IsSheaf J P) : IsSheaf J P' :=
  fun _ S hS => isSheafFor_iso i (h S hS)
theorem isSheaf_of_yoneda {P : Cᵒᵖ ⥤ Type v}
    (h : ∀ {X} (S : Sieve X), S ∈ J X → YonedaSheafCondition P S) : IsSheaf J P := fun _ _ hS =>
  isSheafFor_iff_yonedaSheafCondition.2 (h _ hS)
theorem isSheaf_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf (K.toGrothendieck C) P ↔ ∀ {X : C} (R : Presieve X), R ∈ K X → IsSheafFor P R := by
  constructor
  · intro PJ X R hR
    rw [isSheafFor_iff_generate]
    apply PJ (Sieve.generate R) ⟨_, hR, le_generate R⟩
  · rintro PK X S ⟨R, hR, RS⟩
    have gRS : ⇑(generate R) ≤ S := by
      apply giGenerate.gc.monotone_u
      rwa [generate_le_iff]
    apply isSheafFor_subsieve P gRS _
    intro Y f
    rw [← pullbackArrows_comm, ← isSheafFor_iff_generate]
    exact PK (pullbackArrows f R) (K.pullbacks f R hR)
theorem isSheaf_bot : IsSheaf (⊥ : GrothendieckTopology C) P := fun X => by
  simp [isSheafFor_top_sieve]
def compatibleYonedaFamily_toCocone (R : Presieve X) (W : C) (x : FamilyOfElements (yoneda.obj W) R)
    (hx : FamilyOfElements.Compatible x) :
    Cocone (R.diagram) where
  pt := W
  ι :=
    { app := fun f => x f.obj.hom f.property
      naturality := by
        intro g₁ g₂ F
        simp only [Functor.id_obj, Functor.comp_obj, fullSubcategoryInclusion.obj, Over.forget_obj,
          Functor.const_obj_obj, Functor.comp_map, fullSubcategoryInclusion.map, Over.forget_map,
          Functor.const_obj_map, Category.comp_id]
        rw [← Category.id_comp (x g₁.obj.hom g₁.property)]
        apply hx
        simp only [Functor.id_obj, Over.w, Opposite.unop_op, Category.id_comp] }
def yonedaFamilyOfElements_fromCocone (R : Presieve X) (s : Cocone (diagram R)) :
    FamilyOfElements (yoneda.obj s.pt) R :=
  fun _ f hf => s.ι.app ⟨Over.mk f, hf⟩
end Presieve
namespace Sieve
open Presieve
variable {C : Type u} [Category.{v} C]
variable {X : C}
theorem yonedaFamily_fromCocone_compatible (S : Sieve X) (s : Cocone (diagram S.arrows)) :
    FamilyOfElements.Compatible <| yonedaFamilyOfElements_fromCocone S.arrows s := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hgf
  have Hs := s.ι.naturality
  simp only [Functor.id_obj, yoneda_obj_obj, Opposite.unop_op, yoneda_obj_map, Quiver.Hom.unop_op]
  dsimp [yonedaFamilyOfElements_fromCocone]
  have hgf₁ : S.arrows (g₁ ≫ f₁) := by exact Sieve.downward_closed S hf₁ g₁
  have hgf₂ : S.arrows (g₂ ≫ f₂) := by exact Sieve.downward_closed S hf₂ g₂
  let F : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk (g₂ ≫ f₂) : Over X) := Over.homMk (𝟙 Z)
  let F₁ : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk f₁ : Over X) := Over.homMk g₁
  let F₂ : (Over.mk (g₂ ≫ f₂) : Over X) ⟶ (Over.mk f₂ : Over X) := Over.homMk g₂
  have hF := @Hs ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ F
  have hF₁ := @Hs ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk f₁, hf₁⟩ F₁
  have hF₂ := @Hs ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ ⟨Over.mk f₂, hf₂⟩ F₂
  aesop_cat
theorem forallYonedaIsSheaf_iff_colimit (S : Sieve X) :
    (∀ W : C, Presieve.IsSheafFor (yoneda.obj W) (S : Presieve X)) ↔
      Nonempty (IsColimit S.arrows.cocone) := by
  constructor
  · intro H
    refine Nonempty.intro ?_
    exact
    { desc := fun s => H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
        (yonedaFamily_fromCocone_compatible S s) |>.choose
      fac := by
        intro s f
        replace H := H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
          (yonedaFamily_fromCocone_compatible S s)
        have ht := H.choose_spec.1 f.obj.hom f.property
        aesop_cat
      uniq := by
        intro s Fs HFs
        replace H := H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
          (yonedaFamily_fromCocone_compatible S s)
        apply H.choose_spec.2 Fs
        exact fun _ f hf => HFs ⟨Over.mk f, hf⟩ }
  · intro H W x hx
    replace H := Classical.choice H
    let s := compatibleYonedaFamily_toCocone S.arrows W x hx
    use H.desc s
    constructor
    · exact fun _ f hf => (H.fac s) ⟨Over.mk f, hf⟩
    · exact fun g hg => H.uniq s g (fun ⟨⟨f, _, hom⟩, hf⟩ => hg hom hf)
end Sieve
end CategoryTheory