import Mathlib.CategoryTheory.Sites.OneHypercover
universe w v v' u u'
namespace CategoryTheory
open Category Limits
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A]
namespace GrothendieckTopology
abbrev OneHypercoverFamily := ∀ ⦃X : C⦄, OneHypercover.{w} J X → Prop
namespace OneHypercoverFamily
variable {J}
variable (H : OneHypercoverFamily.{w} J)
class IsGenerating : Prop where
  le {X : C} (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S
lemma exists_oneHypercover [H.IsGenerating] {X : C} (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S :=
  IsGenerating.le _ hS
variable (P : Cᵒᵖ ⥤ A)
namespace IsSheafIff
variable (hP : ∀ ⦃X : C⦄ (E : J.OneHypercover X) (_ : H E), Nonempty (IsLimit (E.multifork P)))
include hP in
lemma hom_ext [H.IsGenerating] {X : C} (S : Sieve X) (hS : S ∈ J X) {T : A}
    {x y : T ⟶ P.obj (Opposite.op X)}
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), x ≫ P.map f.op = y ≫ P.map f.op) :
    x = y := by
  obtain ⟨E, hE, le⟩ := H.exists_oneHypercover S hS
  exact Multifork.IsLimit.hom_ext (hP E hE).some (fun j => h _ (le _ (Sieve.ofArrows_mk _ _ _)))
variable {P H}
variable {X : C} {S : Sieve X} {E : J.OneHypercover X} (hE : H E) (le : E.sieve₀ ≤ S)
section
variable (F : Multifork (Cover.index ⟨S, J.superset_covering le E.mem₀⟩ P))
noncomputable def lift : F.pt ⟶ P.obj (Opposite.op X) :=
  Multifork.IsLimit.lift (hP E hE).some
    (fun i => F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩)
    (fun ⟨⟨i₁, i₂⟩, j⟩ =>
      F.condition (Cover.Relation.mk { hf := le _ (Sieve.ofArrows_mk _ _ i₁) }
        { hf := le _ (Sieve.ofArrows_mk _ _ i₂) } { w := E.w j} ))
@[reassoc]
lemma fac' (i : E.I₀) :
    lift hP hE le F ≫ P.map (E.f i).op =
      F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩ :=
  Multifork.IsLimit.fac (hP E hE).some _ _ i
lemma fac [H.IsGenerating] {Y : C} (f : Y ⟶ X) (hf : S f) :
    lift hP hE le F ≫ P.map f.op = F.ι ⟨Y, f, hf⟩ := by
  apply hom_ext H P hP _ (J.pullback_stable f E.mem₀)
  intro Z g
  rintro ⟨T, a, b, hb, fac⟩
  cases' hb with i
  rw [assoc, ← P.map_comp, ← op_comp, ← fac,
    op_comp, P.map_comp, fac'_assoc]
  exact F.condition (Cover.Relation.mk { hf := le _ (Sieve.ofArrows_mk _ _ _) }
    { hf := hf } { w := fac })
end
noncomputable def isLimit [H.IsGenerating] :
    IsLimit (Cover.multifork ⟨S, J.superset_covering le E.mem₀⟩ P) :=
  Multifork.IsLimit.mk _
    (fun F => lift hP hE le F)
    (fun F => by
      rintro ⟨Y, f, hf⟩
      apply fac)
    (fun F m hm => by
      apply hom_ext H P hP S (J.superset_covering le E.mem₀)
      intro Y f hf
      rw [fac _ _ _ _ _ hf]
      exact hm ⟨_, _, hf⟩)
end IsSheafIff
lemma isSheaf_iff [H.IsGenerating] :
    Presheaf.IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : J.OneHypercover X)
      (_ : H E), Nonempty (IsLimit (E.multifork P)) := by
  constructor
  · intro hP X E _
    exact ⟨E.isLimitMultifork ⟨_, hP⟩⟩
  · intro hP
    rw [Presheaf.isSheaf_iff_multifork]
    rintro X ⟨S, hS⟩
    obtain ⟨E, hE, le⟩ := H.exists_oneHypercover S hS
    exact ⟨IsSheafIff.isLimit hP hE le⟩
end OneHypercoverFamily
abbrev IsGeneratedByOneHypercovers : Prop :=
  OneHypercoverFamily.IsGenerating.{w} (J := J) ⊤
instance : IsGeneratedByOneHypercovers.{max u v} J where
  le S hS := ⟨Cover.oneHypercover ⟨S, hS⟩, by simp, by simp⟩
end GrothendieckTopology
namespace Presheaf
lemma isSheaf_iff_of_isGeneratedByOneHypercovers
    [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] (P : Cᵒᵖ ⥤ A) :
    IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : GrothendieckTopology.OneHypercover.{w} J X),
        Nonempty (IsLimit (E.multifork P)) := by
  simpa using GrothendieckTopology.OneHypercoverFamily.isSheaf_iff.{w} ⊤ P
end Presheaf
end CategoryTheory