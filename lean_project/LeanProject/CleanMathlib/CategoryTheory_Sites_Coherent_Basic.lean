import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.EffectiveEpi.Basic
namespace CategoryTheory
open Limits
variable (C : Type*) [Category C]
class Precoherent : Prop where
  pullback {B₁ B₂ : C} (f : B₂ ⟶ B₁) :
    ∀ (α : Type) [Finite α] (X₁ : α → C) (π₁ : (a : α) → (X₁ a ⟶ B₁)),
      EffectiveEpiFamily X₁ π₁ →
    ∃ (β : Type) (_ : Finite β) (X₂ : β → C) (π₂ : (b : β) → (X₂ b ⟶ B₂)),
      EffectiveEpiFamily X₂ π₂ ∧
      ∃ (i : β → α) (ι : (b :  β) → (X₂ b ⟶ X₁ (i b))),
      ∀ (b : β), ι b ≫ π₁ _ = π₂ _ ≫ f
def coherentCoverage [Precoherent C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Finite α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ EffectiveEpiFamily X π }
  pullback := by
    rintro B₁ B₂ f S ⟨α, _, X₁, π₁, rfl, hS⟩
    obtain ⟨β,_,X₂,π₂,h,i,ι,hh⟩ := Precoherent.pullback f α X₁ π₁ hS
    refine ⟨Presieve.ofArrows X₂ π₂, ⟨β, inferInstance, X₂, π₂, rfl, h⟩, ?_⟩
    rintro _ _ ⟨b⟩
    exact ⟨(X₁ (i b)), ι _, π₁ _, ⟨_⟩, hh _⟩
def coherentTopology [Precoherent C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| coherentCoverage C
class Preregular : Prop where
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk
def regularTopology [Preregular C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| regularCoverage C
def extensiveCoverage [FinitaryPreExtensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Finite α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst _ _
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, FinitaryPreExtensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd _ _, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      exact Presieve.ofArrows.mk a
def extensiveTopology [FinitaryPreExtensive C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| extensiveCoverage C
end CategoryTheory