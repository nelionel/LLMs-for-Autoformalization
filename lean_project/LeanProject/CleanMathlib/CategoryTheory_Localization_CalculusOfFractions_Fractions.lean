import Mathlib.CategoryTheory.Localization.CalculusOfFractions
namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]
namespace MorphismProperty
structure LeftFraction₂ (X Y : C) where
  {Y' : C}
  f : X ⟶ Y'
  f' : X ⟶ Y'
  s : Y ⟶ Y'
  hs : W s
structure LeftFraction₃ (X Y : C) where
  {Y' : C}
  f : X ⟶ Y'
  f' : X ⟶ Y'
  f'' : X ⟶ Y'
  s : Y ⟶ Y'
  hs : W s
structure RightFraction₂ (X Y : C) where
  {X' : C}
  s : X' ⟶ X
  hs : W s
  f : X' ⟶ Y
  f' : X' ⟶ Y
variable {W}
def LeftFraction₂Rel {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y) : Prop :=
  ∃ (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)
namespace LeftFraction₂
variable {X Y : C} (φ : W.LeftFraction₂ X Y)
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs
abbrev symm : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs
end LeftFraction₂
namespace LeftFraction₃
variable {X Y : C} (φ : W.LeftFraction₃ X Y)
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs
abbrev thd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs
abbrev forgetFst : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs
abbrev forgetSnd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs
abbrev forgetThd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs
end LeftFraction₃
namespace LeftFraction₂Rel
variable {X Y : C} {z₁ z₂ : W.LeftFraction₂ X Y}
lemma fst (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst := by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩
lemma snd (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd := by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩
end LeftFraction₂Rel
namespace LeftFraction₂
variable (W)
variable [W.HasLeftCalculusOfFractions]
lemma map_eq_iff {X Y : C} (φ ψ : W.LeftFraction₂ X Y) :
    (φ.fst.map L (Localization.inverts _ _) = ψ.fst.map L (Localization.inverts _ _) ∧
    φ.snd.map L (Localization.inverts _ _) = ψ.snd.map L (Localization.inverts _ _)) ↔
      LeftFraction₂Rel φ ψ := by
  simp only [LeftFraction.map_eq_iff L W]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    obtain ⟨Z', t₁', t₂', hst', hft', ht'⟩ := h'
    dsimp at t₁ t₂ t₁' t₂' hst hft hst' hft' ht ht'
    have ⟨α, hα⟩ := (RightFraction.mk _ ht (φ.s ≫ t₁')).exists_leftFraction
    simp only [Category.assoc] at hα
    obtain ⟨Z'', u, hu, fac⟩ := HasLeftCalculusOfFractions.ext _ _ _ φ.hs hα
    have hα' : ψ.s ≫ t₂ ≫ α.f ≫ u = ψ.s ≫ t₂' ≫ α.s ≫ u := by
      rw [← reassoc_of% hst, ← reassoc_of% hα, ← reassoc_of% hst']
    obtain ⟨Z''', u', hu', fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ ψ.hs hα'
    simp only [Category.assoc] at fac fac'
    refine ⟨Z''', t₁' ≫ α.s ≫ u ≫ u', t₂' ≫ α.s ≫ u ≫ u', ?_, ?_, ?_, ?_⟩
    · rw [reassoc_of% hst']
    · rw [reassoc_of% fac, reassoc_of% hft, fac']
    · rw [reassoc_of% hft']
    · rw [← Category.assoc]
      exact W.comp_mem _ _ ht' (W.comp_mem _ _ α.hs (W.comp_mem _ _ hu hu'))
  · intro h
    exact ⟨h.fst, h.snd⟩
end LeftFraction₂
namespace RightFraction₂
variable {X Y : C}
variable (φ : W.RightFraction₂ X Y)
abbrev fst : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs
abbrev snd : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs
lemma exists_leftFraction₂ [W.HasLeftCalculusOfFractions] :
    ∃ (ψ : W.LeftFraction₂ X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f ∧
      φ.f' ≫ ψ.s = φ.s ≫ ψ.f' := by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_⟩
  · dsimp
    rw [hα, reassoc_of% hψ₁]
  · rw [reassoc_of% hψ₂]
end RightFraction₂
end MorphismProperty
namespace Localization
variable [W.HasLeftCalculusOfFractions]
open MorphismProperty
lemma exists_leftFraction₂ {X Y : C} (f f' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₂ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) := by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_mem _ _ φ'.hs α.hs }
  have := inverts L W _ φ'.hs
  have := inverts L W _ α.hs
  have : IsIso (L.map (φ'.s ≫ α.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), LeftFraction.map_comp_map_s,
      hα, L.map_comp, hφ, LeftFraction.map_comp_map_s_assoc,
      L.map_comp]
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), hφ']
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc, LeftFraction.map_comp_map_s,
      L.map_comp]
lemma exists_leftFraction₃ {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₃ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) ∧
      f'' = φ.thd.map L (inverts L W) := by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫ γ.s
      s := β.s ≫ γ.s
      hs := W.comp_mem _ _ β.hs γ.hs }
  have := inverts L W _ β.hs
  have := inverts L W _ γ.hs
  have : IsIso (L.map (β.s ≫ γ.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα, hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα', hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), hβ]
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc, LeftFraction.map_comp_map_s, L.map_comp]
end Localization
end CategoryTheory