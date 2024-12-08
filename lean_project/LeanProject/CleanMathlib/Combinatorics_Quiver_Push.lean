import Mathlib.Combinatorics.Quiver.Prefunctor
namespace Quiver
universe v v₁ v₂ u u₁ u₂
variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)
@[nolint unusedArguments]
def Push (_ : V → W) :=
  W
instance [h : Nonempty W] : Nonempty (Push σ) :=
  h
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)
instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩
namespace Push
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f
@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl
variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))
noncomputable def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      dsimp only
      rw [← h X, ← h Y]
      exact φ.map f
theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl
theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    apply HEq.symm
    apply (eqRec_heq _ _).trans
    have : ∀ {α γ} {β : α → γ → Sort _} {a a'} (p : a = a') g (b : β a g), HEq (p ▸ b) b := by
      intros
      subst_vars
      rfl
    apply this
theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map, cast_eq]
    rfl
end Push
end Quiver