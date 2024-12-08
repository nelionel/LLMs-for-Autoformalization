import Mathlib.CategoryTheory.Limits.Shapes.Products
namespace CategoryTheory
open Limits
variable {C : Type*} [Category C]
structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h
class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  effectiveEpi : Nonempty (EffectiveEpiStruct f)
noncomputable
def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : EffectiveEpiStruct f :=
  EffectiveEpi.effectiveEpi.some
noncomputable
def EffectiveEpi.desc {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    X ⟶ W := (EffectiveEpi.getStruct f).desc e h
@[reassoc (attr := simp)]
lemma EffectiveEpi.fac {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    f ≫ EffectiveEpi.desc f e h = e :=
  (EffectiveEpi.getStruct f).fac e h
lemma EffectiveEpi.uniq {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W) (hm : f ≫ m = e) :
    m = EffectiveEpi.desc f e h :=
  (EffectiveEpi.getStruct f).uniq e h _ hm
instance epiOfEffectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f := by
  constructor
  intro W m₁ m₂ h
  have : m₂ = EffectiveEpi.desc f (f ≫ m₂)
    (fun {Z} g₁ g₂ h => by simp only [← Category.assoc, h]) := EffectiveEpi.uniq _ _ _ _ rfl
  rw [this]
  exact EffectiveEpi.uniq _ _ _ _ h
structure EffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) where
  desc : ∀ {W} (e : (a : α) → (X a ⟶ W)),
          (∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) → (B ⟶ W)
  fac : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (a : α), π a ≫ desc e h = e a
  uniq : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (m : B ⟶ W), (∀ (a : α), π a ≫ m = e a) → m = desc e h
class EffectiveEpiFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) : Prop where
  effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)
noncomputable
def EffectiveEpiFamily.getStruct {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] : EffectiveEpiFamilyStruct X π :=
  EffectiveEpiFamily.effectiveEpiFamily.some
noncomputable
def EffectiveEpiFamily.desc {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) : B ⟶ W :=
  (EffectiveEpiFamily.getStruct X π).desc e h
@[reassoc (attr := simp)]
lemma EffectiveEpiFamily.fac {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  (EffectiveEpiFamily.getStruct X π).fac e h a
lemma EffectiveEpiFamily.uniq {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
    (m : B ⟶ W) (hm : ∀ a, π a ≫ m = e a) :
    m = EffectiveEpiFamily.desc X π e h :=
  (EffectiveEpiFamily.getStruct X π).uniq e h m hm
lemma EffectiveEpiFamily.hom_ext {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (m₁ m₂ : B ⟶ W) (h : ∀ a, π a ≫ m₁ = π a ≫ m₂) :
    m₁ = m₂ := by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← Category.assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h
noncomputable
def effectiveEpiFamilyStructSingletonOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f] :
    EffectiveEpiFamilyStruct (fun () ↦ X) (fun () ↦ f) where
  desc e h := EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  fac e h := fun _ ↦ EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()
instance {B X : C} (f : X ⟶ B) [EffectiveEpi f] : EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨⟨effectiveEpiFamilyStructSingletonOfEffectiveEpi f⟩⟩
noncomputable
def effectiveEpiStructOfEffectiveEpiFamilySingleton {B X : C} (f : X ⟶ B)
    [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpiStruct f where
  desc e h := EffectiveEpiFamily.desc
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) m (fun _ ↦ hm)
instance {B X : C} (f : X ⟶ B) [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfEffectiveEpiFamilySingleton f⟩⟩
theorem effectiveEpi_iff_effectiveEpiFamily {B X : C} (f : X ⟶ B) :
    EffectiveEpi f ↔ EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
noncomputable
def effectiveEpiFamilyStructOfIsIsoDesc {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [IsIso (Sigma.desc π)] :
    EffectiveEpiFamilyStruct X π where
  desc e _ := (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    rw [this, Category.assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc, Cofan.mk_pt,
      Cofan.mk_ι_app]
  uniq e h m hm := by
    simp only [asIso_inv, IsIso.eq_inv_comp]
    ext a
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.ι_desc]
    exact hm a
instance {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [IsIso (Sigma.desc π)] : EffectiveEpiFamily X π :=
  ⟨⟨effectiveEpiFamilyStructOfIsIsoDesc X π⟩⟩
noncomputable
def effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiStruct f where
  desc e _ := inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h
instance {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpi f := ⟨⟨effectiveEpiStructOfIsIso f⟩⟩
example {X : C} : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) := inferInstance
def EffectiveEpiFamilyStruct.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (P : EffectiveEpiFamilyStruct (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamilyStruct X π where
  desc := fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a,rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _
lemma EffectiveEpiFamily.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (h : EffectiveEpiFamily (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamily X π :=
  .mk <| .intro <| @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h |>.reindex _ _ e
end CategoryTheory