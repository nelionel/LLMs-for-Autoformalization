import Mathlib.CategoryTheory.Sites.Sheaf
namespace CategoryTheory
variable {C D : Type _} [Category C] [Category D]
open Limits
namespace Presieve
def FactorsThruAlong {X Y : C} (S : Presieve Y) (T : Presieve X) (f : Y ⟶ X) : Prop :=
  ∀ ⦃Z : C⦄ ⦃g : Z ⟶ Y⦄, S g →
  ∃ (W : C) (i : Z ⟶ W) (e : W ⟶ X), T e ∧ i ≫ e = g ≫ f
def FactorsThru {X : C} (S T : Presieve X) : Prop :=
  ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g →
  ∃ (W : C) (i : Z ⟶ W) (e : W ⟶ X), T e ∧ i ≫ e = g
@[simp]
lemma factorsThruAlong_id {X : C} (S T : Presieve X) :
    S.FactorsThruAlong T (𝟙 X) ↔ S.FactorsThru T := by
  simp [FactorsThruAlong, FactorsThru]
lemma factorsThru_of_le {X : C} (S T : Presieve X) (h : S ≤ T) :
    S.FactorsThru T :=
  fun Y g hg => ⟨Y, 𝟙 _, g, h _ hg, by simp⟩
lemma le_of_factorsThru_sieve {X : C} (S : Presieve X) (T : Sieve X) (h : S.FactorsThru T) :
    S ≤ T := by
  rintro Y f hf
  obtain ⟨W, i, e, h1, rfl⟩ := h hf
  exact T.downward_closed h1 _
lemma factorsThru_top {X : C} (S : Presieve X) : S.FactorsThru ⊤ :=
  factorsThru_of_le _ _ le_top
lemma isSheafFor_of_factorsThru
    {X : C} {S T : Presieve X}
    (P : Cᵒᵖ ⥤ Type*)
    (H : S.FactorsThru T) (hS : S.IsSheafFor P)
    (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, T f → ∃ (R : Presieve Y),
      R.IsSeparatedFor P ∧ R.FactorsThruAlong S f) :
    T.IsSheafFor P := by
  simp only [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor] at *
  choose W i e h1 h2 using H
  refine ⟨?_, fun x hx => ?_⟩
  · intro x y₁ y₂ h₁ h₂
    refine hS.1.ext (fun Y g hg => ?_)
    simp only [← h2 hg, op_comp, P.map_comp, types_comp_apply, h₁ _ (h1 _ ), h₂ _ (h1 _)]
  let y : S.FamilyOfElements P := fun Y g hg => P.map (i _).op (x (e hg) (h1 _))
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    rw [← types_comp_apply (P.map (i h₁).op) (P.map g₁.op),
      ← types_comp_apply (P.map (i h₂).op) (P.map g₂.op),
      ← P.map_comp, ← op_comp, ← P.map_comp, ← op_comp]
    apply hx
    simp only [h2, h, Category.assoc]
  let ⟨_, h2'⟩ := hS
  obtain ⟨z, hz⟩ := h2' y hy
  refine ⟨z, fun Y g hg => ?_⟩
  obtain ⟨R, hR1, hR2⟩ := h hg
  choose WW ii ee hh1 hh2 using hR2
  refine hR1.ext (fun Q t ht => ?_)
  rw [← types_comp_apply (P.map g.op) (P.map t.op), ← P.map_comp, ← op_comp, ← hh2 ht,
    op_comp, P.map_comp, types_comp_apply, hz _ (hh1 _),
    ← types_comp_apply _ (P.map (ii ht).op), ← P.map_comp, ← op_comp]
  apply hx
  simp only [Category.assoc, h2, hh2]
end Presieve
variable (C) in
@[ext]
structure Coverage where
  covering : ∀ (X : C), Set (Presieve X)
  pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Presieve X) (_ : S ∈ covering X),
    ∃ (T : Presieve Y), T ∈ covering Y ∧ T.FactorsThruAlong S f
namespace Coverage
instance : CoeFun (Coverage C) (fun _ => (X : C) → Set (Presieve X)) where
  coe := covering
variable (C) in
def ofGrothendieck (J : GrothendieckTopology C) : Coverage C where
  covering X := { S | Sieve.generate S ∈ J X }
  pullback := by
    intro X Y f S (hS : Sieve.generate S ∈ J X)
    refine ⟨(Sieve.generate S).pullback f, ?_, fun Z g h => h⟩
    dsimp
    rw [Sieve.generate_sieve]
    exact J.pullback_stable _ hS
lemma ofGrothendieck_iff {X : C} {S : Presieve X} (J : GrothendieckTopology C) :
    S ∈ ofGrothendieck _ J X ↔ Sieve.generate S ∈ J X := Iff.rfl
inductive Saturate (K : Coverage C) : (X : C) → Sieve X → Prop where
  | of (X : C) (S : Presieve X) (hS : S ∈ K X) : Saturate K X (Sieve.generate S)
  | top (X : C) : Saturate K X ⊤
  | transitive (X : C) (R S : Sieve X) :
    Saturate K X R →
    (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → Saturate K Y (S.pullback f)) →
    Saturate K X S
lemma eq_top_pullback {X Y : C} {S T : Sieve X} (h : S ≤ T) (f : Y ⟶ X) (hf : S f) :
    T.pullback f = ⊤ := by
  ext Z g
  simp only [Sieve.pullback_apply, Sieve.top_apply, iff_true]
  apply h
  apply S.downward_closed
  exact hf
lemma saturate_of_superset (K : Coverage C) {X : C} {S T : Sieve X} (h : S ≤ T)
    (hS : Saturate K X S) : Saturate K X T := by
  apply Saturate.transitive _ _ _ hS
  intro Y g hg
  rw [eq_top_pullback (h := h)]
  · apply Saturate.top
  · assumption
variable (C) in
def toGrothendieck (K : Coverage C) : GrothendieckTopology C where
  sieves := Saturate K
  top_mem' := .top
  pullback_stable' := by
    intro X Y S f hS
    induction hS generalizing Y with
    | of X S hS =>
      obtain ⟨R,hR1,hR2⟩ := K.pullback f S hS
      suffices Sieve.generate R ≤ (Sieve.generate S).pullback f from
        saturate_of_superset _ this (Saturate.of _ _ hR1)
      rintro Z g ⟨W, i, e, h1, h2⟩
      obtain ⟨WW, ii, ee, hh1, hh2⟩ := hR2 h1
      refine ⟨WW, i ≫ ii, ee, hh1, ?_⟩
      simp only [hh2, reassoc_of% h2, Category.assoc]
    | top X => apply Saturate.top
    | transitive X R S _ hS H1 _ =>
      apply Saturate.transitive
      · apply H1 f
      intro Z g hg
      rw [← Sieve.pullback_comp]
      exact hS hg
  transitive' _ _ hS _ hR := .transitive _ _ _ hS hR
instance : PartialOrder (Coverage C) where
  le A B := A.covering ≤ B.covering
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
  le_antisymm _ _ h1 h2 := Coverage.ext <| funext <|
    fun X => le_antisymm (h1 X) (h2 X)
variable (C) in
def gi : GaloisInsertion (toGrothendieck C) (ofGrothendieck C) where
  choice K _ := toGrothendieck _ K
  choice_eq := fun _ _ => rfl
  le_l_u J X S hS := by
    rw [← Sieve.generate_sieve S]
    apply Saturate.of
    dsimp [ofGrothendieck]
    rwa [Sieve.generate_sieve S]
  gc K J := by
    constructor
    · intro H X S hS
      exact H _ <| Saturate.of _ _ hS
    · intro H X S hS
      induction hS with
      | of X S hS => exact H _ hS
      | top => apply J.top_mem
      | transitive X R S _ _ H1 H2 => exact J.transitive H1 _ H2
theorem toGrothendieck_eq_sInf (K : Coverage C) : toGrothendieck _ K =
    sInf {J | K ≤ ofGrothendieck _ J } := by
  apply le_antisymm
  · apply le_sInf; intro J hJ
    intro X S hS
    induction hS with
    | of X S hS => apply hJ; assumption
    | top => apply J.top_mem
    | transitive X R S _ _ H1 H2 => exact J.transitive H1 _ H2
  · apply sInf_le
    intro X S hS
    apply Saturate.of _ _ hS
instance : SemilatticeSup (Coverage C) where
  sup x y :=
  { covering := fun B ↦ x.covering B ∪ y.covering B
    pullback := by
      rintro X Y f S (hx | hy)
      · obtain ⟨T, hT⟩ := x.pullback f S hx
        exact ⟨T, Or.inl hT.1, hT.2⟩
      · obtain ⟨T, hT⟩ := y.pullback f S hy
        exact ⟨T, Or.inr hT.1, hT.2⟩ }
  toPartialOrder := inferInstance
  le_sup_left _ _ _ := Set.subset_union_left
  le_sup_right _ _ _ := Set.subset_union_right
  sup_le _ _ _ hx hy X := Set.union_subset_iff.mpr ⟨hx X, hy X⟩
@[simp]
lemma sup_covering (x y : Coverage C) (B : C) :
    (x ⊔ y).covering B = x.covering B ∪ y.covering B :=
  rfl
theorem mem_toGrothendieck_sieves_of_superset (K : Coverage C) {X : C} {S : Sieve X}
    {R : Presieve X} (h : R ≤ S) (hR : R ∈ K.covering X) : S ∈ (K.toGrothendieck C) X :=
  K.saturate_of_superset ((Sieve.generate_le_iff _ _).mpr h) (Coverage.Saturate.of X _ hR)
end Coverage
open Coverage
namespace Presieve
theorem isSheaf_coverage (K : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (toGrothendieck _ K) P ↔
    (∀ {X : C} (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R) := by
  constructor
  · intro H X R hR
    rw [Presieve.isSheafFor_iff_generate]
    apply H _ <| Saturate.of _ _ hR
  · intro H X S hS
    suffices ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows by
      simpa using this (f := 𝟙 _)
    induction hS with
    | of X S hS =>
      intro Y f
      obtain ⟨T, hT1, hT2⟩ := K.pullback f S hS
      apply Presieve.isSheafFor_of_factorsThru (S := T)
      · intro Z g hg
        obtain ⟨W, i, e, h1, h2⟩ := hT2 hg
        exact ⟨Z, 𝟙 _, g, ⟨W, i, e, h1, h2⟩, by simp⟩
      · apply H; assumption
      · intro Z g _
        obtain ⟨R, hR1, hR2⟩ := K.pullback g _ hT1
        exact ⟨R, (H _ hR1).isSeparatedFor, hR2⟩
    | top => intros; simpa using Presieve.isSheafFor_top_sieve _
    | transitive X R S _ _ H1 H2 =>
      intro Y f
      simp only [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor] at *
      choose H1 H1' using H1
      choose H2 H2' using H2
      refine ⟨?_, fun x hx => ?_⟩
      · intro x t₁ t₂ h₁ h₂
        refine (H1 f).ext (fun Z g hg => ?_)
        refine (H2 hg (𝟙 _)).ext (fun ZZ gg hgg => ?_)
        simp only [Sieve.pullback_id, Sieve.pullback_apply] at hgg
        simp only [← types_comp_apply]
        rw [← P.map_comp, ← op_comp, h₁, h₂]
        simpa only [Sieve.pullback_apply, Category.assoc] using hgg
      let y : ∀ ⦃Z : C⦄ (g : Z ⟶ Y),
        ((S.pullback (g ≫ f)).pullback (𝟙 _)).arrows.FamilyOfElements P :=
        fun Z g ZZ gg hgg => x (gg ≫ g) (by simpa using hgg)
      have hy : ∀ ⦃Z : C⦄ (g : Z ⟶ Y), (y g).Compatible := by
        intro Z g Y₁ Y₂ ZZ g₁ g₂ f₁ f₂ h₁ h₂ h
        rw [hx]
        rw [reassoc_of% h]
      choose z hz using fun ⦃Z : C⦄ ⦃g : Z ⟶ Y⦄ (hg : R.pullback f g) =>
        H2' hg (𝟙 _) (y g) (hy g)
      let q : (R.pullback f).arrows.FamilyOfElements P := fun Z g hg => z hg
      have hq : q.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
        apply (H2 h₁ g₁).ext
        intro ZZ gg hgg
        simp only [← types_comp_apply]
        rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hz, hz]
        · dsimp [y]; congr 1; simp only [Category.assoc, h]
        · simpa [reassoc_of% h] using hgg
        · simpa using hgg
      obtain ⟨t, ht⟩ := H1' f q hq
      refine ⟨t, fun Z g hg => ?_⟩
      refine (H1 (g ≫ f)).ext (fun ZZ gg hgg => ?_)
      rw [← types_comp_apply _ (P.map gg.op), ← P.map_comp, ← op_comp, ht]
      on_goal 2 => simpa using hgg
      refine (H2 hgg (𝟙 _)).ext (fun ZZZ ggg hggg => ?_)
      rw [← types_comp_apply _ (P.map ggg.op), ← P.map_comp, ← op_comp, hz]
      on_goal 2 => simpa using hggg
      refine (H2 hgg ggg).ext (fun ZZZZ gggg _ => ?_)
      rw [← types_comp_apply _ (P.map gggg.op), ← P.map_comp, ← op_comp]
      apply hx
      simp
theorem isSheaf_sup (K L : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    (Presieve.IsSheaf ((K ⊔ L).toGrothendieck C)) P ↔
    (Presieve.IsSheaf (K.toGrothendieck C)) P ∧ (Presieve.IsSheaf (L.toGrothendieck C)) P := by
  refine ⟨fun h ↦ ⟨Presieve.isSheaf_of_le _ ((gi C).gc.monotone_l le_sup_left) h,
      Presieve.isSheaf_of_le _ ((gi C).gc.monotone_l le_sup_right) h⟩, fun h ↦ ?_⟩
  rw [isSheaf_coverage, isSheaf_coverage] at h
  rw [isSheaf_coverage]
  intro X R hR
  cases' hR with hR hR
  · exact h.1 R hR
  · exact h.2 R hR
end Presieve
namespace Presheaf
theorem isSheaf_iff_isLimit_coverage (K : Coverage C) (P : Cᵒᵖ ⥤ D) :
    Presheaf.IsSheaf (toGrothendieck _ K) P ↔ ∀ ⦃X : C⦄ (R : Presieve X),
      R ∈ K.covering X →
        Nonempty (IsLimit (P.mapCone (Sieve.generate R).arrows.cocone.op)) := by
  simp only [Presheaf.IsSheaf, Presieve.isSheaf_coverage, isLimit_iff_isSheafFor,
    ← Presieve.isSheafFor_iff_generate]
  aesop
theorem isSheaf_sup (K L : Coverage C) (P : Cᵒᵖ ⥤ D) :
    (IsSheaf ((K ⊔ L).toGrothendieck C)) P ↔
    (IsSheaf (K.toGrothendieck C)) P ∧ (IsSheaf (L.toGrothendieck C)) P :=
  ⟨fun h ↦ ⟨fun E ↦ ((Presieve.isSheaf_sup K L _).mp (h E)).1, fun E ↦
    ((Presieve.isSheaf_sup K L _).mp (h E)).2⟩,
      fun ⟨h₁, h₂⟩ E ↦ (Presieve.isSheaf_sup K L _).mpr ⟨h₁ E, h₂ E⟩⟩
end Presheaf
end CategoryTheory