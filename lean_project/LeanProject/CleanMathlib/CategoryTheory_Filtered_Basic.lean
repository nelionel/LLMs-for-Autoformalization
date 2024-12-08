import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
open Function
universe w v v₁ v₂ u u₁ u₂
namespace CategoryTheory
variable (C : Type u) [Category.{v} C]
class IsFilteredOrEmpty : Prop where
  cocone_objs : ∀ X Y : C, ∃ (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), True
  cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h
class IsFiltered extends IsFilteredOrEmpty C : Prop where
  [nonempty : Nonempty C]
instance (priority := 100) isFilteredOrEmpty_of_semilatticeSup (α : Type u) [SemilatticeSup α] :
    IsFilteredOrEmpty α where
  cocone_objs X Y := ⟨X ⊔ Y, homOfLE le_sup_left, homOfLE le_sup_right, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩
instance (priority := 100) isFiltered_of_semilatticeSup_nonempty (α : Type u) [SemilatticeSup α]
    [Nonempty α] : IsFiltered α where
instance (priority := 100) isFilteredOrEmpty_of_directed_le (α : Type u) [Preorder α]
    [IsDirected α (· ≤ ·)] : IsFilteredOrEmpty α where
  cocone_objs X Y :=
    let ⟨Z, h1, h2⟩ := exists_ge_ge X Y
    ⟨Z, homOfLE h1, homOfLE h2, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩
instance (priority := 100) isFiltered_of_directed_le_nonempty (α : Type u) [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] : IsFiltered α where
example (α : Type u) [SemilatticeSup α] [OrderBot α] : IsFiltered α := by infer_instance
example (α : Type u) [SemilatticeSup α] [OrderTop α] : IsFiltered α := by infer_instance
instance : IsFiltered (Discrete PUnit) where
  cocone_objs X Y := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by subsingleton⟩
namespace IsFiltered
section AllowEmpty
variable {C}
variable [IsFilteredOrEmpty C]
noncomputable def max (j j' : C) : C :=
  (IsFilteredOrEmpty.cocone_objs j j').choose
noncomputable def leftToMax (j j' : C) : j ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose
noncomputable def rightToMax (j j' : C) : j' ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose_spec.choose
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
  (IsFilteredOrEmpty.cocone_maps f f').choose
noncomputable def coeqHom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose
@[reassoc]
theorem coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose_spec
end AllowEmpty
end IsFiltered
namespace IsFilteredOrEmpty
open IsFiltered
variable {C}
variable [IsFilteredOrEmpty C]
variable {D : Type u₁} [Category.{v₁} D]
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFilteredOrEmpty D :=
  { cocone_objs := fun X Y =>
      ⟨R.obj (max (L.obj X) (L.obj Y)),
        h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨R.obj (coeq (L.map f) (L.map g)), h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left, coeq_condition]⟩ }
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFilteredOrEmpty D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)
theorem of_equivalence (h : C ≌ D) : IsFilteredOrEmpty D :=
  of_right_adjoint h.symm.toAdjunction
end IsFilteredOrEmpty
namespace IsFiltered
section Nonempty
open CategoryTheory.Limits
variable {C}
variable [IsFiltered C]
theorem sup_objs_exists (O : Finset C) : ∃ S : C, ∀ {X}, X ∈ O → Nonempty (X ⟶ S) := by
  classical
  induction' O using Finset.induction with X O' nm h
  · exact ⟨Classical.choice IsFiltered.nonempty, by intro; simp⟩
  · obtain ⟨S', w'⟩ := h
    use max X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨leftToMax _ _⟩
    · exact ⟨(w' (Finset.mem_of_mem_insert_of_ne mY h)).some ≫ rightToMax _ _⟩
variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))
theorem sup_exists :
    ∃ (S : C) (T : ∀ {X : C}, X ∈ O → (X ⟶ S)),
      ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H →
          f ≫ T mY = T mX := by
  classical
  induction' H using Finset.induction with h' H' nmf h''
  · obtain ⟨S, f⟩ := sup_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  · obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨coeq (f ≫ T' mY) (T' mX), fun mZ => T' mZ ≫ coeqHom (f ≫ T' mY) (T' mX), ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [← Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      by_cases hf : f = f'
      · subst hf
        apply coeq_condition
      · rw [@w' _ _ mX mY f']
        simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and] at mf'
        rcases mf' with mf' | mf'
        · exfalso
          exact hf mf'.symm
        · exact mf'
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose! h
      obtain ⟨rfl, h⟩ := h
      trivial
noncomputable def sup : C :=
  (sup_exists O H).choose
noncomputable def toSup {X : C} (m : X ∈ O) : X ⟶ sup O H :=
  (sup_exists O H).choose_spec.choose m
theorem toSup_commutes {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H) :
    f ≫ toSup O H mY = toSup O H mX :=
  (sup_exists O H).choose_spec.choose_spec mX mY mf
variable {J : Type w} [SmallCategory J] [FinCategory J]
theorem cocone_nonempty (F : J ⥤ C) : Nonempty (Cocone F) := by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.biUnion   fun X : J =>
      Finset.univ.biUnion fun Y : J =>
        Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := sup_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.comp_id]
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, PSigma.mk.injEq,
    true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩
noncomputable def cocone (F : J ⥤ C) : Cocone F :=
  (cocone_nonempty F).some
variable {D : Type u₁} [Category.{v₁} D]
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFiltered D :=
  { IsFilteredOrEmpty.of_right_adjoint h with
    nonempty := IsFiltered.nonempty.map R.obj }
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFiltered D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)
theorem of_equivalence (h : C ≌ D) : IsFiltered D :=
  of_right_adjoint h.symm.toAdjunction
end Nonempty
section OfCocone
open CategoryTheory.Limits
theorem of_cocone_nonempty (h : ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
    Nonempty (Cocone F)) : IsFiltered C := by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsFilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intros X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.ι.app ⟨⟨WalkingPair.left⟩⟩, c.ι.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intros X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.ι.app ⟨WalkingParallelPair.one⟩, ?_⟩
      have h₁ := c.ι.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.ι.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsFiltered.mk
theorem of_hasFiniteColimits [HasFiniteColimits C] : IsFiltered C :=
  of_cocone_nonempty.{v} C fun F => ⟨colimit.cocone F⟩
theorem of_isTerminal {X : C} (h : IsTerminal X) : IsFiltered C :=
  of_cocone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.from _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩
instance (priority := 100) of_hasTerminal [HasTerminal C] : IsFiltered C :=
  of_isTerminal _ terminalIsTerminal
theorem iff_cocone_nonempty : IsFiltered C ↔
    ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cocone F) :=
  ⟨fun _ _ _ _ F => cocone_nonempty F, of_cocone_nonempty C⟩
end OfCocone
section SpecialShapes
variable {C}
variable [IsFilteredOrEmpty C]
noncomputable def max₃ (j₁ j₂ j₃ : C) : C :=
  max (max j₁ j₂) j₃
noncomputable def firstToMax₃ (j₁ j₂ j₃ : C) : j₁ ⟶ max₃ j₁ j₂ j₃ :=
  leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃
noncomputable def secondToMax₃ (j₁ j₂ j₃ : C) : j₂ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃
noncomputable def thirdToMax₃ (j₁ j₂ j₃ : C) : j₃ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax (max j₁ j₂) j₃
noncomputable def coeq₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : C :=
  coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))
noncomputable def coeq₃Hom {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : j₂ ⟶ coeq₃ f g h :=
  coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))
theorem coeq₃_condition₁ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    f ≫ coeq₃Hom f g h = g ≫ coeq₃Hom f g h := by
  simp only [coeq₃Hom, ← Category.assoc, coeq_condition f g]
theorem coeq₃_condition₂ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    g ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h := by
  dsimp [coeq₃Hom]
  slice_lhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← Category.assoc, coeq_condition _ _]
  simp only [Category.assoc]
theorem coeq₃_condition₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h :=
  Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)
theorem span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j') :
    ∃ (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g' :=
  let ⟨K, G, G', _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  let ⟨k, e, he⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← Category.assoc] ⟩
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsFilteredOrEmpty.cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [Category.assoc] at hs
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by simp only [← Category.assoc, ht], hs⟩
theorem tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
    (g₁ : j₁ ⟶ l) (g₂ : j₃ ⟶ l) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : l ⟶ s) (γ : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = f₃ ≫ γ ∧ f₄ ≫ γ = g₂ ≫ β := by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, ?_, by simp only [← Category.assoc, hl], ?_⟩ <;>
    simp only [hs₁, hs₂, Category.assoc]
end SpecialShapes
end IsFiltered
class IsCofilteredOrEmpty : Prop where
  cone_objs : ∀ X Y : C, ∃ (W : _) (_ : W ⟶ X) (_ : W ⟶ Y), True
  cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (W : _) (h : W ⟶ X), h ≫ f = h ≫ g
class IsCofiltered extends IsCofilteredOrEmpty C : Prop where
  [nonempty : Nonempty C]
instance (priority := 100) isCofilteredOrEmpty_of_semilatticeInf (α : Type u) [SemilatticeInf α] :
    IsCofilteredOrEmpty α where
  cone_objs X Y := ⟨X ⊓ Y, homOfLE inf_le_left, homOfLE inf_le_right, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by
    apply ULift.ext
    subsingleton⟩
instance (priority := 100) isCofiltered_of_semilatticeInf_nonempty (α : Type u) [SemilatticeInf α]
    [Nonempty α] : IsCofiltered α where
instance (priority := 100) isCofilteredOrEmpty_of_directed_ge (α : Type u) [Preorder α]
    [IsDirected α (· ≥ ·)] : IsCofilteredOrEmpty α where
  cone_objs X Y :=
    let ⟨Z, hX, hY⟩ := exists_le_le X Y
    ⟨Z, homOfLE hX, homOfLE hY, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by
    apply ULift.ext
    subsingleton⟩
instance (priority := 100) isCofiltered_of_directed_ge_nonempty (α : Type u) [Preorder α]
    [IsDirected α (· ≥ ·)] [Nonempty α] : IsCofiltered α where
example (α : Type u) [SemilatticeInf α] [OrderBot α] : IsCofiltered α := by infer_instance
example (α : Type u) [SemilatticeInf α] [OrderTop α] : IsCofiltered α := by infer_instance
instance : IsCofiltered (Discrete PUnit) where
  cone_objs _ Y := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by
    apply ULift.ext
    subsingleton⟩
namespace IsCofiltered
section AllowEmpty
variable {C}
variable [IsCofilteredOrEmpty C]
noncomputable def min (j j' : C) : C :=
  (IsCofilteredOrEmpty.cone_objs j j').choose
noncomputable def minToLeft (j j' : C) : min j j' ⟶ j :=
  (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose
noncomputable def minToRight (j j' : C) : min j j' ⟶ j' :=
  (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose_spec.choose
noncomputable def eq {j j' : C} (f f' : j ⟶ j') : C :=
  (IsCofilteredOrEmpty.cone_maps f f').choose
noncomputable def eqHom {j j' : C} (f f' : j ⟶ j') : eq f f' ⟶ j :=
  (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose
@[reassoc]
theorem eq_condition {j j' : C} (f f' : j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f' :=
  (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose_spec
theorem cospan {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i) :
    ∃ (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
  let ⟨K, G, G', _⟩ := IsCofilteredOrEmpty.cone_objs j j'
  let ⟨k, e, he⟩ := IsCofilteredOrEmpty.cone_maps (G ≫ f) (G' ≫ f')
  ⟨k, e ≫ G, e ≫ G', by simpa only [Category.assoc] using he⟩
theorem _root_.CategoryTheory.Functor.ranges_directed (F : C ⥤ Type*) (j : C) :
    Directed (· ⊇ ·) fun f : Σ'i, i ⟶ j => Set.range (F.map f.2) := fun ⟨i, ij⟩ ⟨k, kj⟩ => by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine ⟨⟨l, lk ≫ kj⟩, e ▸ ?_, ?_⟩ <;> simp_rw [F.map_comp] <;> apply Set.range_comp_subset_range
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂) :
    ∃ (s : C) (α : s ⟶ k₁) (β : s ⟶ k₂), α ≫ f₁ = β ≫ g₁ ∧ α ≫ f₂ = β ≫ g₂ := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := cospan f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsCofilteredOrEmpty.cone_maps (k₁t ≫ f₂) (k₂t ≫ g₂)
  exact ⟨s, ts ≫ k₁t, ts ≫ k₂t, by simp only [Category.assoc, ht],
    by simp only [Category.assoc, hs]⟩
end AllowEmpty
end IsCofiltered
namespace IsCofilteredOrEmpty
open IsCofiltered
variable {C}
variable [IsCofilteredOrEmpty C]
variable {D : Type u₁} [Category.{v₁} D]
theorem of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : IsCofilteredOrEmpty D :=
  { cone_objs := fun X Y =>
      ⟨L.obj (min (R.obj X) (R.obj Y)), (h.homEquiv _ X).symm (minToLeft _ _),
        (h.homEquiv _ Y).symm (minToRight _ _), ⟨⟩⟩
    cone_maps := fun X Y f g =>
      ⟨L.obj (eq (R.map f) (R.map g)), (h.homEquiv _ _).symm (eqHom _ _), by
        rw [← h.homEquiv_naturality_right_symm, ← h.homEquiv_naturality_right_symm, eq_condition]⟩ }
theorem of_isLeftAdjoint (L : C ⥤ D) [L.IsLeftAdjoint] : IsCofilteredOrEmpty D :=
  of_left_adjoint (Adjunction.ofIsLeftAdjoint L)
theorem of_equivalence (h : C ≌ D) : IsCofilteredOrEmpty D :=
  of_left_adjoint h.toAdjunction
end IsCofilteredOrEmpty
namespace IsCofiltered
section Nonempty
open CategoryTheory.Limits
variable {C}
variable [IsCofiltered C]
theorem inf_objs_exists (O : Finset C) : ∃ S : C, ∀ {X}, X ∈ O → Nonempty (S ⟶ X) := by
  classical
  induction' O using Finset.induction with X O' nm h
  · exact ⟨Classical.choice IsCofiltered.nonempty, by intro; simp⟩
  · obtain ⟨S', w'⟩ := h
    use min X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨minToLeft _ _⟩
    · exact ⟨minToRight _ _ ≫ (w' (Finset.mem_of_mem_insert_of_ne mY h)).some⟩
variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))
theorem inf_exists :
    ∃ (S : C) (T : ∀ {X : C}, X ∈ O → (S ⟶ X)),
      ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H →
          T mX ≫ f = T mY := by
  classical
  induction' H using Finset.induction with h' H' nmf h''
  · obtain ⟨S, f⟩ := inf_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  · obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨eq (T' mX ≫ f) (T' mY), fun mZ => eqHom (T' mX ≫ f) (T' mY) ≫ T' mZ, ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      by_cases hf : f = f'
      · subst hf
        apply eq_condition
      · rw [@w' _ _ mX mY f']
        simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and] at mf'
        rcases mf' with mf' | mf'
        · exfalso
          exact hf mf'.symm
        · exact mf'
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose! h
      obtain ⟨rfl, h⟩ := h
      trivial
noncomputable def inf : C :=
  (inf_exists O H).choose
noncomputable def infTo {X : C} (m : X ∈ O) : inf O H ⟶ X :=
  (inf_exists O H).choose_spec.choose m
theorem infTo_commutes {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H) :
    infTo O H mX ≫ f = infTo O H mY :=
  (inf_exists O H).choose_spec.choose_spec mX mY mf
variable {J : Type w} [SmallCategory J] [FinCategory J]
theorem cone_nonempty (F : J ⥤ C) : Nonempty (Cone F) := by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J =>
      Finset.univ.biUnion fun Y : J =>
        Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := inf_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.id_comp]
  symm
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    PSigma.mk.injEq, true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩
noncomputable def cone (F : J ⥤ C) : Cone F :=
  (cone_nonempty F).some
variable {D : Type u₁} [Category.{v₁} D]
theorem of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : IsCofiltered D :=
  { IsCofilteredOrEmpty.of_left_adjoint h with
    nonempty := IsCofiltered.nonempty.map L.obj }
theorem of_isLeftAdjoint (L : C ⥤ D) [L.IsLeftAdjoint] : IsCofiltered D :=
  of_left_adjoint (Adjunction.ofIsLeftAdjoint L)
theorem of_equivalence (h : C ≌ D) : IsCofiltered D :=
  of_left_adjoint h.toAdjunction
end Nonempty
section OfCone
open CategoryTheory.Limits
theorem of_cone_nonempty (h : ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
    Nonempty (Cone F)) : IsCofiltered C := by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsCofilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intros X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.π.app ⟨⟨WalkingPair.left⟩⟩, c.π.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intros X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.π.app ⟨WalkingParallelPair.zero⟩, ?_⟩
      have h₁ := c.π.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.π.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsCofiltered.mk
theorem of_hasFiniteLimits [HasFiniteLimits C] : IsCofiltered C :=
  of_cone_nonempty.{v} C fun F => ⟨limit.cone F⟩
theorem of_isInitial {X : C} (h : IsInitial X) : IsCofiltered C :=
  of_cone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.to _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩
instance (priority := 100) of_hasInitial [HasInitial C] : IsCofiltered C :=
  of_isInitial _ initialIsInitial
@[deprecated (since := "2024-03-11")]
alias _root_.CategoryTheory.cofiltered_of_hasFiniteLimits := of_hasFiniteLimits
theorem iff_cone_nonempty : IsCofiltered C ↔
    ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cone F) :=
  ⟨fun _ _ _ _ F => cone_nonempty F, of_cone_nonempty C⟩
end OfCone
end IsCofiltered
section Opposite
open Opposite
instance isCofilteredOrEmpty_op_of_isFilteredOrEmpty [IsFilteredOrEmpty C] :
    IsCofilteredOrEmpty Cᵒᵖ where
  cone_objs X Y :=
    ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op, by
      rw [show f = f.unop.op by simp, show g = g.unop.op by simp, ← op_comp, ← op_comp]
      congr 1
      exact IsFiltered.coeq_condition f.unop g.unop⟩
instance isCofiltered_op_of_isFiltered [IsFiltered C] : IsCofiltered Cᵒᵖ where
  nonempty := letI : Nonempty C := IsFiltered.nonempty; inferInstance
instance isFilteredOrEmpty_op_of_isCofilteredOrEmpty [IsCofilteredOrEmpty C] :
    IsFilteredOrEmpty Cᵒᵖ where
  cocone_objs X Y :=
    ⟨op (IsCofiltered.min X.unop Y.unop), (IsCofiltered.minToLeft X.unop Y.unop).op,
      (IsCofiltered.minToRight X.unop Y.unop).op, trivial⟩
  cocone_maps X Y f g :=
    ⟨op (IsCofiltered.eq f.unop g.unop), (IsCofiltered.eqHom f.unop g.unop).op, by
      rw [show f = f.unop.op by simp, show g = g.unop.op by simp, ← op_comp, ← op_comp]
      congr 1
      exact IsCofiltered.eq_condition f.unop g.unop⟩
instance isFiltered_op_of_isCofiltered [IsCofiltered C] : IsFiltered Cᵒᵖ where
  nonempty := letI : Nonempty C := IsCofiltered.nonempty; inferInstance
lemma isCofilteredOrEmpty_of_isFilteredOrEmpty_op [IsFilteredOrEmpty Cᵒᵖ] : IsCofilteredOrEmpty C :=
  IsCofilteredOrEmpty.of_equivalence (opOpEquivalence _)
lemma isFilteredOrEmpty_of_isCofilteredOrEmpty_op [IsCofilteredOrEmpty Cᵒᵖ] : IsFilteredOrEmpty C :=
  IsFilteredOrEmpty.of_equivalence (opOpEquivalence _)
lemma isCofiltered_of_isFiltered_op [IsFiltered Cᵒᵖ] : IsCofiltered C :=
  IsCofiltered.of_equivalence (opOpEquivalence _)
lemma isFiltered_of_isCofiltered_op [IsCofiltered Cᵒᵖ] : IsFiltered C :=
  IsFiltered.of_equivalence (opOpEquivalence _)
end Opposite
section ULift
instance [IsFiltered C] : IsFiltered (ULift.{u₂} C) :=
  IsFiltered.of_equivalence ULift.equivalence
instance [IsCofiltered C] : IsCofiltered (ULift.{u₂} C) :=
  IsCofiltered.of_equivalence ULift.equivalence
instance [IsFiltered C] : IsFiltered (ULiftHom C) :=
  IsFiltered.of_equivalence ULiftHom.equiv
instance [IsCofiltered C] : IsCofiltered (ULiftHom C) :=
  IsCofiltered.of_equivalence ULiftHom.equiv
instance [IsFiltered C] : IsFiltered (AsSmall C) :=
  IsFiltered.of_equivalence AsSmall.equiv
instance [IsCofiltered C] : IsCofiltered (AsSmall C) :=
  IsCofiltered.of_equivalence AsSmall.equiv
end ULift
section Pi
variable {α : Type w} {I : α → Type u₁} [∀ i, Category.{v₁} (I i)]
open IsFiltered in
instance [∀ i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (∀ i, I i) where
  cocone_objs k l := ⟨fun s => max (k s) (l s), fun s => leftToMax (k s) (l s),
    fun s => rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => coeq (f s) (g s), fun s => coeqHom (f s) (g s),
    funext fun s => by simp [coeq_condition (f s) (g s)]⟩
attribute [local instance] IsFiltered.nonempty in
instance [∀ i, IsFiltered (I i)] : IsFiltered (∀ i, I i) where
open IsCofiltered in
instance [∀ i, IsCofilteredOrEmpty (I i)] : IsCofilteredOrEmpty (∀ i, I i) where
  cone_objs k l := ⟨fun s => min (k s) (l s), fun s => minToLeft (k s) (l s),
    fun s => minToRight (k s) (l s), trivial⟩
  cone_maps k l f g := ⟨fun s => eq (f s) (g s), fun s => eqHom (f s) (g s),
    funext fun s => by simp [eq_condition (f s) (g s)]⟩
attribute [local instance] IsCofiltered.nonempty in
instance [∀ i, IsCofiltered (I i)] : IsCofiltered (∀ i, I i) where
end Pi
section Prod
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
open IsFiltered in
instance [IsFilteredOrEmpty C] [IsFilteredOrEmpty D] : IsFilteredOrEmpty (C × D) where
  cocone_objs k l := ⟨(max k.1 l.1, max k.2 l.2), (leftToMax k.1 l.1, leftToMax k.2 l.2),
    (rightToMax k.1 l.1, rightToMax k.2 l.2), trivial⟩
  cocone_maps k l f g := ⟨(coeq f.1 g.1, coeq f.2 g.2), (coeqHom f.1 g.1, coeqHom f.2 g.2),
    by simp [coeq_condition]⟩
attribute [local instance] IsFiltered.nonempty in
instance [IsFiltered C] [IsFiltered D] : IsFiltered (C × D) where
open IsCofiltered in
instance [IsCofilteredOrEmpty C] [IsCofilteredOrEmpty D] : IsCofilteredOrEmpty (C × D) where
  cone_objs k l := ⟨(min k.1 l.1, min k.2 l.2), (minToLeft k.1 l.1, minToLeft k.2 l.2),
    (minToRight k.1 l.1, minToRight k.2 l.2), trivial⟩
  cone_maps k l f g := ⟨(eq f.1 g.1, eq f.2 g.2), (eqHom f.1 g.1, eqHom f.2 g.2),
    by simp [eq_condition]⟩
attribute [local instance] IsCofiltered.nonempty in
instance [IsCofiltered C] [IsCofiltered D] : IsCofiltered (C × D) where
end Prod
end CategoryTheory