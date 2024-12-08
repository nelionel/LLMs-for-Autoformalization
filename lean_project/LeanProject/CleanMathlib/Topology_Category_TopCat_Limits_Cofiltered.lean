import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Filtered.Basic
open TopologicalSpace Topology
open CategoryTheory
open CategoryTheory.Limits
universe u v w
noncomputable section
namespace TopCat
section CofilteredLimit
variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)
theorem isTopologicalBasis_cofiltered_limit (hC : IsLimit C) (T : ∀ j, Set (Set (F.obj j)))
    (hT : ∀ j, IsTopologicalBasis (T j)) (univ : ∀ i : J, Set.univ ∈ T i)
    (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (_hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis
      {U : Set C.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V} := by
  classical
  let D := limitConeInfi F
  let E : C.pt ≅ D.pt := hC.conePointUniqueUpToIso (limitConeInfiIsLimit _)
  have hE : IsInducing E.hom := (TopCat.homeoOfIso E).isInducing
  suffices
    IsTopologicalBasis
      {U : Set D.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V} by
    convert this.isInducing hE
    ext U0
    constructor
    · rintro ⟨j, V, hV, rfl⟩
      exact ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
    · rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
      exact ⟨j, V, hV, rfl⟩
  convert IsTopologicalBasis.iInf_induced hT fun j (x : D.pt) => D.π.app j x using 1
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : ∀ i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine ⟨U, {j}, ?_, ?_⟩
    · simp only [Finset.mem_singleton]
      rintro i rfl
      simpa [U]
    · simp [U]
  · rintro ⟨U, G, h1, h2⟩
    obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists G
    let g : ∀ e ∈ G, j ⟶ e := fun _ he => (hj he).some
    let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
    let V : Set (F.obj j) := ⋂ (e : J) (_he : e ∈ G), Vs e
    refine ⟨j, V, ?_, ?_⟩
    · 
      have :
        ∀ (S : Set (Set (F.obj j))) (E : Finset J) (P : J → Set (F.obj j)) (_univ : Set.univ ∈ S)
          (_inter : ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
          (_cond : ∀ (e : J) (_he : e ∈ E), P e ∈ S), (⋂ (e) (_he : e ∈ E), P e) ∈ S := by
        intro S E
        induction E using Finset.induction_on with
        | empty =>
          intro P he _hh
          simpa
        | @insert a E _ha hh1 =>
          intro hh2 hh3 hh4 hh5
          rw [Finset.set_biInter_insert]
          refine hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 ?_)
          intro e he
          exact hh5 e (Finset.mem_insert_of_mem he)
      refine this _ _ _ (univ _) (inter _) ?_
      intro e he
      dsimp [Vs]
      rw [dif_pos he]
      exact compat j e (g e he) (U e) (h1 e he)
    · 
      rw [h2]
      change _ = (D.π.app j)⁻¹' ⋂ (e : J) (_ : e ∈ G), Vs e
      rw [Set.preimage_iInter]
      apply congrArg
      ext1 e
      rw [Set.preimage_iInter]
      apply congrArg
      ext1 he
      change (D.π.app e)⁻¹' U e =
        (D.π.app j) ⁻¹' if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
      rw [dif_pos he, ← Set.preimage_comp]
      apply congrFun
      apply congrArg
      rw [← coe_comp, D.w]
      rfl
end CofilteredLimit
end TopCat