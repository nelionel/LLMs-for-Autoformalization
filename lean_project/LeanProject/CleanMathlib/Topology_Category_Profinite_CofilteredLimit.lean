import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Limits.Konig
namespace Profinite
open CategoryTheory Limits
attribute [local instance] ConcreteCategory.instFunLike
universe u v
variable {J : Type v} [SmallCategory J] [IsCofiltered J] {F : J ⥤ Profinite.{max u v}} (C : Cone F)
theorem exists_isClopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)), IsClopen V ∧ U = C.π.app j ⁻¹' V := by
  have hB := TopCat.isTopologicalBasis_cofiltered_limit.{u, v} (F ⋙ Profinite.toTopCat)
      (Profinite.toTopCat.mapCone C) (isLimitOfPreserves _ hC) (fun j => {W | IsClopen W}) ?_
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  rotate_left
  · intro i
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    apply isTopologicalBasis_isClopen
  · rintro i j f V (hV : IsClopen _)
    exact ⟨hV.1.preimage ((F ⋙ toTopCat).map f).continuous,
      hV.2.preimage ((F ⋙ toTopCat).map f).continuous⟩
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.2
  clear hB
  let j : S → J := fun s => (hS s.2).choose
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.choose
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec
  have hUo : ∀ (i : ↑S), IsOpen ((fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i) := by
    intro s
    exact (hV s).1.2.preimage (C.π.app (j s)).continuous
  have hsU : U ⊆ ⋃ (i : ↑S), (fun s ↦ (forget Profinite).map (C.π.app (j s)) ⁻¹' V s) i := by
    dsimp only
    rw [h]
    rintro x ⟨T, hT, hx⟩
    refine ⟨_, ⟨⟨T, hT⟩, rfl⟩, ?_⟩
    dsimp only [forget_map_eq_coe]
    rwa [← (hV ⟨T, hT⟩).2]
  have := hU.1.isCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) hUo hsU
  obtain ⟨G, hG⟩ := this
  classical
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists (G.image j)
  let f : ∀ s ∈ G, j0 ⟶ j s := fun s hs => (hj0 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  refine ⟨j0, ⋃ (s : S) (_ : s ∈ G), W s, ?_, ?_⟩
  · apply isClopen_biUnion_finset
    intro s hs
    dsimp [W]
    rw [dif_pos hs]
    exact ⟨(hV s).1.1.preimage (F.map _).continuous, (hV s).1.2.preimage (F.map _).continuous⟩
  · ext x
    constructor
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion]
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      refine ⟨s, hs, ?_⟩
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, ← Functor.map_comp, C.w]
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      rw [h]
      refine ⟨s.1, s.2, ?_⟩
      rw [(hV s).2]
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, ← Functor.map_comp, C.w] at hx
theorem exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _) := by
  let U := f ⁻¹' {0}
  have hU : IsClopen U := f.isLocallyConstant.isClopen_fiber _
  obtain ⟨j, V, hV, h⟩ := exists_isClopen_of_cofiltered C hC hU
  classical
  use j, LocallyConstant.ofIsClopen hV
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  simp only [Fin.isValue, Functor.const_obj_obj, LocallyConstant.coe_comap, Set.preimage_comp,
    LocallyConstant.ofIsClopen_fiber_zero]
  erw [← h]
open Classical in
theorem exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C)
    (f : LocallyConstant C.pt α) : ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _) := by
  cases nonempty_fintype α
  let ι : α → α → Fin 2 := fun x y => if x = y then 0 else 1
  let ff := (f.map ι).flip
  have hff := fun a : α => exists_locallyConstant_fin_two _ hC (ff a)
  choose j g h using hff
  let G : Finset J := Finset.univ.image j
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists G
  have hj : ∀ a, j a ∈ (Finset.univ.image j : Finset J) := by
    intro a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
  let fs : ∀ a : α, j0 ⟶ j a := fun a => (hj0 (hj a)).some
  let gg : α → LocallyConstant (F.obj j0) (Fin 2) := fun a => (g a).comap (F.map (fs _))
  let ggg := LocallyConstant.unflip gg
  refine ⟨j0, ggg, ?_⟩
  have : f.map ι = LocallyConstant.unflip (f.map ι).flip := by simp
  rw [this]; clear this
  have :
    LocallyConstant.comap (C.π.app j0) ggg =
      LocallyConstant.unflip (LocallyConstant.comap (C.π.app j0) ggg).flip := by
    simp
  rw [this]; clear this
  congr 1
  ext1 a
  change ff a = _
  rw [h]
  dsimp
  ext1 x
  change _ = (g a) ((C.π.app j0 ≫ F.map (fs a)) x)
  rw [C.w]; rfl
theorem exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
    (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  inhabit α
  obtain ⟨j, gg, h⟩ := exists_locallyConstant_finite_aux _ hC f
  classical
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.choose else default
  refine ⟨j, gg.map σ, ?_⟩
  ext x
  simp only [Functor.const_obj_obj, LocallyConstant.coe_comap, LocallyConstant.map_apply,
    Function.comp_apply]
  dsimp [σ]
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    rw [h]
    rfl
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  erw [dif_pos h2]
  apply_fun ι
  · rw [h2.choose_spec]
    exact h1
  · intro a b hh
    have hhh := congr_fun hh a
    dsimp [ι] at hhh
    rw [if_pos rfl] at hhh
    split_ifs at hhh with hh1
    · exact hh1.symm
    · exact False.elim (bot_ne_top hhh)
theorem exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  let S := f.discreteQuotient
  let ff : S → α := f.lift
  cases isEmpty_or_nonempty S
  · suffices ∃ j, IsEmpty (F.obj j) by
      refine this.imp fun j hj => ?_
      refine ⟨⟨hj.elim, fun A => ?_⟩, ?_⟩
      · suffices (fun a ↦ IsEmpty.elim hj a) ⁻¹' A = ∅ by
          rw [this]
          exact isOpen_empty
        exact @Set.eq_empty_of_isEmpty _ hj _
      · ext x
        exact hj.elim' (C.π.app j x)
    simp only [← not_nonempty_iff, ← not_forall]
    intro h
    haveI : ∀ j : J, Nonempty ((F ⋙ Profinite.toTopCat).obj j) := h
    haveI : ∀ j : J, T2Space ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : T2Space (F.obj j))
    haveI : ∀ j : J, CompactSpace ((F ⋙ Profinite.toTopCat).obj j) := fun j =>
      (inferInstance : CompactSpace (F.obj j))
    have cond := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u}
      (F ⋙ Profinite.toTopCat)
    suffices Nonempty C.pt from IsEmpty.false (S.proj this.some)
    let D := Profinite.toTopCat.mapCone C
    have hD : IsLimit D := isLimitOfPreserves Profinite.toTopCat hC
    have CD := (hD.conePointUniqueUpToIso (TopCat.limitConeIsLimit.{v, max u v} _)).inv
    exact cond.map CD
  · let f' : LocallyConstant C.pt S := ⟨S.proj, S.proj_isLocallyConstant⟩
    obtain ⟨j, g', hj⟩ := exists_locallyConstant_finite_nonempty _ hC f'
    refine ⟨j, ⟨ff ∘ g', g'.isLocallyConstant.comp _⟩, ?_⟩
    ext1 t
    apply_fun fun e => e t at hj
    dsimp at hj ⊢
    rw [← hj]
    rfl
end Profinite