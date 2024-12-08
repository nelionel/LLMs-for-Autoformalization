import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Filtered.Basic
open CategoryTheory CategoryTheory.Limits
universe v u w
namespace CategoryTheory.Limits.Types.FilteredColimit
variable {J : Type v} [Category.{w} J] (F : J ⥤ Type u)
attribute [local instance] small_quot_of_hasColimit
protected def Rel (x y : Σ j, F.obj j) : Prop :=
  ∃ (k : _) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2
theorem rel_of_quot_rel (x y : Σ j, F.obj j) :
    Quot.Rel F x y → FilteredColimit.Rel.{v, u} F x y :=
  fun ⟨f, h⟩ => ⟨y.1, f, 𝟙 y.1, by rw [← h, FunctorToTypes.map_id_apply]⟩
theorem eqvGen_quot_rel_of_rel (x y : Σ j, F.obj j) :
    FilteredColimit.Rel.{v, u} F x y → Relation.EqvGen (Quot.Rel F) x y := fun ⟨k, f, g, h⟩ => by
  refine Relation.EqvGen.trans _ ⟨k, F.map f x.2⟩ _ ?_ ?_
  · exact (Relation.EqvGen.rel _ _ ⟨f, rfl⟩)
  · exact (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨g, h⟩))
noncomputable def isColimitOf (t : Cocone F) (hsurj : ∀ x : t.pt, ∃ i xi, x = t.ι.app i xi)
    (hinj :
      ∀ i j xi xj,
        t.ι.app i xi = t.ι.app j xj → ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) :
    IsColimit t := by
  let α : t.pt → J := fun x => (hsurj x).choose
  let f : ∀ (x : t.pt), F.obj (α x) := fun x => (hsurj x).choose_spec.choose
  have hf : ∀ (x : t.pt), x = t.ι.app _ (f x) := fun x => (hsurj x).choose_spec.choose_spec
  exact
    { desc := fun s x => s.ι.app _ (f x)
      fac := fun s j => by
        ext y
        obtain ⟨k, l, g, eq⟩ := hinj _ _ _ _ (hf (t.ι.app j y))
        have h := congr_fun (s.ι.naturality g) (f (t.ι.app j y))
        have h' := congr_fun (s.ι.naturality l) y
        dsimp at h h' ⊢
        rw [← h, ← eq, h']
      uniq := fun s m hm => by
        ext x
        dsimp
        nth_rw 1 [hf x]
        rw [← hm, types_comp_apply] }
variable [IsFilteredOrEmpty J]
protected theorem rel_equiv : _root_.Equivalence (FilteredColimit.Rel.{v, u} F) where
  refl x := ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩
  symm := fun ⟨k, f, g, h⟩ => ⟨k, g, f, h.symm⟩
  trans {x y z} := fun ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩ =>
    let ⟨l, fl, gl, _⟩ := IsFilteredOrEmpty.cocone_objs k k'
    let ⟨m, n, hn⟩ := IsFilteredOrEmpty.cocone_maps (g ≫ fl) (f' ≫ gl)
    ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n,
      calc
        F.map (f ≫ fl ≫ n) x.2 = F.map (fl ≫ n) (F.map f x.2) := by simp
        _ = F.map (fl ≫ n) (F.map g y.2) := by rw [h]
        _ = F.map ((g ≫ fl) ≫ n) y.2 := by simp
        _ = F.map ((f' ≫ gl) ≫ n) y.2 := by rw [hn]
        _ = F.map (gl ≫ n) (F.map f' y.2) := by simp
        _ = F.map (gl ≫ n) (F.map g' z.2) := by rw [h']
        _ = F.map (g' ≫ gl ≫ n) z.2 := by simp⟩
protected theorem rel_eq_eqvGen_quot_rel :
    FilteredColimit.Rel.{v, u} F = Relation.EqvGen (Quot.Rel F) := by
  ext ⟨j, x⟩ ⟨j', y⟩
  constructor
  · apply eqvGen_quot_rel_of_rel
  · rw [← (FilteredColimit.rel_equiv F).eqvGen_iff]
    exact Relation.EqvGen.mono (rel_of_quot_rel F)
variable [HasColimit F]
theorem colimit_eq_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
    (colimitCocone F).ι.app i xi = (colimitCocone F).ι.app j xj ↔
      FilteredColimit.Rel.{v, u} F ⟨i, xi⟩ ⟨j, xj⟩ := by
  dsimp
  rw [← (equivShrink _).symm.injective.eq_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Quot.eq, FilteredColimit.rel_eq_eqvGen_quot_rel]
theorem isColimit_eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j} :
    t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj := by
  refine Iff.trans ?_ (colimit_eq_iff_aux F)
  rw [← (IsColimit.coconePointUniqueUpToIso ht (colimitCoconeIsColimit F)).toEquiv.injective.eq_iff]
  convert Iff.rfl
  · exact (congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom ht (colimitCoconeIsColimit F) _) xi).symm
  · exact (congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom ht (colimitCoconeIsColimit F) _) xj).symm
theorem colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
  isColimit_eq_iff _ (colimit.isColimit F)
end CategoryTheory.Limits.Types.FilteredColimit