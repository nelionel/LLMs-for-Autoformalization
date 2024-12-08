import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.FinCases
open CategoryTheory Category SimplicialObject.Augmented Opposite Simplicial
namespace SimplicialObject
namespace Augmented
variable {C : Type*} [Category C]
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  s' : point.obj X ⟶ drop.obj X _[0]
  s : ∀ n : ℕ, drop.obj X _[n] ⟶ drop.obj X _[n + 1]
  s'_comp_ε : s' ≫ X.hom.app (op [0]) = 𝟙 _
  s₀_comp_δ₁ : s 0 ≫ X.left.δ 1 = X.hom.app (op [0]) ≫ s'
  s_comp_δ₀ : ∀ n : ℕ, s n ≫ X.left.δ 0 = 𝟙 _
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.succ = X.left.δ i ≫ s n
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.succ = X.left.σ i ≫ s (n + 1)
namespace ExtraDegeneracy
attribute [reassoc] s₀_comp_δ₁ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ₀
def map {D : Type*} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    dsimp
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₁ := by
    dsimp
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
  s_comp_δ₀ n := by
    dsimp
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
  s_comp_δ n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    rfl
  s_comp_σ n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    rfl
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op [0])
  s n := (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op [n + 1])
  s'_comp_ε := by
    simpa only [Functor.mapIso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.mapIso e).inv_hom_id
  s₀_comp_δ₁ := by
    have h := w₀ e.inv
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of% h]
  s_comp_δ₀ n := by
    have h := ed.s_comp_δ₀
    dsimp at h ⊢
    simpa only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h] using
      congr_app (drop.mapIso e).inv_hom_id (op [n])
  s_comp_δ n i := by
    have h := ed.s_comp_δ n i
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.δ_naturality, reassoc_of% h,
      ← SimplicialObject.δ_naturality_assoc]
  s_comp_σ n i := by
    have h := ed.s_comp_σ n i
    dsimp at h ⊢
    simp only [assoc, ← SimplicialObject.σ_naturality, reassoc_of% h,
      ← SimplicialObject.σ_naturality_assoc]
end ExtraDegeneracy
end Augmented
end SimplicialObject
namespace SSet
namespace Augmented
namespace StandardSimplex
def shiftFun {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin (n + 1)) : X :=
  dite (i = 0) (fun _ => 0) fun h => f (i.pred h)
@[simp]
theorem shiftFun_0 {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) : shiftFun f 0 = 0 :=
  rfl
@[simp]
theorem shiftFun_succ {n : ℕ} {X : Type*} [Zero X] (f : Fin n → X) (i : Fin n) :
    shiftFun f i.succ = f i := by
  dsimp [shiftFun]
  split_ifs with h
  · exfalso
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false, reduceCtorEq] at h
  · simp only [Fin.pred_succ]
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory}
    (f : ([n] : SimplexCategory) ⟶ Δ) : ([n + 1] : SimplexCategory) ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        · subst h₁
          simp only [shiftFun_0, Fin.zero_le]
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          cases' Fin.eq_succ_of_ne_zero h₁ with j₁ hj₁
          cases' Fin.eq_succ_of_ne_zero h₂ with j₂ hj₂
          substs hj₁ hj₂
          simpa only [shiftFun_succ] using f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hi) }
open SSet.standardSimplex in
protected noncomputable def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ) where
  s' _ := objMk (OrderHom.const _ 0)
  s  _ f := (objEquiv _ _).symm
    (shift (objEquiv _ _ f))
  s'_comp_ε := by
    dsimp
    subsingleton
  s₀_comp_δ₁ := by
    dsimp
    ext1 x
    apply (objEquiv _ _).injective
    ext j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext i : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    simp only [shiftFun_succ]
  s_comp_δ n i := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.δ, SimplexCategory.δ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    by_cases h : j = 0
    · subst h
      simp only [Fin.succ_succAbove_zero, shiftFun_0]
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero <| h
      simp only [Fin.succ_succAbove_succ, shiftFun_succ, Function.comp_apply,
        Fin.succAboveOrderEmb_apply]
  s_comp_σ n i := by
    ext1 φ
    apply (objEquiv _ _).injective
    apply SimplexCategory.Hom.ext
    ext j : 2
    dsimp [SimplicialObject.σ, SimplexCategory.σ, SSet.standardSimplex,
      objEquiv, Equiv.ulift, uliftFunctor]
    by_cases h : j = 0
    · subst h
      rfl
    · obtain ⟨_, rfl⟩ := Fin.eq_succ_of_ne_zero h
      simp only [Fin.succ_predAbove_succ, shiftFun_succ, Function.comp_apply]
instance nonempty_extraDegeneracy_standardSimplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)) :=
  ⟨StandardSimplex.extraDegeneracy Δ⟩
end StandardSimplex
end Augmented
end SSet
namespace CategoryTheory
open Limits
namespace Arrow
namespace AugmentedCechNerve
variable {C : Type*} [Category C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  (S : SplitEpi f.hom)
noncomputable def ExtraDegeneracy.s (n : ℕ) :
    f.cechNerve.obj (op [n]) ⟶ f.cechNerve.obj (op [n + 1]) :=
  WidePullback.lift (WidePullback.base _)
    (fun i =>
      dite (i = 0)
        (fun _ => WidePullback.base _ ≫ S.section_)
        (fun h => WidePullback.π _ (i.pred h)))
    fun i => by
      dsimp
      split_ifs with h
      · subst h
        simp only [assoc, SplitEpi.id, comp_id]
      · simp only [WidePullback.π_arrow]
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 =
      @WidePullback.base _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ ≫
        S.section_ := by
  dsimp [ExtraDegeneracy.s]
  simp only [WidePullback.lift_π]
  rfl
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ =
      @WidePullback.π _ _ _ f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) _ i := by
  dsimp [ExtraDegeneracy.s]
  simp only [WidePullback.lift_π]
  split_ifs with h
  · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, add_eq_zero, and_false, reduceCtorEq] at h
  · simp only [Fin.pred_succ]
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply WidePullback.lift_base
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve where
  s' := S.section_ ≫ WidePullback.lift f.hom (fun _ => 𝟙 _) fun i => by rw [id_comp]
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε := by
    dsimp
    simp only [augmentedCechNerve_hom_app, assoc, WidePullback.lift_base, SplitEpi.id]
  s₀_comp_δ₁ := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simpa only [assoc, WidePullback.lift_π, comp_id] using ExtraDegeneracy.s_comp_π_0 f S 0
    · simpa only [assoc, WidePullback.lift_base, SplitEpi.id, comp_id] using
        ExtraDegeneracy.s_comp_base f S 0
  s_comp_δ₀ n := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · simpa only [assoc, WidePullback.lift_π, id_comp] using ExtraDegeneracy.s_comp_π_succ f S n j
    · simpa only [assoc, WidePullback.lift_base, id_comp] using ExtraDegeneracy.s_comp_base f S n
  s_comp_δ n i := by
    dsimp [cechNerve, SimplicialObject.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, WidePullback.lift_π]
      by_cases h : j = 0
      · subst h
        erw [Fin.succ_succAbove_zero, ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_succAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
    · simp only [assoc, WidePullback.lift_base]
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      dsimp
      simp only [WidePullback.lift_base]
  s_comp_σ n i := by
    dsimp [cechNerve, SimplicialObject.σ, SimplexCategory.σ]
    ext j
    · simp only [assoc, WidePullback.lift_π]
      by_cases h : j = 0
      · subst h
        erw [ExtraDegeneracy.s_comp_π_0, ExtraDegeneracy.s_comp_π_0]
        dsimp
        simp only [WidePullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_predAbove_succ, ExtraDegeneracy.s_comp_π_succ,
          ExtraDegeneracy.s_comp_π_succ]
        simp only [WidePullback.lift_π]
    · simp only [assoc, WidePullback.lift_base]
      erw [ExtraDegeneracy.s_comp_base, ExtraDegeneracy.s_comp_base]
      dsimp
      simp only [WidePullback.lift_base]
end AugmentedCechNerve
end Arrow
end CategoryTheory
namespace SimplicialObject
namespace Augmented
namespace ExtraDegeneracy
open AlgebraicTopology CategoryTheory Limits
noncomputable def homotopyEquiv {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X)) where
  hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    dsimp
    erw [AlternatingFaceMapComplex.ε_app_f_zero,
      ChainComplex.fromSingle₀Equiv_symm_apply_f_zero, s'_comp_ε]
    rfl)
  homotopyHomInvId :=
    { hom := fun i j => by
        by_cases i + 1 = j
        · exact (-ed.s i) ≫ eqToHom (by congr)
        · exact 0
      zero := fun i j hij => by
        dsimp
        split_ifs with h
        · exfalso
          exact hij h
        · simp only [eq_self_iff_true]
      comm := fun i => by
        rcases i with _|i
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          dsimp
          erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
          simp only [comp_id, ite_true, zero_add, ComplexShape.down_Rel, not_true,
            AlternatingFaceMapComplex.obj_d_eq, Preadditive.neg_comp]
          rw [Fin.sum_univ_two]
          simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
            Preadditive.comp_add, s_comp_δ₀, drop_obj, Preadditive.comp_neg, neg_add_rev,
            neg_neg, neg_add_cancel_right, s₀_comp_δ₁,
            AlternatingFaceMapComplex.ε_app_f_zero]
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          dsimp
          simp only [Preadditive.neg_comp,
            AlternatingFaceMapComplex.obj_d_eq, comp_id, ite_true, Preadditive.comp_neg,
            @Fin.sum_univ_succ _ _ (i + 2), Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
            Preadditive.comp_add, drop_obj, s_comp_δ₀, Preadditive.sum_comp,
            Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
            zsmul_neg, s_comp_δ, pow_add, pow_one, mul_neg, mul_one, neg_zsmul, neg_neg,
            neg_add_cancel_comm_assoc, neg_add_cancel, zero_comp] }
end ExtraDegeneracy
end Augmented
end SimplicialObject