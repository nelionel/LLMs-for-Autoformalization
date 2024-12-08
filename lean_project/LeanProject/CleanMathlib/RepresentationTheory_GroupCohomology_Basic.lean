import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.GroupCohomology.Resolution
noncomputable section
universe u
variable {k G : Type u} [CommRing k] {n : ℕ}
open CategoryTheory
namespace groupCohomology
variable [Monoid G]
abbrev linearYonedaObjResolution (A : Rep k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (groupCohomology.resolution k G).linearYonedaObj k A
theorem linearYonedaObjResolution_d_apply {A : Rep k G} (i j : ℕ) (x : (resolution k G).X i ⟶ A) :
    (linearYonedaObjResolution A).d i j x = (resolution k G).d j i ≫ x :=
  rfl
end groupCohomology
namespace inhomogeneousCochains
open Rep groupCohomology
@[simps]
def d [Monoid G] (n : ℕ) (A : Rep k G) : ((Fin n → G) → A) →ₗ[k] (Fin (n + 1) → G) → A where
  toFun f g :=
    A.ρ (g 0) (f fun i => g i.succ) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f g := by
    ext x
    simp_rw [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    ext x
    simp_rw [Pi.smul_apply, RingHom.id_apply, map_smul, smul_add, Finset.smul_sum, ← smul_assoc,
      smul_eq_mul, mul_comm r]
variable [Group G] (n) (A : Rep k G)
@[nolint checkType] theorem d_eq :
    d n A =
      (diagonalHomEquiv n A).toModuleIso.inv ≫
        (linearYonedaObjResolution A).d n (n + 1) ≫
          (diagonalHomEquiv (n + 1) A).toModuleIso.hom := by
  ext f g
  change d n A f g = diagonalHomEquiv (n + 1) A
    ((resolution k G).d (n + 1) n ≫ (diagonalHomEquiv n A).symm f) g
  rw [diagonalHomEquiv_apply, Action.comp_hom, ModuleCat.comp_def, LinearMap.comp_apply,
    resolution.d_eq]
  erw [resolution.d_of (Fin.partialProd g)]
  simp only [map_sum, ← Finsupp.smul_single_one _ ((-1 : k) ^ _)]
  erw [d_apply, @Fin.sum_univ_succ _ _ (n + 1), Fin.val_zero, pow_zero, one_smul,
    Fin.succAbove_zero, diagonalHomEquiv_symm_apply f (Fin.partialProd g ∘ @Fin.succ (n + 1))]
  simp_rw [Function.comp_apply, Fin.partialProd_succ, Fin.castSucc_zero,
    Fin.partialProd_zero, one_mul]
  rcongr x
  · have := Fin.partialProd_right_inv g (Fin.castSucc x)
    simp only [mul_inv_rev, Fin.castSucc_fin_succ] at this ⊢
    rw [mul_assoc, ← mul_assoc _ _ (g x.succ), this, inv_mul_cancel_left]
  · 
    erw [map_smul, diagonalHomEquiv_symm_partialProd_succ, Fin.val_succ]
end inhomogeneousCochains
namespace groupCohomology
variable [Group G] (n) (A : Rep k G)
open inhomogeneousCochains
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d n A) fun n => by
    ext x
    have := LinearMap.ext_iff.1 ((linearYonedaObjResolution A).d_comp_d n (n + 1) (n + 2))
    simp only [ModuleCat.comp_def, LinearMap.comp_apply] at this
    dsimp only
    simp only [d_eq, LinearEquiv.toModuleIso_inv, LinearEquiv.toModuleIso_hom, ModuleCat.coe_comp,
      Function.comp_apply]
    erw [LinearEquiv.symm_apply_apply, this]
    exact map_zero _
@[simp]
theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = inhomogeneousCochains.d n A :=
  CochainComplex.of_d _ _ _ _
def inhomogeneousCochainsIso : inhomogeneousCochains A ≅ linearYonedaObjResolution A := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    (Rep.diagonalHomEquiv i A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp only [CochainComplex.of_d, d_eq, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
    Category.comp_id]
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ ModuleCat.of k ((Fin n → G) → A) :=
  (inhomogeneousCochains A).iCycles n
abbrev toCocycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) → A) ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j
end groupCohomology
open groupCohomology
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n
abbrev groupCohomologyπ [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (extIso k G A n).symm