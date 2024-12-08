import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Basic
universe u v w w₁
namespace DirectSum
open DFinsupp
open scoped DirectSum
variable {R : Type u} {ι : Type v} [CommRing R]
section Modules
variable {L : Type w₁} {M : ι → Type w}
variable [LieRing L] [LieAlgebra R L]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]
instance : LieRingModule L (⨁ i, M i) where
  bracket x m := m.mapRange (fun _ m' => ⁅x, m'⁆) fun _ => lie_zero x
  add_lie x y m := by
    refine DFinsupp.ext fun _ => ?_ 
    simp only [mapRange_apply, add_apply, add_lie]
  lie_add x m n := by
    refine DFinsupp.ext fun _ => ?_ 
    simp only [mapRange_apply, add_apply, lie_add]
  leibniz_lie x y m := by
    refine DFinsupp.ext fun _ => ?_ 
    simp only [mapRange_apply, lie_lie, add_apply, sub_add_cancel]
@[simp]
theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m i⁆ :=
  mapRange_apply _ _ m i
instance : LieModule R L (⨁ i, M i) where
  smul_lie t x m := by
    refine DFinsupp.ext fun _ => ?_ 
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul t x m := by
    refine DFinsupp.ext fun _ => ?_ 
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]
variable (R ι L M)
def lieModuleOf [DecidableEq ι] (j : ι) : M j →ₗ⁅R,L⁆ ⨁ i, M i :=
  { lof R ι M j with
    map_lie' := fun {x m} => by
      refine DFinsupp.ext fun i => ?_ 
      by_cases h : j = i
      · rw [← h]; simp
      · 
        simp only [lof, lsingle, AddHom.toFun_eq_coe, lie_module_bracket_apply]
        erw [AddHom.coe_mk]
        simp [h] }
def lieModuleComponent (j : ι) : (⨁ i, M i) →ₗ⁅R,L⁆ M j :=
  { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }
end Modules
section Algebras
variable (L : ι → Type w)
variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]
instance lieRing : LieRing (⨁ i, L i) :=
  { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun _ => fun x y => ⁅x, y⁆) fun _ => lie_zero 0
    add_lie := fun x y z => by
      refine DFinsupp.ext fun _ => ?_ 
      simp only [zipWith_apply, add_apply, add_lie]
    lie_add := fun x y z => by
      refine DFinsupp.ext fun _ => ?_ 
      simp only [zipWith_apply, add_apply, lie_add]
    lie_self := fun x => by
      refine DFinsupp.ext fun _ => ?_ 
      simp only [zipWith_apply, add_apply, lie_self, zero_apply]
    leibniz_lie := fun x y z => by
      refine DFinsupp.ext fun _ => ?_ 
      simp only [sub_apply, zipWith_apply, add_apply, zero_apply]
      apply leibniz_lie }
@[simp]
theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ :=
  zipWith_apply _ _ x y i
theorem lie_of_same [DecidableEq ι] {i : ι} (x y : L i) :
    ⁅of L i x, of L i y⁆ = of L i ⁅x, y⁆ :=
  DFinsupp.zipWith_single_single _ _ _ _
theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i ≠ j) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = 0 := by
  refine DFinsupp.ext fun k => ?_
  rw [bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [of_eq_of_ne _ _ _ hij.symm, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]
@[simp]
theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = if hij : i = j then of L i ⁅x, hij.symm.recOn y⁆ else 0 := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [lie_of_same L x y, dif_pos]
  · simp only [lie_of_of_ne L hij x y, hij, dif_neg, dite_false]
instance lieAlgebra : LieAlgebra R (⨁ i, L i) :=
  { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      refine DFinsupp.ext fun _ => ?_ 
      simp only [zipWith_apply, smul_apply, bracket_apply, lie_smul] }
variable (R ι)
@[simps]
def lieAlgebraOf [DecidableEq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
  { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => by
      refine DFinsupp.ext fun i => ?_ 
      by_cases h : j = i
      · rw [← h]
        simp only [of, singleAddHom, bracket_apply]
        erw [AddHom.coe_mk, single_apply, single_apply]
        · simp? [h] says simp only [h, ↓reduceDIte, single_apply]
        · intros
          rw [single_add]
      · 
        simp only [of, singleAddHom, bracket_apply]
        erw [AddHom.coe_mk, single_apply, single_apply]
        · simp only [h, dite_false, single_apply, lie_self]
        · intros
          rw [single_add] }
@[simps]
def lieAlgebraComponent (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
  { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }
@[ext (iff := false)]
theorem lieAlgebra_ext {x y : ⨁ i, L i}
    (h : ∀ i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y) : x = y :=
  DFinsupp.ext h
variable {R L ι}
@[simps]
def toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
    (f : ∀ i, L i →ₗ⁅R⁆ L') (hf : Pairwise fun i j => ∀ (x : L i) (y : L j), ⁅f i x, f j y⁆ = 0) :
    (⨁ i, L i) →ₗ⁅R⁆ L' :=
  { toModule R ι L' fun i => (f i : L i →ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i →ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i →ₗ[R] L')
      suffices ∀ (i : ι) (y : L i),
          toModule R ι L' f' ⁅x, of L i y⁆ =
            ⁅toModule R ι L' f' x, toModule R ι L' f' (of L i y)⁆ by
        simp only [← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear y; ext i y; exact this i y
      suffices ∀ (i j) (y : L i) (x : L j),
          toModule R ι L' f' ⁅of L j x, of L i y⁆ =
            ⁅toModule R ι L' f' (of L j x), toModule R ι L' f' (of L i y)⁆ by
        intro i y
        rw [← lie_skew x, ← lie_skew (toModule R ι L' f' x)]
        simp only [LinearMap.map_neg, neg_inj, ← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear x; ext j x; exact this j i x y
      intro i j y x
      simp only [f', coe_toModule_eq_coe_toAddMonoid, toAddMonoid_of]
      obtain rfl | hij := Decidable.eq_or_ne i j
      · simp_rw [lie_of_same, toAddMonoid_of, LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
          LieHom.map_lie]
      · simp_rw [lie_of_of_ne _ hij.symm, map_zero,  LinearMap.toAddMonoidHom_coe,
          LieHom.coe_toLinearMap, hf hij.symm x y] }
end Algebras
section Ideals
variable {L : Type w} [LieRing L] [LieAlgebra R L] (I : ι → LieIdeal R L)
instance lieRingOfIdeals : LieRing (⨁ i, I i) :=
  DirectSum.lieRing fun i => ↥(I i)
instance lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i) :=
  DirectSum.lieAlgebra fun i => ↥(I i)
end Ideals
end DirectSum