import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Kaehler.Basic
universe v u
open CategoryTheory
attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid
namespace ModuleCat
variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)
nonrec def Derivation : Type _ :=
  letI := f.toAlgebra
  letI := Module.compHom M f
  Derivation A B M
namespace Derivation
variable {M f}
def mk (d : B → M) (d_add : ∀ (b b' : B), d (b + b') = d b + d b' := by simp)
    (d_mul : ∀ (b b' : B), d (b * b') = b • d b' + b' • d b := by simp)
    (d_map : ∀ (a : A), d (f a) = 0 := by simp) :
    M.Derivation f :=
  letI := f.toAlgebra
  letI := Module.compHom M f
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b ↦ by
      dsimp
      erw [d_mul, d_map, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.map_one, d_map]
    leibniz' := d_mul }
variable (D : M.Derivation f)
def d (b : B) : M :=
  letI := f.toAlgebra
  letI := Module.compHom M f
  _root_.Derivation.toLinearMap D b
@[simp]
lemma d_add (b b' : B) : D.d (b + b') = D.d b + D.d b' := by simp [d]
@[simp]
lemma d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b := by simp [d]
@[simp]
lemma d_map (a : A) : D.d (f a) = 0 :=
  letI := f.toAlgebra
  letI := Module.compHom M f
  D.map_algebraMap a
end Derivation
end ModuleCat
namespace CommRingCat
variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')
variable (f) in
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)
namespace KaehlerDifferential
variable (f) in
noncomputable def D : (KaehlerDifferential f).Derivation f :=
  letI := f.toAlgebra
  ModuleCat.Derivation.mk
    (fun b ↦ _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap
noncomputable abbrev d (b : B) : KaehlerDifferential f := (D f).d b
@[ext]
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (d b) = β (d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ ≤ LinearMap.ker (α - β) := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    apply h
  rw [top_le_iff, LinearMap.ker_eq_top] at this
  exact this
noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g').obj (KaehlerDifferential f') :=
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (g ≫ f').toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' fac
  { toFun := fun x ↦ _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }
@[simp]
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (f'.comp g).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' fac
  exact _root_.KaehlerDifferential.map_D A A' B B' b
end KaehlerDifferential
end CommRingCat
namespace ModuleCat.Derivation
variable {A B : CommRingCat.{u}} {f : A ⟶ B}
  {M : ModuleCat.{u} B} (D : M.Derivation f)
noncomputable def desc : CommRingCat.KaehlerDifferential f ⟶ M :=
  letI := f.toAlgebra
  letI := Module.compHom M f
  D.liftKaehlerDifferential
@[simp]
lemma desc_d (b : B) : D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b := by
  letI := f.toAlgebra
  letI := Module.compHom M f
  apply D.liftKaehlerDifferential_comp_D
end ModuleCat.Derivation