import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.Basic
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Opposite
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Abelian C]
attribute [local instance] Abelian.hasPullbacks
namespace NormalizedMooreComplex
open CategoryTheory.Subobject
variable (X : SimplicialObject C)
def objX : ∀ n : ℕ, Subobject (X.obj (op (SimplexCategory.mk n)))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)
@[simp] theorem objX_zero : objX X 0 = ⊤ :=
  rfl
@[simp] theorem objX_add_one (n) :
    objX X (n + 1) = Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ) :=
  rfl
@[simp]
def objD : ∀ n : ℕ, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 => by
    refine factorThru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) ?_
    refine (finset_inf_factors _).mpr fun i _ => ?_
    apply kernelSubobject_factors
    dsimp [objX]
    erw [Category.assoc, ← X.δ_comp_δ (Fin.zero_le i.succ)]
    rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  rcases n with _ | n <;> dsimp [objD]
  · erw [Subobject.factorThru_arrow_assoc, Category.assoc,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
  · erw [factorThru_right, factorThru_eq_zero, factorThru_arrow_assoc, Category.assoc,
      ← X.δ_comp_δ (Fin.zero_le (0 : Fin (n + 3))),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
@[simps!]
def obj (X : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (objX X n : C))
    (
      objD X) (d_squared X)
variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)
@[simps!]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ (arrow _ ≫ f.app (op (SimplexCategory.mk n))) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        erw [Category.assoc, ← f.naturality,
          ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp)),
          Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]))
    fun n => by
    cases n <;> dsimp [objD, objX] <;> aesop_cat
end NormalizedMooreComplex
open NormalizedMooreComplex
variable (C)
@[simps]
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := map f
  map_id X := by ext (_ | _) <;> dsimp <;> aesop_cat
  map_comp f g := by ext (_ | _) <;> apply Subobject.eq_of_comp_arrow_eq <;> dsimp <;> aesop_cat
variable {C}
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n :=
  ChainComplex.of_d _ _ (d_squared X) n
end AlgebraicTopology