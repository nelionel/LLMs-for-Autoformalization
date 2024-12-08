import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
universe v u
open CategoryTheory
open Simplicial SimplicialObject SimplexCategory
namespace SSet
variable (X : SSet.{u})
class StrictSegal where
  spineToSimplex {n : ℕ} : Path X n → X _[n]
  spine_spineToSimplex {n : ℕ} (f : Path X n) : X.spine n (spineToSimplex f) = f
  spineToSimplex_spine {n : ℕ} (Δ : X _[n]) : spineToSimplex (X.spine n Δ) = Δ
namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}
def spineEquiv (n : ℕ) : X _[n] ≃ Path X n where
  toFun := spine X n
  invFun := spineToSimplex
  left_inv := spineToSimplex_spine
  right_inv := spine_spineToSimplex
theorem spineInjective {n : ℕ} : Function.Injective (spineEquiv (X := X) n) := Equiv.injective _
@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spine_spineToSimplex]
@[simp]
theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spine_spineToSimplex]
def spineToDiagonal (f : Path X n) : X _[1] := diagonal X (spineToSimplex f)
@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l ≤  n)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply spineInjective
  unfold spineEquiv
  dsimp
  rw [spine_spineToSimplex]
  convert spine_map_subinterval X j l hjl (spineToSimplex f)
  exact Eq.symm (spine_spineToSimplex f)
theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) :
    X.map (intervalEdge j l hjl).op (spineToSimplex f) =
      spineToDiagonal (Path.interval f j l hjl) := by
  unfold spineToDiagonal
  rw [← congrArg (diagonal X) (spineToSimplex_interval f j l hjl)]
  unfold diagonal
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, diag_subinterval_eq]
lemma spineToSimplex_map {X Y : SSet.{u}} [StrictSegal X] [StrictSegal Y]
    {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) :
    spineToSimplex (f.map σ) = σ.app _ (spineToSimplex f) := by
  apply spineInjective
  ext k
  dsimp only [spineEquiv, Equiv.coe_fn_mk, Path.map, spine_arrow]
  rw [← types_comp_apply (σ.app _) (Y.map _), ← σ.naturality]
  simp only [types_comp_apply, spineToSimplex_arrow]
lemma spine_δ_vertex_lt (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : i.castSucc < j) :
    (X.spine n (X.δ j (spineToSimplex f))).vertex i = f.vertex i.castSucc := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_castSucc_lt j i h]
lemma spine_δ_vertex_ge (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)}
    (h : j ≤ i.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).vertex i = f.vertex i.succ := by
  simp only [SimplicialObject.δ, spine_vertex]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, const_comp, spineToSimplex_vertex]
  simp only [SimplexCategory.δ, Hom.toOrderHom, len_mk, mkHom, Hom.mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_of_le_castSucc j i h]
lemma spine_δ_arrow_lt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i = f.arrow i.castSucc := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_lt h, spineToSimplex_arrow]
lemma spine_δ_arrow_gt (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i = f.arrow i.succ := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_gt h, spineToSimplex_arrow]
lemma spine_δ_arrow_eq (f : Path X (n + 1)) {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    (X.spine n (X.δ j (spineToSimplex f))).arrow i =
      spineToDiagonal (Path.interval f i 2 (by omega)) := by
  simp only [SimplicialObject.δ, spine_arrow]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [mkOfSucc_δ_eq h, spineToSimplex_edge]
end StrictSegal
end SSet
namespace CategoryTheory.Nerve
open SSet
noncomputable instance strictSegal (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  spineToSimplex {n} F :=
    ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
      (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
        (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
  spine_spineToSimplex {n} F := by
    ext i
    · exact ComposableArrows.ext₀ rfl
    · refine ComposableArrows.ext₁ ?_ ?_ ?_
      · exact Functor.congr_obj (F.arrow_src i).symm 0
      · exact Functor.congr_obj (F.arrow_tgt i).symm 0
      · dsimp
        apply ComposableArrows.mkOfObjOfMapSucc_map_succ
  spineToSimplex_spine {n} F := by
    fapply ComposableArrows.ext
    · intro i
      rfl
    · intro i hi
      apply ComposableArrows.mkOfObjOfMapSucc_map_succ
end CategoryTheory.Nerve