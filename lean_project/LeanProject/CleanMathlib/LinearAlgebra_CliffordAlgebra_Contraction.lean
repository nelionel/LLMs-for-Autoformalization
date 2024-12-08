import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Dual
open LinearMap (BilinMap BilinForm)
universe u1 u2 u3
variable {R : Type u1} [CommRing R]
variable {M : Type u2} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
namespace CliffordAlgebra
section contractLeft
variable (d d' : Module.Dual R M)
@[simps!]
def contractLeftAux (d : Module.Dual R M) :
    M →ₗ[R] CliffordAlgebra Q × CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)
theorem contractLeftAux_contractLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) :
    contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)) = Q v • fx := by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← sub_add, mul_smul_comm, sub_self,
    zero_add]
variable {Q}
def contractLeft : Module.Dual R M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun d := foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      dsimp only
      rw [LinearMap.add_apply]
      induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
      · simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      · rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [sub_add_sub_comm, mul_add, LinearMap.add_apply, add_smul]
  map_smul' c d :=
    LinearMap.ext fun x => by
      dsimp only
      rw [LinearMap.smul_apply, RingHom.id_apply]
      induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
      · simp_rw [foldr'_algebraMap, smul_zero]
      · rw [map_add, map_add, smul_add, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [LinearMap.smul_apply, smul_assoc, mul_smul_comm, smul_sub]
def contractRight : CliffordAlgebra Q →ₗ[R] Module.Dual R M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)
theorem contractRight_eq (x : CliffordAlgebra Q) :
    contractRight (Q := Q) x d = reverse (contractLeft (R := R) (M := M) d <| reverse x) :=
  rfl
local infixl:70 "⌋" => contractLeft (R := R) (M := M)
local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)
instance : SMul R (CliffordAlgebra Q) := inferInstance
theorem contractLeft_ι_mul (a : M) (b : CliffordAlgebra Q) :
    d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b) := by
  refine foldr'_ι_mul _ _ ?_ _ _ _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
theorem contractRight_mul_ι (a : M) (b : CliffordAlgebra Q) :
    b * ι Q a⌊d = d a • b - b⌊d * ι Q a := by
  rw [contractRight_eq, reverse.map_mul, reverse_ι, contractLeft_ι_mul, map_sub, map_smul,
    reverse_reverse, reverse.map_mul, reverse_ι, contractRight_eq]
theorem contractLeft_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    d⌋(algebraMap _ _ r * b) = algebraMap _ _ r * (d⌋b) := by
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
theorem contractLeft_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    d⌋(a * algebraMap _ _ r) = d⌋a * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractLeft_algebraMap_mul, Algebra.commutes]
theorem contractRight_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    algebraMap _ _ r * b⌊d = algebraMap _ _ r * (b⌊d) := by
  rw [← Algebra.smul_def, LinearMap.map_smul₂, Algebra.smul_def]
theorem contractRight_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    a * algebraMap _ _ r⌊d = a⌊d * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractRight_algebraMap_mul, Algebra.commutes]
variable (Q)
@[simp]
theorem contractLeft_ι (x : M) : d⌋ι Q x = algebraMap R _ (d x) := by
  refine (foldr'_ι _ _ ?_ _ _).trans <| by
    simp_rw [contractLeftAux_apply_apply, mul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one]
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
@[simp]
theorem contractRight_ι (x : M) : ι Q x⌊d = algebraMap R _ (d x) := by
  rw [contractRight_eq, reverse_ι, contractLeft_ι, reverse.commutes]
@[simp]
theorem contractLeft_algebraMap (r : R) : d⌋algebraMap R (CliffordAlgebra Q) r = 0 := by
  refine (foldr'_algebraMap _ _ ?_ _ _).trans <| smul_zero _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
@[simp]
theorem contractRight_algebraMap (r : R) : algebraMap R (CliffordAlgebra Q) r⌊d = 0 := by
  rw [contractRight_eq, reverse.commutes, contractLeft_algebraMap, map_zero]
@[simp]
theorem contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0 := by
  simpa only [map_one] using contractLeft_algebraMap Q d 1
@[simp]
theorem contractRight_one : (1 : CliffordAlgebra Q)⌊d = 0 := by
  simpa only [map_one] using contractRight_algebraMap Q d 1
variable {Q}
theorem contractLeft_contractLeft (x : CliffordAlgebra Q) : d⌋(d⌋x) = 0 := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [contractLeft_algebraMap, map_zero]
  · rw [map_add, map_add, hx, hy, add_zero]
  · rw [contractLeft_ι_mul, map_sub, contractLeft_ι_mul, hx, LinearMap.map_smul,
      mul_zero, sub_zero, sub_self]
theorem contractRight_contractRight (x : CliffordAlgebra Q) : x⌊d⌊d = 0 := by
  rw [contractRight_eq, contractRight_eq, reverse_reverse, contractLeft_contractLeft, map_zero]
theorem contractLeft_comm (x : CliffordAlgebra Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x)) := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  · rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  · simp only [contractLeft_ι_mul, map_sub, LinearMap.map_smul]
    rw [neg_sub, sub_sub_eq_add_sub, hx, mul_neg, ← sub_eq_add_neg]
theorem contractRight_comm (x : CliffordAlgebra Q) : x⌊d⌊d' = -(x⌊d'⌊d) := by
  rw [contractRight_eq, contractRight_eq, contractRight_eq, contractRight_eq, reverse_reverse,
    reverse_reverse, contractLeft_comm, map_neg]
end contractLeft
local infixl:70 "⌋" => contractLeft
local infixl:70 "⌊" => contractRight
@[simps!]
def changeFormAux (B : BilinForm R M) : M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B
theorem changeFormAux_changeFormAux (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q) :
    changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x := by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, map_sub, contractLeft_ι_mul, ← sub_add, sub_sub_sub_comm,
    ← Algebra.smul_def, sub_self, sub_zero, contractLeft_contractLeft, add_zero, sub_smul]
variable {Q}
variable {Q' Q'' : QuadraticForm R M} {B B' : BilinForm R M}
def changeForm (h : B.toQuadraticMap = Q' - Q) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q' :=
  foldr Q (changeFormAux Q' B)
    (fun m x =>
      (changeFormAux_changeFormAux Q' B m x).trans <| by
        dsimp only [← BilinMap.toQuadraticMap_apply]
        rw [h, QuadraticMap.sub_apply, sub_sub_cancel])
    1
theorem changeForm.zero_proof : (0 : BilinForm R M).toQuadraticMap = Q - Q :=
  (sub_self _).symm
variable (h : B.toQuadraticMap = Q' - Q) (h' : B'.toQuadraticMap = Q'' - Q')
include h h' in
theorem changeForm.add_proof : (B + B').toQuadraticMap = Q'' - Q :=
  (congr_arg₂ (· + ·) h h').trans <| sub_add_sub_cancel' _ _ _
include h in
theorem changeForm.neg_proof : (-B).toQuadraticMap = Q - Q' :=
  (congr_arg Neg.neg h).trans <| neg_sub _ _
theorem changeForm.associated_neg_proof [Invertible (2 : R)] :
    (QuadraticMap.associated (R := R) (M := M) (-Q)).toQuadraticMap = 0 - Q := by
  simp [QuadraticMap.toQuadraticMap_associated]
@[simp]
theorem changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r :=
  (foldr_algebraMap _ _ _ _ _).trans <| Eq.symm <| Algebra.algebraMap_eq_smul_one r
@[simp]
theorem changeForm_one : changeForm h (1 : CliffordAlgebra Q) = 1 := by
  simpa using changeForm_algebraMap h (1 : R)
@[simp]
theorem changeForm_ι (m : M) : changeForm h (ι (M := M) Q m) = ι (M := M) Q' m :=
  (foldr_ι _ _ _ _ _).trans <|
    Eq.symm <| by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]
theorem changeForm_ι_mul (m : M) (x : CliffordAlgebra Q) :
    changeForm h (ι (M := M) Q m * x) = ι (M := M) Q' m * changeForm h x
    - contractLeft (Q := Q') (B m) (changeForm h x) :=
  (foldr_mul _ _ _ _ _ _).trans <| by rw [foldr_ι]; rfl
theorem changeForm_ι_mul_ι (m₁ m₂ : M) :
    changeForm h (ι Q m₁ * ι Q m₂) = ι Q' m₁ * ι Q' m₂ - algebraMap _ _ (B m₁ m₂) := by
  rw [changeForm_ι_mul, changeForm_ι, contractLeft_ι]
theorem changeForm_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    changeForm h (contractLeft (Q := Q) d x) = contractLeft (Q := Q') d (changeForm h x) := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  · rw [map_add, map_add, map_add, map_add, hx, hy]
  · simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, LinearMap.map_smul]
    rw [← hx, contractLeft_comm, ← sub_add, sub_neg_eq_add, ← hx]
theorem changeForm_self_apply (x : CliffordAlgebra Q) : changeForm (Q' := Q)
    changeForm.zero_proof x = x := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [changeForm_algebraMap]
  · rw [map_add, hx, hy]
  · rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]
@[simp]
theorem changeForm_self :
    changeForm changeForm.zero_proof = (LinearMap.id : CliffordAlgebra Q →ₗ[R] _) :=
  LinearMap.ext <| changeForm_self_apply
theorem changeForm_changeForm (x : CliffordAlgebra Q) :
    changeForm h' (changeForm h x) = changeForm (changeForm.add_proof h h') x := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [changeForm_algebraMap]
  · rw [map_add, map_add, map_add, hx, hy]
  · rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_add, LinearMap.add_apply, changeForm_contractLeft, hx,
      add_comm (_ : CliffordAlgebra Q'')]
theorem changeForm_comp_changeForm :
    (changeForm h').comp (changeForm h) = changeForm (changeForm.add_proof h h') :=
  LinearMap.ext <| changeForm_changeForm _ h'
@[simps apply]
def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
      dsimp only
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(add_neg_cancel B), changeForm_self_apply]
    right_inv := fun x => by
      dsimp only
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(neg_add_cancel B), changeForm_self_apply] }
@[simp]
theorem changeFormEquiv_symm :
    (changeFormEquiv h).symm = changeFormEquiv (changeForm.neg_proof h) :=
  LinearEquiv.ext fun _ => rfl
variable (Q)
@[simp]
def equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  changeFormEquiv changeForm.associated_neg_proof
instance [Nontrivial R] [Invertible (2 : R)] :
    Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial
end CliffordAlgebra