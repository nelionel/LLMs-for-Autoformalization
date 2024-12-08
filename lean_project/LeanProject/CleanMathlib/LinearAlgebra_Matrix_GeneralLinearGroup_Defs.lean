import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Ring.Subring.Units
namespace Matrix
universe u v
open Matrix
open LinearMap
attribute [-instance] SpecialLinearGroup.instCoeFun
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [CommRing R] :
    Type _ :=
  (Matrix n n R)ˣ
@[inherit_doc] notation "GL" => GeneralLinearGroup
namespace GeneralLinearGroup
variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
section CoeFnInstance
instance instCoeFun : CoeFun (GL n R) fun _ => n → n → R where
  coe A := (A : Matrix n n R)
end CoeFnInstance
@[simps]
def det : GL n R →* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' _ _ := Units.ext <| det_mul _ _
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv
def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h
def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h
section CoeLemmas
variable (A B : GL n R)
@[simp]
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R) :=
  rfl
@[simp]
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl
theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)
@[deprecated (since := "2024-11-26")] alias toLinear := toLin
@[simp]
theorem coe_toLin : (@toLin n ‹_› ‹_› _ _ A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl
@[simp]
theorem toLin_apply (v : n → R) : (toLin A).toLinearEquiv v = Matrix.mulVecLin (↑A) v :=
  rfl
end CoeLemmas
variable {S T : Type*} [CommRing S] [CommRing T]
def map (f : R →+* S) : GL n R →* GL n S := Units.map <| (RingHom.mapMatrix f).toMonoidHom
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl
@[simp]
protected lemma map_apply (f : R →+* S) (i j : n) (g : GL n R) : map f g i j = f (g i j) := by
  rfl
@[simp]
theorem map_comp (f : T →+* R) (g : R →+* S) :
    map (g.comp f) = (map g).comp (map (n := n) f) :=
  rfl
@[simp]
theorem map_comp_apply (f : T →+* R) (g : R →+* S) (x : GL n T) :
    (map g).comp (map f) x = map g (map f x) :=
  rfl
variable (f : R →+* S)
@[simp]
protected lemma map_one : map f (1 : GL n R) = 1 := by
  ext
  simp only [_root_.map_one, Units.val_one]
protected lemma map_mul (g h : GL n R) : map f (g * h) = map f g * map f h := by
  ext
  simp only [_root_.map_mul, Units.val_mul]
protected lemma map_inv (g : GL n R) : map f g⁻¹ = (map f g)⁻¹ := by
  ext
  simp only [_root_.map_inv, coe_units_inv]
protected lemma map_det (g : GL n R) : Matrix.GeneralLinearGroup.det (map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)
lemma map_mul_map_inv (g : GL n R) : map f g * map f g⁻¹ = 1 := by
  simp only [map_inv, mul_inv_cancel]
lemma map_inv_mul_map (g : GL n R) : map f g⁻¹ * map f g = 1 := by
  simp only [map_inv, inv_mul_cancel]
@[simp]
lemma coe_map_mul_map_inv (g : GL n R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, _root_.map_one, Matrix.map_one]
@[simp]
lemma coe_map_inv_mul_map (g : GL n R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, _root_.map_one, Matrix.map_one]
end GeneralLinearGroup
namespace SpecialLinearGroup
variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
def toGL : Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n R where
  toFun A := ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
@[deprecated (since := "2024-11-26")] alias coeToGL := toGL
instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨toGL⟩
@[simp]
theorem coeToGL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (g : GL n R) = 1 :=
  Units.ext g.prop
end SpecialLinearGroup
section
variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]
section
variable (n R)
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det
@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R
end
@[simp]
theorem mem_glpos (A : GL n R) : A ∈ GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) :=
  Iff.rfl
theorem GLPos.det_ne_zero (A : GLPos n R) : ((A : GL n R) : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.prop
end
section Neg
variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]
  [Fact (Even (Fintype.card n))]
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos, GeneralLinearGroup.val_det_apply, Units.val_neg, det_neg,
        (Fact.out (p := Even <| Fintype.card n)).neg_one_pow, one_mul]
      exact g.prop⟩⟩
@[simp]
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl
@[simp]
theorem GLPos.coe_neg (g : GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) :=
  rfl
@[simp]
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    ((↑(-g) : GL n R) : Matrix n n R) i j = -((g : GL n R) : Matrix n n R) i j :=
  rfl
instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul
end Neg
namespace SpecialLinearGroup
variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [LinearOrderedCommRing R]
def toGLPos : SpecialLinearGroup n R →* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' _ _ := Subtype.ext <| Units.ext <| rfl
instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩
theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → GLPos n R) :=
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) ↦ ((A : GL n R) : Matrix n n R))
    (show Function.Injective (_ ∘ (toGLPos : SpecialLinearGroup n R → GLPos n R))
      from Subtype.coe_injective)
@[simp]
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl
@[simp]
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : GLPos n R) : GL n R) = 1 :=
  Units.ext g.prop
variable [Fact (Even (Fintype.card n))]
@[norm_cast]
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
  Subtype.ext <| Units.ext rfl
end SpecialLinearGroup
end Matrix