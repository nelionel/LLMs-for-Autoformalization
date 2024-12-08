import Mathlib.Algebra.TrivSqZeroExt
variable {R A B : Type*}
abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1
@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps
@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber
open DualNumber
namespace DualNumber
open TrivSqZeroExt
@[simp]
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  fst_inr _ _
@[simp]
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  snd_inr _ _
@[simp]
theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
  TrivSqZeroExt.snd_mul _ _
@[simp]
theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _
@[simp]
theorem inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0 :=
  TrivSqZeroExt.inv_inr 1
@[simp]
theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (mul_zero r).symm (mul_one r).symm
theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp
theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (commute_eps_left x).symm
variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
@[ext 1100]
nonrec theorem algHom_ext' ⦃f g : A[ε] →ₐ[R] B⦄
    (hinl : f.comp (inlAlgHom _ _ _) = g.comp (inlAlgHom _ _ _))
    (hinr : f.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R =
        g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R) :
      f = g :=
  algHom_ext' hinl (by
    ext a
    show f (inr a) = g (inr a)
    simpa only [inr_eq_smul_eps] using DFunLike.congr_fun hinr a)
@[ext 1200]
nonrec theorem algHom_ext ⦃f g : R[ε] →ₐ[R] A⦄ (hε : f ε = g ε) : f = g := by
  ext
  dsimp
  simp only [one_smul, hε]
def lift :
    {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)} ≃ (A[ε] →ₐ[R] B) := by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun fe => ⟨
      (fe.val.1, MulOpposite.op fe.val.2 • fe.val.1.toLinearMap),
      fun x y => show (fe.val.1 x * fe.val.2) * (fe.val.1 y * fe.val.2) = 0 by
        rw [(fe.prop.2 _).mul_mul_mul_comm, fe.prop.1, mul_zero],
      fun r x => show fe.val.1 (r * x) * fe.val.2 = fe.val.1 r * (fe.val.1 x * fe.val.2) by
        rw [map_mul, mul_assoc],
      fun r x => show fe.val.1 (x * r) * fe.val.2 = (fe.val.1 x * fe.val.2) * fe.val.1 r by
        rw [map_mul, (fe.prop.2 _).right_comm]⟩
    invFun := fun fg => ⟨
      (fg.val.1, fg.val.2 1),
      fg.prop.1 _ _,
      fun a => show fg.val.2 1 * fg.val.1 a = fg.val.1 a * fg.val.2 1 by
        rw [← fg.prop.2.1, ← fg.prop.2.2, smul_eq_mul, op_smul_eq_mul, mul_one, one_mul]⟩
    left_inv := fun fe => Subtype.ext <| Prod.ext rfl <|
      show fe.val.1 1 * fe.val.2 = fe.val.2 by
        rw [map_one, one_mul]
    right_inv := fun fg => Subtype.ext <| Prod.ext rfl <| LinearMap.ext fun x =>
      show fg.val.1 x * fg.val.2 1 = fg.val.2 x by
        rw [← fg.prop.2.1, smul_eq_mul, mul_one] }
theorem lift_apply_apply (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A[ε]) :
    lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2 := rfl
@[simp] theorem coe_lift_symm_apply (F : A[ε] →ₐ[R] B) :
    (lift.symm F).val = (F.comp (inlAlgHom _ _ _), F ε) := rfl
#adaptation_note
set_option linter.unusedVariables false in
@[simp] theorem lift_apply_inl (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) :
    lift fe (inl a : A[ε]) = fe.val.1 a := by
  rw [lift_apply_apply, fst_inl, snd_inl, map_zero, zero_mul, add_zero]
#adaptation_note
set_option linter.unusedVariables false in
@[simp] theorem lift_smul (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (a • ad) = fe.val.1 a * lift fe ad := by
  rw [← inl_mul_eq_smul, map_mul, lift_apply_inl]
#adaptation_note
set_option linter.unusedVariables false in
@[simp] theorem lift_op_smul (fe : {fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (MulOpposite.op a • ad) = lift fe ad * fe.val.1 a := by
  rw [← mul_inl_eq_op_smul, map_mul, lift_apply_inl]
@[simp] theorem lift_apply_eps
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    lift fe (ε : A[ε]) = fe.val.2 := by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]
@[simp]
theorem lift_inlAlgHom_eps :
    lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => commute_eps_left _⟩ = AlgHom.id R A[ε] :=
  lift.apply_symm_apply <| AlgHom.id R A[ε]
instance instRepr [Repr R] : Repr (DualNumber R) where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"
end DualNumber