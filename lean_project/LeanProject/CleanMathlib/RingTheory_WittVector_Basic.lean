import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.Algebra.MvPolynomial.Invertible
import Mathlib.RingTheory.WittVector.Defs
noncomputable section
open MvPolynomial Function
variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]
variable {α : Type*} {β : Type*}
local notation "𝕎" => WittVector p
local notation "W_" => wittPolynomial p
open scoped Witt
namespace WittVector
def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)
namespace mapFun
theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) := by
  intros _ _ h
  ext p
  exact hf (congr_arg (fun x => coeff x p) h : _)
theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.choose <| hf <| x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩
macro "map_fun_tac" : tactic => `(tactic| (
  ext n
  simp only [mapFun, mk, comp_apply, zero_coeff, map_zero,
    add_coeff, sub_coeff, mul_coeff, neg_coeff, nsmul_coeff, zsmul_coeff, pow_coeff,
    peval, map_aeval, algebraMap_int_eq, coe_eval₂Hom] <;>
  try { cases n <;> simp <;> done } <;>  
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl <;>
  ext ⟨i, k⟩ <;>
    fin_cases i <;> rfl))
variable [Fact p.Prime]
variable (f : R →+* S) (x y : WittVector p R)
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by map_fun_tac
theorem one : mapFun f (1 : 𝕎 R) = 1 := by map_fun_tac
theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac
theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac
theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac
theorem neg : mapFun f (-x) = -mapFun f x := by map_fun_tac
theorem nsmul (n : ℕ) (x : WittVector p R) : mapFun f (n • x) = n • mapFun f x := by map_fun_tac
theorem zsmul (z : ℤ) (x : WittVector p R) : mapFun f (z • x) = z • mapFun f x := by map_fun_tac
theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac
theorem natCast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast := natCast
theorem intCast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, add, one, neg, zero, natCast] <;> rfl
@[deprecated (since := "2024-04-17")]
alias int_cast := intCast
end mapFun
end WittVector
namespace WittVector
private def ghostFun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)
section Tactic
open Lean Elab Tactic
elab "ghost_fun_tac" φ:term "," fn:term : tactic => do
  evalTactic (← `(tactic| (
  ext n
  have := congr_fun (congr_arg (@peval R _ _) (wittStructureInt_prop p $φ n)) $fn
  simp only [wittZero, OfNat.ofNat, Zero.zero, wittOne, One.one,
    HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, Neg.neg, HMul.hMul, Mul.mul,HPow.hPow, Pow.pow,
    wittNSMul, wittZSMul, HSMul.hSMul, SMul.smul]
  simpa (config := { unfoldPartialApp := true }) [WittVector.ghostFun, aeval_rename, aeval_bind₁,
    comp, uncurry, peval, eval] using this
  )))
end Tactic
section GhostFun
@[local simp]
theorem matrix_vecEmpty_coeff {R} (i j) :
    @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩
variable [Fact p.Prime]
variable (x y : WittVector p R)
private theorem ghostFun_zero : ghostFun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, ![]
private theorem ghostFun_one : ghostFun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, ![]
private theorem ghostFun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]
private theorem ghostFun_natCast (i : ℕ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;>
      simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add, -Pi.natCast_def]
@[deprecated (since := "2024-04-17")]
alias ghostFun_nat_cast := ghostFun_natCast
private theorem ghostFun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]
private theorem ghostFun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]
private theorem ghostFun_neg : ghostFun (-x) = -ghostFun x := by ghost_fun_tac -X 0, ![x.coeff]
private theorem ghostFun_intCast (i : ℤ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_natCast, ghostFun_neg, -Pi.natCast_def,
      -Pi.intCast_def]
@[deprecated (since := "2024-04-17")]
alias ghostFun_int_cast := ghostFun_intCast
private lemma ghostFun_nsmul (m : ℕ) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]
private lemma ghostFun_zsmul (m : ℤ) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]
private theorem ghostFun_pow (m : ℕ) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]
end GhostFun
variable (p) (R)
private def ghostEquiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R) where
  toFun := ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this
    simpa (config := { unfoldPartialApp := true }) only [aeval_bind₁, aeval_X, ghostFun,
      aeval_wittPolynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_xInTermsOfW_wittPolynomial p R n
    apply_fun aeval x at this
    simpa only [aeval_bind₁, aeval_X, ghostFun, aeval_wittPolynomial]
variable [Fact p.Prime]
@[local instance]
private def comm_ring_aux₁ : CommRing (𝕎 (MvPolynomial R ℚ)) :=
  (ghostEquiv' p (MvPolynomial R ℚ)).injective.commRing ghostFun ghostFun_zero ghostFun_one
    ghostFun_add ghostFun_mul ghostFun_neg ghostFun_sub ghostFun_nsmul ghostFun_zsmul
    ghostFun_pow ghostFun_natCast ghostFun_intCast
@[local instance]
private abbrev comm_ring_aux₂ : CommRing (𝕎 (MvPolynomial R ℤ)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).commRing _
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)
instance : CommRing (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)
variable {p R}
noncomputable def map (f : R →+* S) : 𝕎 R →+* 𝕎 S where
  toFun := mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f
theorem map_injective (f : R →+* S) (hf : Injective f) : Injective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.injective f hf
theorem map_surjective (f : R →+* S) (hf : Surjective f) : Surjective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.surjective f hf
@[simp]
theorem map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) : (map f x).coeff n = f (x.coeff n) :=
  rfl
def ghostMap : 𝕎 R →+* ℕ → R where
  toFun := ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul
def ghostComponent (n : ℕ) : 𝕎 R →+* R :=
  (Pi.evalRingHom _ n).comp ghostMap
theorem ghostComponent_apply (n : ℕ) (x : 𝕎 R) : ghostComponent n x = aeval x.coeff (W_ ℤ n) :=
  rfl
@[simp]
theorem ghostMap_apply (x : 𝕎 R) (n : ℕ) : ghostMap x n = ghostComponent n x :=
  rfl
section Invertible
variable (p R)
variable [Invertible (p : R)]
def ghostEquiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghostMap : 𝕎 R →+* ℕ → R), ghostEquiv' p R with }
@[simp]
theorem ghostEquiv_coe : (ghostEquiv p R : 𝕎 R →+* ℕ → R) = ghostMap :=
  rfl
theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R → ℕ → R) :=
  (ghostEquiv p R).bijective
end Invertible
@[simps]
noncomputable def constantCoeff : 𝕎 R →+* R where
  toFun x := x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero
instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial
end WittVector