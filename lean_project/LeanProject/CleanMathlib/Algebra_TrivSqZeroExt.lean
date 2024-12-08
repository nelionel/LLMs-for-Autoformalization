import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.BigOperators.Pi
universe u v w
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M
local notation "tsze" => TrivSqZeroExt
open scoped RightActions
namespace TrivSqZeroExt
open MulOpposite
section Basic
variable {R : Type u} {M : Type v}
def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)
def inr [Zero R] (m : M) : tsze R M :=
  (0, m)
def fst (x : tsze R M) : R :=
  x.1
def snd (x : tsze R M) : M :=
  x.2
@[simp]
theorem fst_mk (r : R) (m : M) : fst (r, m) = r :=
  rfl
@[simp]
theorem snd_mk (r : R) (m : M) : snd (r, m) = m :=
  rfl
@[ext]
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
section
variable (M)
@[simp]
theorem fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl
@[simp]
theorem snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl
@[simp]
theorem fst_comp_inl [Zero M] : fst ∘ (inl : R → tsze R M) = id :=
  rfl
@[simp]
theorem snd_comp_inl [Zero M] : snd ∘ (inl : R → tsze R M) = 0 :=
  rfl
end
section
variable (R)
@[simp]
theorem fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl
@[simp]
theorem snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl
@[simp]
theorem fst_comp_inr [Zero R] : fst ∘ (inr : M → tsze R M) = 0 :=
  rfl
@[simp]
theorem snd_comp_inr [Zero R] : snd ∘ (inr : M → tsze R M) = id :=
  rfl
end
theorem fst_surjective [Nonempty M] : Function.Surjective (fst : tsze R M → R) :=
  Prod.fst_surjective
theorem snd_surjective [Nonempty R] : Function.Surjective (snd : tsze R M → M) :=
  Prod.snd_surjective
theorem inl_injective [Zero M] : Function.Injective (inl : R → tsze R M) :=
  Function.LeftInverse.injective <| fst_inl _
theorem inr_injective [Zero R] : Function.Injective (inr : M → tsze R M) :=
  Function.LeftInverse.injective <| snd_inr _
end Basic
section Additive
variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}
instance inhabited [Inhabited R] [Inhabited M] : Inhabited (tsze R M) :=
  instInhabitedProd
instance zero [Zero R] [Zero M] : Zero (tsze R M) :=
  Prod.instZero
instance add [Add R] [Add M] : Add (tsze R M) :=
  Prod.instAdd
instance sub [Sub R] [Sub M] : Sub (tsze R M) :=
  Prod.instSub
instance neg [Neg R] [Neg M] : Neg (tsze R M) :=
  Prod.instNeg
instance addSemigroup [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M) :=
  Prod.instAddSemigroup
instance addZeroClass [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M) :=
  Prod.instAddZeroClass
instance addMonoid [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) :=
  Prod.instAddMonoid
instance addGroup [AddGroup R] [AddGroup M] : AddGroup (tsze R M) :=
  Prod.instAddGroup
instance addCommSemigroup [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigroup (tsze R M) :=
  Prod.instAddCommSemigroup
instance addCommMonoid [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R M) :=
  Prod.instAddCommMonoid
instance addCommGroup [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M) :=
  Prod.instAddCommGroup
instance smul [SMul S R] [SMul S M] : SMul S (tsze R M) :=
  Prod.smul
instance isScalarTower [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S M] : IsScalarTower T S (tsze R M) :=
  Prod.isScalarTower
instance smulCommClass [SMul T R] [SMul T M] [SMul S R] [SMul S M]
    [SMulCommClass T S R] [SMulCommClass T S M] : SMulCommClass T S (tsze R M) :=
  Prod.smulCommClass
instance isCentralScalar [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
    [IsCentralScalar S M] : IsCentralScalar S (tsze R M) :=
  Prod.isCentralScalar
instance mulAction [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R M) :=
  Prod.mulAction
instance distribMulAction [Monoid S] [AddMonoid R] [AddMonoid M]
    [DistribMulAction S R] [DistribMulAction S M] : DistribMulAction S (tsze R M) :=
  Prod.distribMulAction
instance module [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M] :
    Module S (tsze R M) :=
  Prod.instModule
instance instNontrivial_of_left {R M : Type*} [Nontrivial R] [Nonempty M] :
    Nontrivial (TrivSqZeroExt R M) :=
  fst_surjective.nontrivial
instance instNontrivial_of_right {R M : Type*} [Nonempty R] [Nontrivial M] :
    Nontrivial (TrivSqZeroExt R M) :=
  snd_surjective.nontrivial
@[simp]
theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 :=
  rfl
@[simp]
theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 :=
  rfl
@[simp]
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl
@[simp]
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl
@[simp]
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl
@[simp]
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl
@[simp]
theorem fst_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).fst = x₁.fst - x₂.fst :=
  rfl
@[simp]
theorem snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.snd :=
  rfl
@[simp]
theorem fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst :=
  rfl
@[simp]
theorem snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd :=
  rfl
theorem fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst :=
  Prod.fst_sum
theorem snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd :=
  Prod.snd_sum
section
variable (M)
@[simp]
theorem inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0 :=
  rfl
@[simp]
theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm
@[simp]
theorem inl_neg [Neg R] [SubNegZeroMonoid M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm
@[simp]
theorem inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : tsze R M) = inl r₁ - inl r₂ :=
  ext rfl (sub_zero _).symm
@[simp]
theorem inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R) :
    (inl (s • r) : tsze R M) = s • inl r :=
  ext rfl (smul_zero s).symm
theorem inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → R) :
    (inl (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, inl (f i) :=
  map_sum (LinearMap.inl ℕ _ _) _ _
end
section
variable (R)
@[simp]
theorem inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0 :=
  rfl
@[simp]
theorem inr_add [AddZeroClass R] [AddZeroClass M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl
@[simp]
theorem inr_neg [SubNegZeroMonoid R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl
@[simp]
theorem inr_sub [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M) :
    (inr (m₁ - m₂) : tsze R M) = inr m₁ - inr m₂ :=
  ext (sub_zero _).symm rfl
@[simp]
theorem inr_smul [Zero R] [Zero S] [SMulWithZero S R] [SMul S M] (r : S) (m : M) :
    (inr (r • m) : tsze R M) = r • inr m :=
  ext (smul_zero _).symm rfl
theorem inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
    (inr (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, inr (f i) :=
  map_sum (LinearMap.inr ℕ _ _) _ _
end
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    inl x.fst + inr x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)
@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (inl_add_inr : ∀ r m, P (inl r + inr m)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
variable (R M)
@[simps apply]
def inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] tsze R M :=
  { LinearMap.inr R R M with toFun := inr }
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M →ₗ[R] M :=
  { LinearMap.snd _ _ _ with toFun := snd }
end Additive
section Mul
variable {R : Type u} {M : Type v}
instance one [One R] [Zero M] : One (tsze R M) :=
  ⟨(1, 0)⟩
instance mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩
@[simp]
theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 :=
  rfl
@[simp]
theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 :=
  rfl
@[simp]
theorem fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl
@[simp]
theorem snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst :=
  rfl
section
variable (M)
@[simp]
theorem inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1 :=
  rfl
@[simp]
theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
  ext rfl <| show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]
theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
  (inl_mul M r₁ r₂).symm
end
section
variable (R)
@[simp]
theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) :
    (inr m₁ * inr m₂ : tsze R M) = 0 :=
  ext (mul_zero _) <|
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]
end
theorem inl_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (r : R) (m : M) :
    (inl r * inr m : tsze R M) = inr (r • m) :=
  ext (mul_zero r) <|
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]
theorem inr_mul_inl [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (r : R) (m : M) :
    (inr m * inl r : tsze R M) = inr (m <• r) :=
  ext (zero_mul r) <|
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]
theorem inl_mul_eq_smul [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    (r : R) (x : tsze R M) :
    inl r * x = r •> x :=
  ext rfl (by dsimp; rw [smul_zero, add_zero])
theorem mul_inl_eq_op_smul [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    (x : tsze R M) (r : R) :
    x * inl r = x <• r :=
  ext rfl (by dsimp; rw [smul_zero, zero_add])
instance mulOneClass [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    MulOneClass (tsze R M) :=
  { TrivSqZeroExt.one, TrivSqZeroExt.mul with
    one_mul := fun x =>
      ext (one_mul x.1) <|
        show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul] }
instance addMonoidWithOne [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (tsze R M) :=
  { TrivSqZeroExt.addMonoid, TrivSqZeroExt.one with
    natCast := fun n => inl n
    natCast_zero := by simp [Nat.cast]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast] }
@[simp]
theorem fst_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).fst = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias fst_nat_cast := fst_natCast
@[simp]
theorem snd_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).snd = 0 :=
  rfl
@[deprecated (since := "2024-04-17")]
alias snd_nat_cast := snd_natCast
@[simp]
theorem inl_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (inl n : tsze R M) = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias inl_nat_cast := inl_natCast
instance addGroupWithOne [AddGroupWithOne R] [AddGroup M] : AddGroupWithOne (tsze R M) :=
  { TrivSqZeroExt.addGroup, TrivSqZeroExt.addMonoidWithOne with
    intCast := fun z => inl z
    intCast_ofNat := fun _n => ext (Int.cast_natCast _) rfl
    intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm }
@[simp]
theorem fst_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).fst = z :=
  rfl
@[deprecated (since := "2024-04-17")]
alias fst_int_cast := fst_intCast
@[simp]
theorem snd_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).snd = 0 :=
  rfl
@[deprecated (since := "2024-04-17")]
alias snd_int_cast := snd_intCast
@[simp]
theorem inl_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (inl z : tsze R M) = z :=
  rfl
@[deprecated (since := "2024-04-17")]
alias inl_int_cast := inl_intCast
instance nonAssocSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocSemiring (tsze R M) :=
  { TrivSqZeroExt.addMonoidWithOne, TrivSqZeroExt.mulOneClass, TrivSqZeroExt.addCommMonoid with
    zero_mul := fun x =>
      ext (zero_mul x.1) <|
        show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
    mul_zero := fun x =>
      ext (mul_zero x.1) <|
        show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 •> (x₂.2 + x₃.2) + x₁.2 <• (x₂.1 + x₃.1) =
            x₁.1 •> x₂.2 + x₁.2 <• x₂.1 + (x₁.1 •> x₃.2 + x₁.2 <• x₃.1)
          by simp_rw [smul_add, MulOpposite.op_add, add_smul, add_add_add_comm]
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) •> x₃.2 + (x₁.2 + x₂.2) <• x₃.1 =
            x₁.1 •> x₃.2 + x₁.2 <• x₃.1 + (x₂.1 •> x₃.2 + x₂.2 <• x₃.1)
          by simp_rw [add_smul, smul_add, add_add_add_comm] }
instance nonAssocRing [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocRing (tsze R M) :=
  { TrivSqZeroExt.addGroupWithOne, TrivSqZeroExt.nonAssocSemiring with }
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    Pow (tsze R M) ℕ :=
  ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩
@[simp]
theorem fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) : fst (x ^ n) = x.fst ^ n :=
  rfl
theorem snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) :
    snd (x ^ n) = ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum :=
  rfl
theorem snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • x.fst ^ n.pred •> x.snd := by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    refine (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd) ?_).trans ?_
    · rintro m hm
      simp_rw [List.mem_map, List.mem_range] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp hi)]
    · rw [List.length_map, List.length_range]
where
  aux : ∀ n : ℕ, x.snd <• x.fst ^ n = x.fst ^ n •> x.snd := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, op_mul, mul_smul, mul_smul, ← h, smul_comm (_ : R) (op x.fst) x.snd, ih]
theorem snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred) := by
  rw [snd_pow_of_smul_comm _ _ h, snd_pow_of_smul_comm.aux _ h]
@[simp]
theorem snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (x : tsze R M) (n : ℕ) : snd (x ^ n) = n • x.fst ^ n.pred • x.snd :=
  snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)
@[simp]
theorem inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
    (n : ℕ) : (inl r ^ n : tsze R M) = inl (r ^ n) :=
  ext rfl <| by simp [snd_pow_eq_sum, List.map_const']
instance monoid [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] : Monoid (tsze R M) :=
  { TrivSqZeroExt.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
            x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
          by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
    npow := fun n x => x ^ n
    npow_zero := fun x => ext (pow_zero x.fst) (by simp [snd_pow_eq_sum])
    npow_succ := fun n x =>
      ext (pow_succ _ _)
        (by
          simp_rw [snd_mul, snd_pow_eq_sum, Nat.pred_succ]
          cases n
          · simp [List.range_succ]
          rw [List.sum_range_succ']
          simp only [pow_zero, op_one, Nat.sub_zero, one_smul, Nat.succ_sub_succ_eq_sub, fst_pow,
            Nat.pred_succ, List.smul_sum, List.map_map, Function.comp_def]
          simp_rw [← smul_comm (_ : R) (_ : Rᵐᵒᵖ), smul_smul, pow_succ]
          rfl) }
theorem fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.map fst).prod :=
  map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M →* R) _
instance semiring [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] : Semiring (tsze R M) :=
  { TrivSqZeroExt.monoid, TrivSqZeroExt.nonAssocSemiring with }
theorem snd_list_prod [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) :
    l.prod.snd =
      (l.enum.map fun x : ℕ × tsze R M =>
          ((l.map fst).take x.1).prod •> x.snd.snd <• ((l.map fst).drop x.1.succ).prod).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.enum_cons, ← List.map_fst_add_enum_eq_enumFrom]
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul,
      List.drop, mul_smul, List.sum_cons, fst_list_prod, ih, List.smul_sum, List.map_map,
      ← smul_comm (_ : R) (_ : Rᵐᵒᵖ)]
    exact add_comm _ _
instance ring [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    Ring (tsze R M) :=
  { TrivSqZeroExt.semiring, TrivSqZeroExt.nonAssocRing with }
instance commMonoid [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] : CommMonoid (tsze R M) :=
  { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul, op_smul_eq_smul, add_comm] }
instance commSemiring [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : CommSemiring (tsze R M) :=
  { TrivSqZeroExt.commMonoid, TrivSqZeroExt.nonAssocSemiring with }
instance commRing [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    CommRing (tsze R M) :=
  { TrivSqZeroExt.nonAssocRing, TrivSqZeroExt.commSemiring with }
variable (R M)
@[simps apply]
def inlHom [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] : R →+* tsze R M where
  toFun := inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M
end Mul
section Inv
variable {R : Type u} {M : Type v}
variable [Neg M] [Inv R] [SMul Rᵐᵒᵖ M] [SMul R M]
instance instInv : Inv (tsze R M) :=
  ⟨fun b => (b.1⁻¹, -(b.1⁻¹ •> b.2 <• b.1⁻¹))⟩
@[simp] theorem fst_inv (x : tsze R M) : fst x⁻¹ = (fst x)⁻¹ :=
  rfl
@[simp] theorem snd_inv (x : tsze R M) : snd x⁻¹ = -((fst x)⁻¹ •> snd x <• (fst x)⁻¹) :=
  rfl
end Inv
section Invertible
variable {R : Type u} {M : Type v}
variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]
abbrev invertibleFstOfInvertible (x : tsze R M) [Invertible x] : Invertible x.fst where
  invOf := (⅟x).fst
  invOf_mul_self := by rw [← fst_mul, invOf_mul_self, fst_one]
  mul_invOf_self := by rw [← fst_mul, mul_invOf_self, fst_one]
theorem fst_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).fst = ⅟(x.fst) := by
  letI := invertibleFstOfInvertible x
  convert (rfl : _ = ⅟ x.fst)
theorem mul_left_eq_one (r : R) (x : tsze R M) (h : r * x.fst = 1) :
    (inl r + inr (-((r •> x.snd) <• r))) * x = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]
theorem mul_right_eq_one (x : tsze R M) (r : R) (h : x.fst * r = 1) :
    x * (inl r + inr (-(r •> (x.snd <• r)))) = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]
variable [SMulCommClass R Rᵐᵒᵖ M]
abbrev invertibleOfInvertibleFst (x : tsze R M) [Invertible x.fst] : Invertible x where
  invOf := (⅟x.fst, -(⅟x.fst •> x.snd <• ⅟x.fst))
  invOf_mul_self := by
    convert mul_left_eq_one _ _ (invOf_mul_self x.fst)
    ext <;> simp
  mul_invOf_self := by
    convert mul_right_eq_one _ _ (mul_invOf_self x.fst)
    ext <;> simp [smul_comm]
theorem snd_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] :
    (⅟x).snd = -(⅟x.fst •> x.snd <• ⅟x.fst) := by
  letI := invertibleOfInvertibleFst x
  convert congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟ x)
  convert rfl
@[simps]
def invertibleEquivInvertibleFst (x : tsze R M) : Invertible x ≃ Invertible x.fst where
  toFun _ := invertibleFstOfInvertible x
  invFun _ := invertibleOfInvertibleFst x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
theorem isUnit_iff_isUnit_fst {x : tsze R M} : IsUnit x ↔ IsUnit x.fst := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivInvertibleFst x).nonempty_congr]
@[simp]
theorem isUnit_inl_iff {r : R} : IsUnit (inl r : tsze R M) ↔ IsUnit r := by
  rw [isUnit_iff_isUnit_fst, fst_inl]
@[simp]
theorem isUnit_inr_iff {m : M} : IsUnit (inr m : tsze R M) ↔ Subsingleton R := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]
end Invertible
section DivisionSemiring
variable {R : Type u} {M : Type v}
variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]
protected theorem inv_inl (r : R) :
    (inl r)⁻¹ = (inl (r⁻¹ : R) : tsze R M) := by
  ext
  · rw [fst_inv, fst_inl, fst_inl]
  · rw [snd_inv, fst_inl, snd_inl, snd_inl, smul_zero, smul_zero, neg_zero]
@[simp]
theorem inv_inr (m : M) : (inr m)⁻¹ = (0 : tsze R M) := by
  ext
  · rw [fst_inv, fst_inr, fst_zero, inv_zero]
  · rw [snd_inv, snd_inr, fst_inr, inv_zero, op_zero, zero_smul, snd_zero, neg_zero]
@[simp]
protected theorem inv_zero : (0 : tsze R M)⁻¹ = (0 : tsze R M) := by
  rw [← inl_zero, TrivSqZeroExt.inv_inl, inv_zero]
@[simp]
protected theorem inv_one : (1 : tsze R M)⁻¹ = (1 : tsze R M) := by
  rw [← inl_one, TrivSqZeroExt.inv_inl, inv_one]
protected theorem inv_mul_cancel {x : tsze R M} (hx : fst x ≠ 0) : x⁻¹ * x = 1 := by
  convert mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx) using 2
  ext <;> simp
variable [SMulCommClass R Rᵐᵒᵖ M]
@[simp] theorem invOf_eq_inv (x : tsze R M) [Invertible x] : ⅟x = x⁻¹ := by
  letI := invertibleFstOfInvertible x
  ext <;> simp [fst_invOf, snd_invOf]
protected theorem mul_inv_cancel {x : tsze R M} (hx : fst x ≠ 0) : x * x⁻¹ = 1 := by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv, mul_invOf_self]
protected theorem mul_inv_rev (a b : tsze R M) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  ext
  · rw [fst_inv, fst_mul, fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, snd_mul, fst_mul, fst_inv]
    simp only [neg_smul, smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (fst a) 0
    · simp [ha0]
    obtain hb0 | hb := eq_or_ne (fst b) 0
    · simp [hb0]
    rw [inv_mul_cancel_right₀ ha, mul_inv_cancel_left₀ hb]
protected theorem inv_inv {x : tsze R M} (hx : fst x ≠ 0) : x⁻¹⁻¹ = x :=
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc, TrivSqZeroExt.mul_inv_cancel, mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx
@[simp]
theorem isUnit_inv_iff {x : tsze R M} : IsUnit x⁻¹ ↔ IsUnit x := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]
end DivisionSemiring
section DivisionRing
variable {R : Type u} {M : Type v}
variable [DivisionRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]
protected theorem inv_neg {x : tsze R M} : (-x)⁻¹ = -(x⁻¹) := by
  ext <;> simp [inv_neg]
end DivisionRing
section Algebra
variable (S : Type*) (R R' : Type u) (M : Type v)
variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]
variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
instance algebra' : Algebra S (tsze R M) :=
  { (TrivSqZeroExt.inlHom R M).comp (algebraMap S R) with
    smul := (· • ·)
    commutes' := fun s x =>
      ext (Algebra.commutes _ _) <|
        show algebraMap S R s •> x.snd + (0 : M) <• x.fst
            = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
          rw [smul_zero, smul_zero, add_zero, zero_add]
          rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, op_one, smul_assoc,
            one_smul, smul_assoc, one_smul]
    smul_def' := fun s x =>
      ext (Algebra.smul_def _ _) <|
        show s • x.snd = algebraMap S R s •> x.snd + (0 : M) <• x.fst by
          rw [smul_zero, add_zero, algebraMap_smul] }
instance : Algebra R' (tsze R' M) :=
  TrivSqZeroExt.algebra' _ _ _
theorem algebraMap_eq_inl : ⇑(algebraMap R' (tsze R' M)) = inl :=
  rfl
theorem algebraMap_eq_inlHom : algebraMap R' (tsze R' M) = inlHom R' M :=
  rfl
theorem algebraMap_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S R s) :=
  rfl
@[simps]
def fstHom : tsze R M →ₐ[S] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _
@[simps]
def inlAlgHom : R →ₐ[S] tsze R M where
  toFun := inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm
variable {R R' S M}
theorem algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M →ₐ[R'] A⦄
    (h : ∀ m, f (inr m) = g (inr m)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h
@[ext]
theorem algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M →ₐ[S] A⦄
    (hinl : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R M))
    (hinr : f.toLinearMap.comp (inrHom R M |>.restrictScalars S) =
      g.toLinearMap.comp (inrHom R M |>.restrictScalars S)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)
variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]
def lift (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) : tsze R M →ₐ[S] A :=
  AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, add_mul, mul_add, smul_mul_smul_comm, hg, smul_zero,
          op_smul_eq_smul]
        rw [← map_mul, LinearMap.map_add, add_comm (g _), add_assoc, hfg, hgf])
theorem lift_def (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r • x) = f r * g x)
    (hgf : ∀ r x, g (op r • x) = g x * f r) (x : tsze R M) :
    lift f g hg hfg hgf x = f x.fst + g x.snd :=
  rfl
@[simp]
theorem lift_apply_inl (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (r : R) :
    lift f g hg hfg hgf (inl r) = f r :=
  show f r + g 0 = f r by rw [map_zero, add_zero]
@[simp]
theorem lift_apply_inr (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (m : M) :
    lift f g hg hfg hgf (inr m) = g m :=
  show f 0 + g m = g m by rw [map_zero, zero_add]
@[simp]
theorem lift_comp_inlHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).comp (inlAlgHom S R M) = f :=
  AlgHom.ext <| lift_apply_inl f g hg hfg hgf
@[simp]
theorem lift_comp_inrHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).toLinearMap.comp (inrHom R M |>.restrictScalars S) = g :=
  LinearMap.ext <| lift_apply_inr f g hg hfg hgf
@[simp]
theorem lift_inlAlgHom_inrHom :
    lift (inlAlgHom _ _ _) (inrHom R M |>.restrictScalars S)
      (inr_mul_inr R) (fun _ _ => (inl_mul_inr _ _).symm) (fun _ _ => (inr_mul_inl _ _).symm) =
    AlgHom.id S (tsze R M) :=
  algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
@[simps! apply symm_apply_coe]
def liftEquiv :
    {fg : (R →ₐ[S] A) × (M →ₗ[S] A) //
      (∀ x y, fg.2 x * fg.2 y = 0) ∧
      (∀ r x, fg.2 (r •> x) = fg.1 r * fg.2 x) ∧
      (∀ r x, fg.2 (x <• r) = fg.2 x * fg.1 r)} ≃ (tsze R M →ₐ[S] A) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
        (map_mul F _ _).symm.trans <| (F.congr_arg <| inr_mul_inr _ _ _).trans (map_zero F)),
      (fun _r _x => (F.congr_arg (inl_mul_inr _ _).symm).trans (map_mul F _ _)),
      (fun _r _x => (F.congr_arg (inr_mul_inl _ _).symm).trans (map_mul F _ _))⟩
  left_inv _f := Subtype.ext <| Prod.ext (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
  right_inv _F := algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
@[simps! apply symm_apply_coe]
def liftEquivOfComm :
    { f : M →ₗ[R'] A // ∀ x y, f x * f y = 0 } ≃ (tsze R' M →ₐ[R'] A) := by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩
    left_inv := fun f => rfl
    right_inv := fun fg => Subtype.ext <|
      Prod.ext (AlgHom.toLinearMap_injective <| LinearMap.ext_ring <| by simp)
      rfl }
section map
variable {N P : Type*} [AddCommMonoid N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [AddCommMonoid P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
def map (f : M →ₗ[R'] N) : TrivSqZeroExt R' M →ₐ[R'] TrivSqZeroExt R' N :=
  liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩
@[simp]
theorem map_inl (f : M →ₗ[R'] N) (r : R') : map f (inl r) = inl r := by
  rw [map, liftEquivOfComm_apply, lift_apply_inl, Algebra.ofId_apply, algebraMap_eq_inl]
@[simp]
theorem map_inr (f : M →ₗ[R'] N) (x : M) : map f (inr x) = inr (f x) := by
  rw [map, liftEquivOfComm_apply, lift_apply_inr, LinearMap.comp_apply, inrHom_apply]
@[simp]
theorem fst_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : fst (map f x) = fst x := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]
@[simp]
theorem snd_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : snd (map f x) = f (snd x) := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]
@[simp]
theorem map_comp_inlAlgHom (f : M →ₗ[R'] N) :
    (map f).comp (inlAlgHom R' R' M) = inlAlgHom R' R' N :=
  AlgHom.ext <| map_inl _
@[simp]
theorem map_comp_inrHom (f : M →ₗ[R'] N) :
    (map f).toLinearMap ∘ₗ inrHom R' M = inrHom R' N ∘ₗ f :=
  LinearMap.ext <| map_inr _
@[simp]
theorem fstHom_comp_map (f : M →ₗ[R'] N) :
    (fstHom R' R' N).comp (map f) = fstHom R' R' M :=
  AlgHom.ext <| fst_map _
@[simp]
theorem sndHom_comp_map (f : M →ₗ[R'] N) :
    sndHom R' N ∘ₗ (map f).toLinearMap = f ∘ₗ sndHom R' M :=
  LinearMap.ext <| snd_map _
@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R'] M) = AlgHom.id R' _ := by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]
theorem map_comp_map (f : M →ₗ[R'] N) (g : N →ₗ[R'] P) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]
end map
end Algebra
end TrivSqZeroExt