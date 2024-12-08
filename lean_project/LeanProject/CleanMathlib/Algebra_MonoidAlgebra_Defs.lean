import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.Submodule.Basic
assert_not_exists NonUnitalAlgHom
assert_not_exists AlgEquiv
noncomputable section
open Finset
open Finsupp hiding single mapDomain
universe u₁ u₂ u₃ u₄
variable (k : Type u₁) (G : Type u₂) (H : Type*) {R : Type*}
section
variable [Semiring k]
def MonoidAlgebra : Type max u₁ u₂ :=
  G →₀ k
instance MonoidAlgebra.inhabited : Inhabited (MonoidAlgebra k G) :=
  inferInstanceAs (Inhabited (G →₀ k))
instance MonoidAlgebra.addCommMonoid : AddCommMonoid (MonoidAlgebra k G) :=
  inferInstanceAs (AddCommMonoid (G →₀ k))
instance MonoidAlgebra.instIsCancelAdd [IsCancelAdd k] : IsCancelAdd (MonoidAlgebra k G) :=
  inferInstanceAs (IsCancelAdd (G →₀ k))
instance MonoidAlgebra.coeFun : CoeFun (MonoidAlgebra k G) fun _ => G → k :=
  inferInstanceAs (CoeFun (G →₀ k) _)
end
namespace MonoidAlgebra
variable {k G}
section
variable [Semiring k] [NonUnitalNonAssocSemiring R]
abbrev single (a : G) (b : k) : MonoidAlgebra k G := Finsupp.single a b
theorem single_zero (a : G) : (single a 0 : MonoidAlgebra k G) = 0 := Finsupp.single_zero a
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  Finsupp.single_add a b₁ b₂
@[simp]
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G → k → N}
    (h_zero : h a 0 = 0) :
    (single a b).sum h = h a b := Finsupp.sum_single_index h_zero
@[simp]
theorem sum_single (f : MonoidAlgebra k G) : f.sum single = f :=
  Finsupp.sum_single f
theorem single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    single a b a' = if a = a' then b else 0 :=
  Finsupp.single_apply
@[simp]
theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := Finsupp.single_eq_zero
abbrev mapDomain {G' : Type*} (f : G → G') (v : MonoidAlgebra k G) : MonoidAlgebra k G' :=
  Finsupp.mapDomain f v
theorem mapDomain_sum {k' G' : Type*} [Semiring k'] {f : G → G'} {s : MonoidAlgebra k' G}
    {v : G → k' → MonoidAlgebra k G} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  Finsupp.mapDomain_sum
def liftNC (f : k →+ R) (g : G → R) : MonoidAlgebra k G →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g x)).comp f
@[simp]
theorem liftNC_single (f : k →+ R) (g : G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g a :=
  liftAddHom_apply_single _ _ _
end
section Mul
variable [Semiring k] [Mul G]
@[irreducible] def mul' (f g : MonoidAlgebra k G) : MonoidAlgebra k G :=
  f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂)
instance instMul : Mul (MonoidAlgebra k G) := ⟨MonoidAlgebra.mul'⟩
theorem mul_def {f g : MonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂) := by
  with_unfolding_all rfl
instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (MonoidAlgebra k G) :=
  { Finsupp.instAddCommMonoid with
    left_distrib := fun f g h => by
      haveI := Classical.decEq G
      simp only [mul_def]
      refine Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_add_index ?_ ?_)) ?_ <;>
        simp only [mul_add, mul_zero, single_zero, single_add, forall_true_iff, sum_add]
    right_distrib := fun f g h => by
      haveI := Classical.decEq G
      simp only [mul_def]
      refine Eq.trans (sum_add_index ?_ ?_) ?_ <;>
        simp only [add_mul, zero_mul, single_zero, single_add, forall_true_iff, sum_zero, sum_add]
    zero_mul := fun f => by
      simp only [mul_def]
      exact sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero }
variable [Semiring R]
theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) (a b : MonoidAlgebra k G)
    (h_comm : ∀ {x y}, y ∈ a.support → Commute (f (b x)) (g y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_finsupp_sum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]
end Mul
section Semigroup
variable [Semiring k] [Semigroup G] [Semiring R]
instance nonUnitalSemiring : NonUnitalSemiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalNonAssocSemiring with
    mul_assoc := fun f g h => by
      simp only [mul_def]
      rw [sum_sum_index] <;> congr; on_goal 1 => ext a₁ b₁
      rw [sum_sum_index, sum_sum_index] <;> congr; on_goal 1 => ext a₂ b₂
      rw [sum_sum_index, sum_single_index] <;> congr; on_goal 1 => ext a₃ b₃
      on_goal 1 => rw [sum_single_index, mul_assoc, mul_assoc]
      all_goals simp only [single_zero, single_add, forall_true_iff, add_mul,
        mul_add, zero_mul, mul_zero, sum_zero, sum_add] }
end Semigroup
section One
variable [NonAssocSemiring R] [Semiring k] [One G]
instance one : One (MonoidAlgebra k G) :=
  ⟨single 1 1⟩
theorem one_def : (1 : MonoidAlgebra k G) = single 1 1 :=
  rfl
@[simp]
theorem liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) :
    liftNC (f : k →+ R) g 1 = 1 := by simp [one_def]
end One
section MulOneClass
variable [Semiring k] [MulOneClass G]
instance nonAssocSemiring : NonAssocSemiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalNonAssocSemiring with
    natCast := fun n => single 1 n
    natCast_zero := by simp
    natCast_succ := fun _ => by simp; rfl
    one_mul := fun f => by
      simp only [mul_def, one_def, sum_single_index, zero_mul, single_zero, sum_zero, zero_add,
        one_mul, sum_single]
    mul_one := fun f => by
      simp only [mul_def, one_def, sum_single_index, mul_zero, single_zero, sum_zero, add_zero,
        mul_one, sum_single] }
theorem natCast_def (n : ℕ) : (n : MonoidAlgebra k G) = single (1 : G) (n : k) :=
  rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast_def := natCast_def
end MulOneClass
section Semiring
variable [Semiring k] [Monoid G]
instance semiring : Semiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalSemiring,
    MonoidAlgebra.nonAssocSemiring with }
variable [Semiring R]
def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra k G →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }
end Semiring
instance nonUnitalCommSemiring [CommSemiring k] [CommSemigroup G] :
    NonUnitalCommSemiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalSemiring with
    mul_comm := fun f g => by
      simp only [mul_def, Finsupp.sum, mul_comm]
      rw [Finset.sum_comm]
      simp only [mul_comm] }
instance nontrivial [Semiring k] [Nontrivial k] [Nonempty G] : Nontrivial (MonoidAlgebra k G) :=
  Finsupp.instNontrivial
section DerivedInstances
instance commSemiring [CommSemiring k] [CommMonoid G] : CommSemiring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalCommSemiring, MonoidAlgebra.semiring with }
instance unique [Semiring k] [Subsingleton k] : Unique (MonoidAlgebra k G) :=
  Finsupp.uniqueOfRight
instance addCommGroup [Ring k] : AddCommGroup (MonoidAlgebra k G) :=
  Finsupp.instAddCommGroup
instance nonUnitalNonAssocRing [Ring k] [Mul G] : NonUnitalNonAssocRing (MonoidAlgebra k G) :=
  { MonoidAlgebra.addCommGroup, MonoidAlgebra.nonUnitalNonAssocSemiring with }
instance nonUnitalRing [Ring k] [Semigroup G] : NonUnitalRing (MonoidAlgebra k G) :=
  { MonoidAlgebra.addCommGroup, MonoidAlgebra.nonUnitalSemiring with }
instance nonAssocRing [Ring k] [MulOneClass G] : NonAssocRing (MonoidAlgebra k G) :=
  { MonoidAlgebra.addCommGroup,
    MonoidAlgebra.nonAssocSemiring with
    intCast := fun z => single 1 (z : k)
    intCast_ofNat := fun n => by simp; rfl
    intCast_negSucc := fun n => by simp; rfl }
theorem intCast_def [Ring k] [MulOneClass G] (z : ℤ) :
    (z : MonoidAlgebra k G) = single (1 : G) (z : k) :=
  rfl
@[deprecated (since := "2024-04-17")]
alias int_cast_def := intCast_def
instance ring [Ring k] [Monoid G] : Ring (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonAssocRing, MonoidAlgebra.semiring with }
instance nonUnitalCommRing [CommRing k] [CommSemigroup G] :
    NonUnitalCommRing (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalCommSemiring, MonoidAlgebra.nonUnitalRing with }
instance commRing [CommRing k] [CommMonoid G] : CommRing (MonoidAlgebra k G) :=
  { MonoidAlgebra.nonUnitalCommRing, MonoidAlgebra.ring with }
variable {S : Type*}
instance smulZeroClass [Semiring k] [SMulZeroClass R k] : SMulZeroClass R (MonoidAlgebra k G) :=
  Finsupp.smulZeroClass
instance noZeroSMulDivisors [Zero R] [Semiring k] [SMulZeroClass R k] [NoZeroSMulDivisors R k] :
    NoZeroSMulDivisors R (MonoidAlgebra k G) :=
  Finsupp.noZeroSMulDivisors
instance distribSMul [Semiring k] [DistribSMul R k] : DistribSMul R (MonoidAlgebra k G) :=
  Finsupp.distribSMul _ _
instance distribMulAction [Monoid R] [Semiring k] [DistribMulAction R k] :
    DistribMulAction R (MonoidAlgebra k G) :=
  Finsupp.distribMulAction G k
instance module [Semiring R] [Semiring k] [Module R k] : Module R (MonoidAlgebra k G) :=
  Finsupp.module G k
instance faithfulSMul [Semiring k] [SMulZeroClass R k] [FaithfulSMul R k] [Nonempty G] :
    FaithfulSMul R (MonoidAlgebra k G) :=
  Finsupp.faithfulSMul
instance isScalarTower [Semiring k] [SMulZeroClass R k] [SMulZeroClass S k] [SMul R S]
    [IsScalarTower R S k] : IsScalarTower R S (MonoidAlgebra k G) :=
  Finsupp.isScalarTower G k
instance smulCommClass [Semiring k] [SMulZeroClass R k] [SMulZeroClass S k] [SMulCommClass R S k] :
    SMulCommClass R S (MonoidAlgebra k G) :=
  Finsupp.smulCommClass G k
instance isCentralScalar [Semiring k] [SMulZeroClass R k] [SMulZeroClass Rᵐᵒᵖ k]
    [IsCentralScalar R k] : IsCentralScalar R (MonoidAlgebra k G) :=
  Finsupp.isCentralScalar G k
def comapDistribMulActionSelf [Group G] [Semiring k] : DistribMulAction G (MonoidAlgebra k G) :=
  Finsupp.comapDistribMulAction
end DerivedInstances
section ExtLemmas
@[ext]
theorem ext [Semiring k] ⦃f g : MonoidAlgebra k G⦄ (H : ∀ (x : G), f x = g x) :
    f = g :=
  Finsupp.ext H
abbrev singleAddHom [Semiring k] (a : G) : k →+ MonoidAlgebra k G := Finsupp.singleAddHom a
@[simp] lemma singleAddHom_apply [Semiring k] (a : G) (b : k) :
  singleAddHom a b = single a b := rfl
@[ext high]
theorem addHom_ext' {N : Type*} [Semiring k] [AddZeroClass N]
    ⦃f g : MonoidAlgebra k G →+ N⦄
    (H : ∀ (x : G), AddMonoidHom.comp f (singleAddHom x) = AddMonoidHom.comp g (singleAddHom x)) :
    f = g :=
  Finsupp.addHom_ext' H
@[ext]
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [Semiring k] [AddMonoid N]
    [DistribMulAction R N] [DistribMulAction R k]
    {f g : MonoidAlgebra k G →+[R] N}
    (h : ∀ a : G,
      f.comp (DistribMulActionHom.single (M := k) a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  Finsupp.distribMulActionHom_ext' h
abbrev lsingle [Semiring R] [Semiring k] [Module R k] (a : G) :
    k →ₗ[R] MonoidAlgebra k G := Finsupp.lsingle a
@[simp] lemma lsingle_apply [Semiring R] [Semiring k] [Module R k] (a : G) (b : k) :
  lsingle (R := R) a b = single a b := rfl
@[ext high]
lemma lhom_ext' {N : Type*} [Semiring R] [Semiring k] [AddCommMonoid N] [Module R N] [Module R k]
    ⦃f g : MonoidAlgebra k G →ₗ[R] N⦄
    (H : ∀ (x : G), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) :
    f = g :=
  Finsupp.lhom_ext' H
end ExtLemmas
section MiscTheorems
variable [Semiring k]
theorem mul_apply [DecidableEq G] [Mul G] (f g : MonoidAlgebra k G) (x : G) :
    (f * g) x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => if a₁ * a₂ = x then b₁ * b₂ else 0 := by
  rw [mul_def, Finsupp.sum_apply]; congr; ext
  rw [Finsupp.sum_apply]; congr; ext
  apply single_apply
theorem mul_apply_antidiagonal [Mul G] (f g : MonoidAlgebra k G) (x : G) (s : Finset (G × G))
    (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = x) : (f * g) x = ∑ p ∈ s, f p.1 * g p.2 := by
  classical exact
      let F : G × G → k := fun p => if p.1 * p.2 = x then f p.1 * g p.2 else 0
      calc
        (f * g) x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := mul_apply f g x
        _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
        _ = ∑ p ∈ f.support ×ˢ g.support with p.1 * p.2 = x, f p.1 * g p.2 :=
          (Finset.sum_filter _ _).symm
        _ = ∑ p ∈ s with p.1 ∈ f.support ∧ p.2 ∈ g.support, f p.1 * g p.2 := by
          congr! 1; ext; simp only [mem_filter, mem_product, hs, and_comm]
        _ = ∑ p ∈ s, f p.1 * g p.2 :=
          sum_subset (filter_subset _ _) fun p hps hp => by
            simp only [mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
            by_cases h1 : f p.1 = 0
            · rw [h1, zero_mul]
            · rw [hp hps h1, mul_zero]
@[simp]
theorem single_mul_single [Mul G] {a₁ a₂ : G} {b₁ b₂ : k} :
    single a₁ b₁ * single a₂ b₂ = single (a₁ * a₂) (b₁ * b₂) := by
  rw [mul_def]
  exact (sum_single_index (by simp only [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by rw [mul_zero, single_zero]))
theorem single_commute_single [Mul G] {a₁ a₂ : G} {b₁ b₂ : k}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (single a₁ b₁) (single a₂ b₂) :=
  single_mul_single.trans <| congr_arg₂ single ha hb |>.trans single_mul_single.symm
theorem single_commute [Mul G] {a : G} {b : k} (ha : ∀ a', Commute a a') (hb : ∀ b', Commute b b') :
    ∀ f : MonoidAlgebra k G, Commute (single a b) f :=
  suffices AddMonoidHom.mulLeft (single a b) = AddMonoidHom.mulRight (single a b) from
    DFunLike.congr_fun this
  addHom_ext' fun a' => AddMonoidHom.ext fun b' => single_commute_single (ha a') (hb b')
@[simp]
theorem single_pow [Monoid G] {a : G} {b : k} : ∀ n : ℕ, single a b ^ n = single (a ^ n) (b ^ n)
  | 0 => by
    simp only [pow_zero]
    rfl
  | n + 1 => by simp only [pow_succ, single_pow n, single_mul_single]
section
@[simp]
theorem mapDomain_one {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [One α] [One α₂]
    {F : Type*} [FunLike F α α₂] [OneHomClass F α α₂] (f : F) :
    (mapDomain f (1 : MonoidAlgebra β α) : MonoidAlgebra β α₂) = (1 : MonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_one]
theorem mapDomain_mul {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Mul α] [Mul α₂]
    {F : Type*} [FunLike F α α₂] [MulHomClass F α α₂] (f : F) (x y : MonoidAlgebra β α) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp_rw [mul_def, mapDomain_sum, mapDomain_single, map_mul]
  rw [Finsupp.sum_mapDomain_index]
  · congr
    ext a b
    rw [Finsupp.sum_mapDomain_index]
    · simp
    · simp [mul_add]
  · simp
  · simp [add_mul]
variable (k G)
@[simps]
def ofMagma [Mul G] : G →ₙ* MonoidAlgebra k G where
  toFun a := single a 1
  map_mul' a b := by simp only [mul_def, mul_one, sum_single_index, single_eq_zero, mul_zero]
@[simps]
def of [MulOneClass G] : G →* MonoidAlgebra k G :=
  { ofMagma k G with
    toFun := fun a => single a 1
    map_one' := rfl }
end
@[simp]
theorem smul_single' (c : k) (a : G) (b : k) : c • single a b = single a (c * b) :=
  Finsupp.smul_single' c a b
theorem smul_of [MulOneClass G] (g : G) (r : k) : r • of k G g = single g r := by
  simp
theorem of_injective [MulOneClass G] [Nontrivial k] :
    Function.Injective (of k G) := fun a b h => by
  simpa using (single_eq_single_iff _ _ _ _).mp h
theorem of_commute [MulOneClass G] {a : G} (h : ∀ a', Commute a a') (f : MonoidAlgebra k G) :
    Commute (of k G a) f :=
  single_commute h Commute.one_left f
@[simps]
def singleHom [MulOneClass G] : k × G →* MonoidAlgebra k G where
  toFun a := single a.2 a.1
  map_one' := rfl
  map_mul' _a _b := single_mul_single.symm
theorem mul_single_apply_aux [Mul G] (f : MonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, a * x = z ↔ a = y) : (f * single x r) z = f y * r := by
  classical exact
      have A :
        ∀ a₁ b₁,
          ((single x r).sum fun a₂ b₂ => ite (a₁ * a₂ = z) (b₁ * b₂) 0) =
            ite (a₁ * x = z) (b₁ * r) 0 :=
        fun a₁ b₁ => sum_single_index <| by simp
      calc
        (HMul.hMul (β := MonoidAlgebra k G) f (single x r)) z =
            sum f fun a b => if a = y then b * r else 0 := by simp only [mul_apply, A, H]
        _ = if y ∈ f.support then f y * r else 0 := f.support.sum_ite_eq' _ _
        _ = f y * r := by split_ifs with h <;> simp at h <;> simp [h]
theorem mul_single_one_apply [MulOneClass G] (f : MonoidAlgebra k G) (r : k) (x : G) :
    (HMul.hMul (β := MonoidAlgebra k G) f (single 1 r)) x = f x * r :=
  f.mul_single_apply_aux fun a => by rw [mul_one]
theorem mul_single_apply_of_not_exists_mul [Mul G] (r : k) {g g' : G} (x : MonoidAlgebra k G)
    (h : ¬∃ d, g' = d * g) : (x * single g r) g' = 0 := by
  classical
    rw [mul_apply, Finsupp.sum_comm, Finsupp.sum_single_index]
    swap
    · simp_rw [Finsupp.sum, mul_zero, ite_self, Finset.sum_const_zero]
    · apply Finset.sum_eq_zero
      simp_rw [ite_eq_right_iff]
      rintro g'' _hg'' rfl
      exfalso
      exact h ⟨_, rfl⟩
theorem single_mul_apply_aux [Mul G] (f : MonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, x * a = y ↔ a = z) : (single x r * f) y = r * f z := by
  classical exact
      have : (f.sum fun a b => ite (x * a = y) (0 * b) 0) = 0 := by simp
      calc
        (HMul.hMul (α := MonoidAlgebra k G) (single x r) f) y =
            sum f fun a b => ite (x * a = y) (r * b) 0 :=
          (mul_apply _ _ _).trans <| sum_single_index this
        _ = f.sum fun a b => ite (a = z) (r * b) 0 := by simp only [H]
        _ = if z ∈ f.support then r * f z else 0 := f.support.sum_ite_eq' _ _
        _ = _ := by split_ifs with h <;> simp at h <;> simp [h]
theorem single_one_mul_apply [MulOneClass G] (f : MonoidAlgebra k G) (r : k) (x : G) :
    (single (1 : G) r * f) x = r * f x :=
  f.single_mul_apply_aux fun a => by rw [one_mul]
theorem single_mul_apply_of_not_exists_mul [Mul G] (r : k) {g g' : G} (x : MonoidAlgebra k G)
    (h : ¬∃ d, g' = g * d) : (single g r * x) g' = 0 := by
  classical
    rw [mul_apply, Finsupp.sum_single_index]
    swap
    · simp_rw [Finsupp.sum, zero_mul, ite_self, Finset.sum_const_zero]
    · apply Finset.sum_eq_zero
      simp_rw [ite_eq_right_iff]
      rintro g'' _hg'' rfl
      exfalso
      exact h ⟨_, rfl⟩
theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k →+* R) (g : G →* R) (c : k)
    (φ : MonoidAlgebra k G) : liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom k (MonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  unfold MonoidAlgebra
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, singleAddHom_apply, smulAddHom_apply,
    smul_single, smul_eq_mul, AddMonoidHom.coe_mulLeft, Finsupp.singleAddHom_apply]
  erw [liftNC_single, liftNC_single]; rw [AddMonoidHom.coe_coe, map_mul, mul_assoc]
end MiscTheorems
section NonUnitalNonAssocAlgebra
variable (k) [Semiring k] [DistribSMul R k] [Mul G]
instance isScalarTower_self [IsScalarTower R k k] :
    IsScalarTower R (MonoidAlgebra k G) (MonoidAlgebra k G) where
  smul_assoc t a b := by
    ext
    classical
    simp only [smul_eq_mul, mul_apply]
    rw [coe_smul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [mul_apply, Finsupp.smul_sum, smul_ite, smul_mul_assoc,
        zero_mul, ite_self, imp_true_iff, sum_zero, Pi.smul_apply, smul_zero]
instance smulCommClass_self [SMulCommClass R k k] :
    SMulCommClass R (MonoidAlgebra k G) (MonoidAlgebra k G) where
  smul_comm t a b := by
    ext
    classical
    simp only [smul_eq_mul, mul_apply]
    rw [coe_smul]
    refine Eq.symm (Eq.trans (congr_arg (sum a)
      (funext₂ fun a₁ b₁ => sum_smul_index' (g := b) (b := t) ?_)) ?_) <;>
    simp only [mul_apply, Finsupp.sum, Finset.smul_sum, smul_ite, mul_smul_comm,
      imp_true_iff, ite_eq_right_iff, Pi.smul_apply, mul_zero, smul_zero]
instance smulCommClass_symm_self [SMulCommClass k R k] :
    SMulCommClass (MonoidAlgebra k G) R (MonoidAlgebra k G) :=
  ⟨fun t a b => by
    haveI := SMulCommClass.symm k R k
    rw [← smul_comm]⟩
end NonUnitalNonAssocAlgebra
theorem single_one_comm [CommSemiring k] [MulOneClass G] (r : k) (f : MonoidAlgebra k G) :
    single (1 : G) r * f = f * single (1 : G) r :=
  single_commute Commute.one_left (Commute.all _) f
@[simps]
def singleOneRingHom [Semiring k] [MulOneClass G] : k →+* MonoidAlgebra k G :=
  { Finsupp.singleAddHom 1 with
    map_one' := rfl
    map_mul' := fun x y => by simp }
@[simps]
def mapDomainRingHom (k : Type*) {H F : Type*} [Semiring k] [Monoid G] [Monoid H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F) : MonoidAlgebra k G →+* MonoidAlgebra k H :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }
theorem ringHom_ext {R} [Semiring k] [MulOneClass G] [Semiring R] {f g : MonoidAlgebra k G →+* R}
    (h₁ : ∀ b, f (single 1 b) = g (single 1 b)) (h_of : ∀ a, f (single a 1) = g (single a 1)) :
    f = g :=
  RingHom.coe_addMonoidHom_injective <|
    addHom_ext fun a b => by
      rw [← single, ← one_mul a, ← mul_one b, ← single_mul_single]
      erw [AddMonoidHom.coe_coe f, AddMonoidHom.coe_coe g]; rw [f.map_mul, g.map_mul, h₁, h_of]
@[ext high]
theorem ringHom_ext' {R} [Semiring k] [MulOneClass G] [Semiring R] {f g : MonoidAlgebra k G →+* R}
    (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom)
    (h_of :
      (f : MonoidAlgebra k G →* R).comp (of k G) = (g : MonoidAlgebra k G →* R).comp (of k G)) :
    f = g :=
  ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)
theorem induction_on [Semiring k] [Monoid G] {p : MonoidAlgebra k G → Prop} (f : MonoidAlgebra k G)
    (hM : ∀ g, p (of k G g)) (hadd : ∀ f g : MonoidAlgebra k G, p f → p g → p (f + g))
    (hsmul : ∀ (r : k) (f), p f → p (r • f)) : p f := by
  refine Finsupp.induction_linear f ?_ (fun f g hf hg => hadd f g hf hg) fun g r => ?_
  · simpa using hsmul 0 (of k G 1) (hM 1)
  · convert hsmul r (of k G g) (hM g)
    simp
section
universe ui
variable {ι : Type ui}
theorem prod_single [CommSemiring k] [CommMonoid G] {s : Finset ι} {a : ι → G} {b : ι → k} :
    (∏ i ∈ s, single (a i) (b i)) = single (∏ i ∈ s, a i) (∏ i ∈ s, b i) :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons has, ih, single_mul_single, prod_cons has, prod_cons has]
end
section
variable [Semiring k] [Group G]
@[simp]
theorem mul_single_apply (f : MonoidAlgebra k G) (r : k) (x y : G) :
    (f * single x r) y = f (y * x⁻¹) * r :=
  f.mul_single_apply_aux fun _a => eq_mul_inv_iff_mul_eq.symm
@[simp]
theorem single_mul_apply (r : k) (x : G) (f : MonoidAlgebra k G) (y : G) :
    (single x r * f) y = r * f (x⁻¹ * y) :=
  f.single_mul_apply_aux fun _z => eq_inv_mul_iff_mul_eq.symm
theorem mul_apply_left (f g : MonoidAlgebra k G) (x : G) :
    (f * g) x = f.sum fun a b => b * g (a⁻¹ * x) :=
  calc
    (f * g) x = sum f fun a b => (single a b * g) x := by
      rw [← Finsupp.sum_apply, ← Finsupp.sum_mul g f, f.sum_single]
    _ = _ := by simp only [single_mul_apply, Finsupp.sum]
theorem mul_apply_right (f g : MonoidAlgebra k G) (x : G) :
    (f * g) x = g.sum fun a b => f (x * a⁻¹) * b :=
  calc
    (f * g) x = sum g fun a b => (f * single a b) x := by
      rw [← Finsupp.sum_apply, ← Finsupp.mul_sum f g, g.sum_single]
    _ = _ := by simp only [mul_single_apply, Finsupp.sum]
end
section Opposite
open Finsupp MulOpposite
variable [Semiring k]
@[simps! (config := { simpRhs := true }) apply symm_apply]
protected noncomputable def opRingEquiv [Monoid G] :
    (MonoidAlgebra k G)ᵐᵒᵖ ≃+* MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ :=
  { opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv with
    map_mul' := by
      rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
      rw [← AddEquiv.coe_toAddMonoidHom]
      refine Iff.mpr (AddMonoidHom.map_mul_iff (R := (MonoidAlgebra k G)ᵐᵒᵖ)
        (S := MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ) _) ?_
      ext
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, opAddEquiv_apply,
        Function.comp_apply, singleAddHom_apply, AddMonoidHom.compr₂_apply, AddMonoidHom.coe_mul,
        AddMonoidHom.coe_mulLeft, AddMonoidHom.compl₂_apply]
      erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
        AddEquiv.trans_apply, AddEquiv.trans_apply, MulOpposite.opAddEquiv_symm_apply]
      rw [MulOpposite.unop_mul (α := MonoidAlgebra k G), unop_op, unop_op, single_mul_single]
      simp }
theorem opRingEquiv_single [Monoid G] (r : k) (x : G) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp
theorem opRingEquiv_symm_single [Monoid G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp
end Opposite
section Submodule
variable [CommSemiring k] [Monoid G]
variable {V : Type*} [AddCommMonoid V]
variable [Module k V] [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V]
def submoduleOfSMulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (MonoidAlgebra k G) V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← Finsupp.sum_single f, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv
end Submodule
end MonoidAlgebra
section
variable [Semiring k]
def AddMonoidAlgebra :=
  G →₀ k
@[inherit_doc]
scoped[AddMonoidAlgebra] notation:9000 R:max "[" A "]" => AddMonoidAlgebra R A
namespace AddMonoidAlgebra
instance inhabited : Inhabited k[G] :=
  inferInstanceAs (Inhabited (G →₀ k))
instance addCommMonoid : AddCommMonoid k[G] :=
  inferInstanceAs (AddCommMonoid (G →₀ k))
instance instIsCancelAdd [IsCancelAdd k] : IsCancelAdd (AddMonoidAlgebra k G) :=
  inferInstanceAs (IsCancelAdd (G →₀ k))
instance coeFun : CoeFun k[G] fun _ => G → k :=
  inferInstanceAs (CoeFun (G →₀ k) _)
end AddMonoidAlgebra
end
namespace AddMonoidAlgebra
variable {k G}
section
variable [Semiring k] [NonUnitalNonAssocSemiring R]
abbrev single (a : G) (b : k) : k[G] := Finsupp.single a b
theorem single_zero (a : G) : (single a 0 : k[G]) = 0 := Finsupp.single_zero a
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  Finsupp.single_add a b₁ b₂
@[simp]
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G → k → N}
    (h_zero : h a 0 = 0) :
    (single a b).sum h = h a b := Finsupp.sum_single_index h_zero
@[simp]
theorem sum_single (f : k[G]) : f.sum single = f :=
  Finsupp.sum_single f
theorem single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    single a b a' = if a = a' then b else 0 :=
  Finsupp.single_apply
@[simp]
theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := Finsupp.single_eq_zero
abbrev mapDomain {G' : Type*} (f : G → G') (v : k[G]) : k[G'] :=
  Finsupp.mapDomain f v
theorem mapDomain_sum {k' G' : Type*} [Semiring k'] {f : G → G'} {s : AddMonoidAlgebra k' G}
    {v : G → k' → k[G]} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  Finsupp.mapDomain_sum
theorem mapDomain_single {G' : Type*} {f : G → G'} {a : G} {b : k} :
    mapDomain f (single a b) = single (f a) b :=
  Finsupp.mapDomain_single
def liftNC (f : k →+ R) (g : Multiplicative G → R) : k[G] →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g <| Multiplicative.ofAdd x)).comp f
@[simp]
theorem liftNC_single (f : k →+ R) (g : Multiplicative G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g (Multiplicative.ofAdd a) :=
  liftAddHom_apply_single _ _ _
end
section Mul
variable [Semiring k] [Add G]
instance hasMul : Mul k[G] :=
  ⟨fun f g => MonoidAlgebra.mul' (G := Multiplicative G) f g⟩
theorem mul_def {f g : k[G]} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ + a₂) (b₁ * b₂) :=
  MonoidAlgebra.mul_def (G := Multiplicative G)
instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring k[G] :=
  { Finsupp.instAddCommMonoid with
    left_distrib := fun f g h => by
      haveI := Classical.decEq G
      simp only [mul_def]
      refine Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_add_index ?_ ?_)) ?_ <;>
        simp only [mul_add, mul_zero, single_zero, single_add, forall_true_iff, sum_add]
    right_distrib := fun f g h => by
      haveI := Classical.decEq G
      simp only [mul_def]
      refine Eq.trans (sum_add_index ?_ ?_) ?_ <;>
        simp only [add_mul, zero_mul, single_zero, single_add, forall_true_iff, sum_zero, sum_add]
    zero_mul := fun f => by
      simp only [mul_def]
      exact sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero
    nsmul := fun n f => n • f
    nsmul_zero := by
      intros
      refine Finsupp.ext fun _ => ?_
      simp [-nsmul_eq_mul, add_smul]
    nsmul_succ := by
      intros
      refine Finsupp.ext fun _ => ?_
      simp [-nsmul_eq_mul, add_smul] }
variable [Semiring R]
theorem liftNC_mul {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [MulHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.support → Commute (f (b x)) (g <| Multiplicative.ofAdd y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b :=
  (MonoidAlgebra.liftNC_mul f g _ _ @h_comm : _)
end Mul
section One
variable [Semiring k] [Zero G] [NonAssocSemiring R]
instance one : One k[G] :=
  ⟨single 0 1⟩
theorem one_def : (1 : k[G]) = single 0 1 :=
  rfl
@[simp]
theorem liftNC_one {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [OneHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) : liftNC (f : k →+ R) g 1 = 1 :=
  (MonoidAlgebra.liftNC_one f g : _)
end One
section Semigroup
variable [Semiring k] [AddSemigroup G]
instance nonUnitalSemiring : NonUnitalSemiring k[G] :=
  { AddMonoidAlgebra.nonUnitalNonAssocSemiring with
    mul_assoc := fun f g h => by
      simp only [mul_def]
      rw [sum_sum_index] <;> congr; on_goal 1 => ext a₁ b₁
      rw [sum_sum_index, sum_sum_index] <;> congr; on_goal 1 => ext a₂ b₂
      rw [sum_sum_index, sum_single_index] <;> congr; on_goal 1 => ext a₃ b₃
      on_goal 1 => rw [sum_single_index, mul_assoc, add_assoc]
      all_goals simp only [single_zero, single_add, forall_true_iff, add_mul,
        mul_add, zero_mul, mul_zero, sum_zero, sum_add] }
end Semigroup
section MulOneClass
variable [Semiring k] [AddZeroClass G]
instance nonAssocSemiring : NonAssocSemiring k[G] :=
  { AddMonoidAlgebra.nonUnitalNonAssocSemiring with
    natCast := fun n => single 0 n
    natCast_zero := by simp
    natCast_succ := fun _ => by simp; rfl
    one_mul := fun f => by
      simp only [mul_def, one_def, sum_single_index, zero_mul, single_zero, sum_zero, zero_add,
        one_mul, sum_single]
    mul_one := fun f => by
      simp only [mul_def, one_def, sum_single_index, mul_zero, single_zero, sum_zero, add_zero,
        mul_one, sum_single] }
theorem natCast_def (n : ℕ) : (n : k[G]) = single (0 : G) (n : k) :=
  rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast_def := natCast_def
end MulOneClass
section Semiring
instance smulZeroClass [Semiring k] [SMulZeroClass R k] : SMulZeroClass R k[G] :=
  Finsupp.smulZeroClass
instance noZeroSMulDivisors [Zero R] [Semiring k] [SMulZeroClass R k] [NoZeroSMulDivisors R k] :
    NoZeroSMulDivisors R k[G] :=
  Finsupp.noZeroSMulDivisors
variable [Semiring k] [AddMonoid G]
instance semiring : Semiring k[G] :=
  { AddMonoidAlgebra.nonUnitalSemiring,
    AddMonoidAlgebra.nonAssocSemiring with }
variable [Semiring R]
def liftNCRingHom (f : k →+* R) (g : Multiplicative G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    k[G] →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }
end Semiring
instance nonUnitalCommSemiring [CommSemiring k] [AddCommSemigroup G] :
    NonUnitalCommSemiring k[G] :=
  { AddMonoidAlgebra.nonUnitalSemiring with
    mul_comm := @mul_comm (MonoidAlgebra k <| Multiplicative G) _ }
instance nontrivial [Semiring k] [Nontrivial k] [Nonempty G] : Nontrivial k[G] :=
  Finsupp.instNontrivial
section DerivedInstances
instance commSemiring [CommSemiring k] [AddCommMonoid G] : CommSemiring k[G] :=
  { AddMonoidAlgebra.nonUnitalCommSemiring, AddMonoidAlgebra.semiring with }
instance unique [Semiring k] [Subsingleton k] : Unique k[G] :=
  Finsupp.uniqueOfRight
instance addCommGroup [Ring k] : AddCommGroup k[G] :=
  Finsupp.instAddCommGroup
instance nonUnitalNonAssocRing [Ring k] [Add G] : NonUnitalNonAssocRing k[G] :=
  { AddMonoidAlgebra.addCommGroup, AddMonoidAlgebra.nonUnitalNonAssocSemiring with }
instance nonUnitalRing [Ring k] [AddSemigroup G] : NonUnitalRing k[G] :=
  { AddMonoidAlgebra.addCommGroup, AddMonoidAlgebra.nonUnitalSemiring with }
instance nonAssocRing [Ring k] [AddZeroClass G] : NonAssocRing k[G] :=
  { AddMonoidAlgebra.addCommGroup,
    AddMonoidAlgebra.nonAssocSemiring with
    intCast := fun z => single 0 (z : k)
    intCast_ofNat := fun n => by simp; rfl
    intCast_negSucc := fun n => by simp; rfl }
theorem intCast_def [Ring k] [AddZeroClass G] (z : ℤ) :
    (z : k[G]) = single (0 : G) (z : k) :=
  rfl
@[deprecated (since := "2024-04-17")]
alias int_cast_def := intCast_def
instance ring [Ring k] [AddMonoid G] : Ring k[G] :=
  { AddMonoidAlgebra.nonAssocRing, AddMonoidAlgebra.semiring with }
instance nonUnitalCommRing [CommRing k] [AddCommSemigroup G] :
    NonUnitalCommRing k[G] :=
  { AddMonoidAlgebra.nonUnitalCommSemiring, AddMonoidAlgebra.nonUnitalRing with }
instance commRing [CommRing k] [AddCommMonoid G] : CommRing k[G] :=
  { AddMonoidAlgebra.nonUnitalCommRing, AddMonoidAlgebra.ring with }
variable {S : Type*}
instance distribSMul [Semiring k] [DistribSMul R k] : DistribSMul R k[G] :=
  Finsupp.distribSMul G k
instance distribMulAction [Monoid R] [Semiring k] [DistribMulAction R k] :
    DistribMulAction R k[G] :=
  Finsupp.distribMulAction G k
instance faithfulSMul [Semiring k] [SMulZeroClass R k] [FaithfulSMul R k] [Nonempty G] :
    FaithfulSMul R k[G] :=
  Finsupp.faithfulSMul
instance module [Semiring R] [Semiring k] [Module R k] : Module R k[G] :=
  Finsupp.module G k
instance isScalarTower [Semiring k] [SMulZeroClass R k] [SMulZeroClass S k] [SMul R S]
    [IsScalarTower R S k] : IsScalarTower R S k[G] :=
  Finsupp.isScalarTower G k
instance smulCommClass [Semiring k] [SMulZeroClass R k] [SMulZeroClass S k] [SMulCommClass R S k] :
    SMulCommClass R S k[G] :=
  Finsupp.smulCommClass G k
instance isCentralScalar [Semiring k] [SMulZeroClass R k] [SMulZeroClass Rᵐᵒᵖ k]
    [IsCentralScalar R k] : IsCentralScalar R k[G] :=
  Finsupp.isCentralScalar G k
end DerivedInstances
section ExtLemmas
@[ext]
theorem ext [Semiring k] ⦃f g : AddMonoidAlgebra k G⦄ (H : ∀ (x : G), f x = g x) :
    f = g :=
  Finsupp.ext H
abbrev singleAddHom [Semiring k] (a : G) : k →+ AddMonoidAlgebra k G := Finsupp.singleAddHom a
@[simp] lemma singleAddHom_apply [Semiring k] (a : G) (b : k) :
  singleAddHom a b = single a b := rfl
@[ext high]
theorem addHom_ext' {N : Type*} [Semiring k] [AddZeroClass N]
    ⦃f g : AddMonoidAlgebra k G →+ N⦄
    (H : ∀ (x : G), AddMonoidHom.comp f (singleAddHom x) = AddMonoidHom.comp g (singleAddHom x)) :
    f = g :=
  Finsupp.addHom_ext' H
@[ext]
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [Semiring k] [AddMonoid N]
    [DistribMulAction R N] [DistribMulAction R k]
    {f g : AddMonoidAlgebra k G →+[R] N}
    (h : ∀ a : G,
      f.comp (DistribMulActionHom.single (M := k) a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  Finsupp.distribMulActionHom_ext' h
abbrev lsingle [Semiring R] [Semiring k] [Module R k] (a : G) :
    k →ₗ[R] AddMonoidAlgebra k G := Finsupp.lsingle a
@[simp] lemma lsingle_apply [Semiring R] [Semiring k] [Module R k] (a : G) (b : k) :
  lsingle (R := R) a b = single a b := rfl
@[ext high]
lemma lhom_ext' {N : Type*} [Semiring R] [Semiring k] [AddCommMonoid N] [Module R N] [Module R k]
    ⦃f g : AddMonoidAlgebra k G →ₗ[R] N⦄
    (H : ∀ (x : G), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) :
    f = g :=
  Finsupp.lhom_ext' H
end ExtLemmas
section MiscTheorems
variable [Semiring k]
theorem mul_apply [DecidableEq G] [Add G] (f g : k[G]) (x : G) :
    (f * g) x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => if a₁ + a₂ = x then b₁ * b₂ else 0 :=
  @MonoidAlgebra.mul_apply k (Multiplicative G) _ _ _ _ _ _
theorem mul_apply_antidiagonal [Add G] (f g : k[G]) (x : G) (s : Finset (G × G))
    (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 + p.2 = x) : (f * g) x = ∑ p ∈ s, f p.1 * g p.2 :=
  @MonoidAlgebra.mul_apply_antidiagonal k (Multiplicative G) _ _ _ _ _ s @hs
theorem single_mul_single [Add G] {a₁ a₂ : G} {b₁ b₂ : k} :
    single a₁ b₁ * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
  @MonoidAlgebra.single_mul_single k (Multiplicative G) _ _ _ _ _ _
theorem single_commute_single [Add G] {a₁ a₂ : G} {b₁ b₂ : k}
    (ha : AddCommute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (single a₁ b₁) (single a₂ b₂) :=
  @MonoidAlgebra.single_commute_single k (Multiplicative G) _ _ _ _ _ _ ha hb
theorem single_pow [AddMonoid G] {a : G} {b : k} : ∀ n : ℕ, single a b ^ n = single (n • a) (b ^ n)
  | 0 => by
    simp only [pow_zero, zero_nsmul]
    rfl
  | n + 1 => by
    rw [pow_succ, pow_succ, single_pow n, single_mul_single, add_nsmul, one_nsmul]
@[simp]
theorem mapDomain_one {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Zero α] [Zero α₂]
    {F : Type*} [FunLike F α α₂] [ZeroHomClass F α α₂] (f : F) :
    (mapDomain f (1 : AddMonoidAlgebra β α) : AddMonoidAlgebra β α₂) =
      (1 : AddMonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_zero]
theorem mapDomain_mul {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Add α] [Add α₂]
    {F : Type*} [FunLike F α α₂] [AddHomClass F α α₂] (f : F) (x y : AddMonoidAlgebra β α) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp_rw [mul_def, mapDomain_sum, mapDomain_single, map_add]
  rw [Finsupp.sum_mapDomain_index]
  · congr
    ext a b
    rw [Finsupp.sum_mapDomain_index]
    · simp
    · simp [mul_add]
  · simp
  · simp [add_mul]
section
variable (k G)
@[simps]
def ofMagma [Add G] : Multiplicative G →ₙ* k[G] where
  toFun a := single a 1
  map_mul' a b := by simp only [mul_def, mul_one, sum_single_index, single_eq_zero, mul_zero]; rfl
def of [AddZeroClass G] : Multiplicative G →* k[G] :=
  { ofMagma k G with
    toFun := fun a => single a 1
    map_one' := rfl }
def of' : G → k[G] := fun a => single a 1
end
@[simp]
theorem of_apply [AddZeroClass G] (a : Multiplicative G) :
    of k G a = single a.toAdd 1 :=
  rfl
@[simp]
theorem of'_apply (a : G) : of' k G a = single a 1 :=
  rfl
theorem of'_eq_of [AddZeroClass G] (a : G) : of' k G a = of k G (.ofAdd a) := rfl
theorem of_injective [Nontrivial k] [AddZeroClass G] : Function.Injective (of k G) :=
  MonoidAlgebra.of_injective
theorem of'_commute [AddZeroClass G] {a : G} (h : ∀ a', AddCommute a a')
    (f : AddMonoidAlgebra k G) :
    Commute (of' k G a) f :=
  MonoidAlgebra.of_commute (G := Multiplicative G) h f
@[simps]
def singleHom [AddZeroClass G] : k × Multiplicative G →* k[G] where
  toFun a := single a.2.toAdd a.1
  map_one' := rfl
  map_mul' _a _b := single_mul_single.symm
@[simp]
theorem smul_single' (c : k) (a : G) (b : k) : c • single a b = single a (c * b) :=
  Finsupp.smul_single' c a b
theorem mul_single_apply_aux [Add G] (f : k[G]) (r : k) (x y z : G)
    (H : ∀ a, a + x = z ↔ a = y) : (f * single x r) z = f y * r :=
  @MonoidAlgebra.mul_single_apply_aux k (Multiplicative G) _ _ _ _ _ _ _ H
theorem mul_single_zero_apply [AddZeroClass G] (f : k[G]) (r : k) (x : G) :
    (f * single (0 : G) r) x = f x * r :=
  f.mul_single_apply_aux r _ _ _ fun a => by rw [add_zero]
theorem mul_single_apply_of_not_exists_add [Add G] (r : k) {g g' : G} (x : k[G])
    (h : ¬∃ d, g' = d + g) : (x * single g r) g' = 0 :=
  @MonoidAlgebra.mul_single_apply_of_not_exists_mul k (Multiplicative G) _ _ _ _ _ _ h
theorem single_mul_apply_aux [Add G] (f : k[G]) (r : k) (x y z : G)
    (H : ∀ a, x + a = y ↔ a = z) : (single x r * f) y = r * f z :=
  @MonoidAlgebra.single_mul_apply_aux k (Multiplicative G) _ _ _ _ _ _ _ H
theorem single_zero_mul_apply [AddZeroClass G] (f : k[G]) (r : k) (x : G) :
    (single (0 : G) r * f) x = r * f x :=
  f.single_mul_apply_aux r _ _ _ fun a => by rw [zero_add]
theorem single_mul_apply_of_not_exists_add [Add G] (r : k) {g g' : G} (x : k[G])
    (h : ¬∃ d, g' = g + d) : (single g r * x) g' = 0 :=
  @MonoidAlgebra.single_mul_apply_of_not_exists_mul k (Multiplicative G) _ _ _ _ _ _ h
theorem mul_single_apply [AddGroup G] (f : k[G]) (r : k) (x y : G) :
    (f * single x r) y = f (y - x) * r :=
  (sub_eq_add_neg y x).symm ▸ @MonoidAlgebra.mul_single_apply k (Multiplicative G) _ _ _ _ _ _
theorem single_mul_apply [AddGroup G] (r : k) (x : G) (f : k[G]) (y : G) :
    (single x r * f) y = r * f (-x + y) :=
  @MonoidAlgebra.single_mul_apply k (Multiplicative G) _ _ _ _ _ _
theorem liftNC_smul {R : Type*} [AddZeroClass G] [Semiring R] (f : k →+* R)
    (g : Multiplicative G →* R) (c : k) (φ : MonoidAlgebra k G) :
    liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ :=
  @MonoidAlgebra.liftNC_smul k (Multiplicative G) _ _ _ _ f g c φ
theorem induction_on [AddMonoid G] {p : k[G] → Prop} (f : k[G])
    (hM : ∀ g, p (of k G (Multiplicative.ofAdd g)))
    (hadd : ∀ f g : k[G], p f → p g → p (f + g))
    (hsmul : ∀ (r : k) (f), p f → p (r • f)) : p f := by
  refine Finsupp.induction_linear f ?_ (fun f g hf hg => hadd f g hf hg) fun g r => ?_
  · simpa using hsmul 0 (of k G (Multiplicative.ofAdd 0)) (hM 0)
  · convert hsmul r (of k G (Multiplicative.ofAdd g)) (hM g)
    simp
@[simps]
def mapDomainRingHom (k : Type*) [Semiring k] {H F : Type*} [AddMonoid G] [AddMonoid H]
    [FunLike F G H] [AddMonoidHomClass F G H] (f : F) : k[G] →+* k[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }
end MiscTheorems
end AddMonoidAlgebra
protected def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) :=
  { Finsupp.domCongr
      Multiplicative.ofAdd with
    toFun := equivMapDomain Multiplicative.ofAdd
    map_mul' := fun x y => by
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Multiplicative.ofAdd]
      exact MonoidAlgebra.mapDomain_mul (α := Multiplicative G) (β := k)
        (MulHom.id (Multiplicative G)) x y }
protected def MonoidAlgebra.toAdditive [Semiring k] [Mul G] :
    MonoidAlgebra k G ≃+* AddMonoidAlgebra k (Additive G) :=
  { Finsupp.domCongr Additive.ofMul with
    toFun := equivMapDomain Additive.ofMul
    map_mul' := fun x y => by
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Additive.ofMul]
      convert MonoidAlgebra.mapDomain_mul (β := k) (MulHom.id G) x y }
namespace AddMonoidAlgebra
variable {k G H}
section NonUnitalNonAssocAlgebra
variable (k) [Semiring k] [DistribSMul R k] [Add G]
instance isScalarTower_self [IsScalarTower R k k] :
    IsScalarTower R k[G] k[G] :=
  @MonoidAlgebra.isScalarTower_self k (Multiplicative G) R _ _ _ _
instance smulCommClass_self [SMulCommClass R k k] :
    SMulCommClass R k[G] k[G] :=
  @MonoidAlgebra.smulCommClass_self k (Multiplicative G) R _ _ _ _
instance smulCommClass_symm_self [SMulCommClass k R k] :
    SMulCommClass k[G] R k[G] :=
  @MonoidAlgebra.smulCommClass_symm_self k (Multiplicative G) R _ _ _ _
end NonUnitalNonAssocAlgebra
section Algebra
@[simps]
def singleZeroRingHom [Semiring k] [AddMonoid G] : k →+* k[G] :=
  { Finsupp.singleAddHom 0 with
    map_one' := rfl
    map_mul' := fun x y => by simp only [Finsupp.singleAddHom, single_mul_single, zero_add] }
theorem ringHom_ext {R} [Semiring k] [AddMonoid G] [Semiring R] {f g : k[G] →+* R}
    (h₀ : ∀ b, f (single 0 b) = g (single 0 b)) (h_of : ∀ a, f (single a 1) = g (single a 1)) :
    f = g :=
  @MonoidAlgebra.ringHom_ext k (Multiplicative G) R _ _ _ _ _ h₀ h_of
@[ext high]
theorem ringHom_ext' {R} [Semiring k] [AddMonoid G] [Semiring R] {f g : k[G] →+* R}
    (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom)
    (h_of : (f : k[G] →* R).comp (of k G) = (g : k[G] →* R).comp (of k G)) :
    f = g :=
  ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)
section Opposite
open Finsupp MulOpposite
variable [Semiring k]
@[simps! (config := { simpRhs := true }) apply symm_apply]
protected noncomputable def opRingEquiv [AddCommMonoid G] :
    k[G]ᵐᵒᵖ ≃+* kᵐᵒᵖ[G] :=
  { MulOpposite.opAddEquiv.symm.trans
      (Finsupp.mapRange.addEquiv (MulOpposite.opAddEquiv : k ≃+ kᵐᵒᵖ)) with
    map_mul' := by
      rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
      rw [← AddEquiv.coe_toAddMonoidHom]
      refine Iff.mpr (AddMonoidHom.map_mul_iff (R := k[G]ᵐᵒᵖ) (S := kᵐᵒᵖ[G]) _) ?_
      refine AddMonoidHom.mul_op_ext _ _ <| addHom_ext' fun i₁ => AddMonoidHom.ext fun r₁ =>
        AddMonoidHom.mul_op_ext _ _ <| addHom_ext' fun i₂ => AddMonoidHom.ext fun r₂ => ?_
      dsimp
      erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
        MulOpposite.opAddEquiv_symm_apply]; rw [MulOpposite.unop_mul (α := k[G])]
      dsimp
      rw [mapRange_single, single_mul_single, mapRange_single, mapRange_single]
      simp only [mapRange_single, single_mul_single, ← op_mul, add_comm] }
theorem opRingEquiv_single [AddCommMonoid G] (r : k) (x : G) :
    AddMonoidAlgebra.opRingEquiv (op (single x r)) = single x (op r) := by simp
theorem opRingEquiv_symm_single [AddCommMonoid G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    AddMonoidAlgebra.opRingEquiv.symm (single x r) = op (single x r.unop) := by simp
end Opposite
end Algebra
section
universe ui
variable {ι : Type ui}
theorem prod_single [CommSemiring k] [AddCommMonoid G] {s : Finset ι} {a : ι → G} {b : ι → k} :
    (∏ i ∈ s, single (a i) (b i)) = single (∑ i ∈ s, a i) (∏ i ∈ s, b i) :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons has, ih, single_mul_single, sum_cons has, prod_cons has]
end
end AddMonoidAlgebra
set_option linter.style.longFile 1700