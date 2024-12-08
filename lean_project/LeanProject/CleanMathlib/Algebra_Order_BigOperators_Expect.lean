import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Module.Rat
open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat
variable {ι α R : Type*}
local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a
namespace Finset
section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α] [Module ℚ≥0 α] {s : Finset ι} {f g : ι → α}
lemma expect_eq_zero_iff_of_nonneg (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, hs.ne_empty]
lemma expect_eq_zero_iff_of_nonpos (hs : s.Nonempty) (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, hs.ne_empty]
section PosSMulMono
variable [PosSMulMono ℚ≥0 α] {a : α}
lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  smul_le_smul_of_nonneg_left (sum_le_sum hfg) <| by positivity
@[gcongr]
lemma _root_.GCongr.expect_le_expect (h : ∀ i ∈ s, f i ≤ g i) : s.expect f ≤ s.expect g :=
  Finset.expect_le_expect h
lemma expect_le (hs : s.Nonempty) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h
lemma le_expect (hs : s.Nonempty) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h
lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  smul_nonneg (by positivity) <| sum_nonneg hf
end PosSMulMono
section PosSMulMono
variable {M N : Type*} [AddCommMonoid M] [Module ℚ≥0 M] [OrderedAddCommMonoid N] [Module ℚ≥0 N]
  [PosSMulMono ℚ≥0 N] {m : M → N} {p : M → Prop} {f : ι → M} {s : Finset ι}
lemma le_expect_nonempty_of_subadditive_on_pred (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b)
    (hp_add : ∀ a b, p a → p b → p (a + b)) (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (f i)) :
    m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
    (le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) <| by positivity
lemma le_expect_nonempty_of_subadditive (m : M → N) (h_mul : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) (hs : s.Nonempty) :
    m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) :=
  le_expect_nonempty_of_subadditive_on_pred (p := fun _ ↦ True) (by simpa) (by simp) (by simpa) hs
    (by simp)
lemma le_expect_of_subadditive_on_pred (h_zero : m 0 = 0)
    (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b) (hp_add : ∀ a b, p a → p b → p (a + b))
    (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs : ∀ i ∈ s, p (f i)) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs
lemma le_expect_of_subadditive (h_zero : m 0 = 0) (h_add : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) :=
  le_expect_of_subadditive_on_pred (p := fun _ ↦ True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)
end PosSMulMono
end OrderedAddCommMonoid
section OrderedCancelAddCommMonoid
variable [OrderedCancelAddCommMonoid α] [Module ℚ≥0 α] {s : Finset ι} {f : ι → α}
section PosSMulStrictMono
variable [PosSMulStrictMono ℚ≥0 α]
lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  smul_pos (inv_pos.2 <| mod_cast hs.card_pos) <| sum_pos hf hs
end PosSMulStrictMono
end OrderedCancelAddCommMonoid
section LinearOrderedAddCommMonoid
variable [LinearOrderedAddCommMonoid α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α] {s : Finset ι}
  {f : ι → α} {a : α}
lemma exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i ∈ s, f i) : ∃ x ∈ s, a < f x := by
  contrapose! h; exact expect_le hs h
lemma exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i < a) : ∃ x ∈ s, f x < a := by
  contrapose! h; exact le_expect hs h
end LinearOrderedAddCommMonoid
section LinearOrderedAddCommGroup
variable [LinearOrderedAddCommGroup α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]
lemma abs_expect_le (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive abs_zero abs_add (fun _ ↦ abs_nnqsmul _)
end LinearOrderedAddCommGroup
section LinearOrderedCommSemiring
variable [LinearOrderedCommSemiring R] [ExistsAddOfLE R] [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]
lemma expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (𝔼 i ∈ s, f i * g i) ^ 2 ≤ (𝔼 i ∈ s, f i ^ 2) * 𝔼 i ∈ s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..
end LinearOrderedCommSemiring
end Finset
open Finset
namespace Fintype
variable [Fintype ι]
section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α] [Module ℚ≥0 α] {f : ι → α}
lemma expect_eq_zero_iff_of_nonneg [Nonempty ι] (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, univ_nonempty.ne_empty]
lemma expect_eq_zero_iff_of_nonpos [Nonempty ι] (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, univ_nonempty.ne_empty]
end OrderedAddCommMonoid
end Fintype
open Finset
namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
open scoped BigOperators
attribute [local instance] monadLiftOptionMetaM in
@[positivity Finset.expect _ _]
def evalFinsetExpect : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.expect $ι _ $instα $instmod $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) := ← (do
      let .positive pbody := rbody | pure none 
      let .some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(OrderedCancelAddCommMonoid $α) | pure none
      let .some instαordsmul ← trySynthInstanceQ q(PosSMulStrictMono ℚ≥0 $α) | pure none
      assumeInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      return some q(@expect_pos $ι $α $pα' $instmod $s $f $instαordsmul (fun i _ ↦ $pr i) $ps))
    if let some p_pos := p_pos then
      return .positive p_pos
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let instαordmon ← synthInstanceQ q(OrderedAddCommMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulMono ℚ≥0 $α)
      assumeInstancesCommute
      return .nonnegative q(@expect_nonneg $ι $α $instαordmon $instmod $s $f $instαordsmul
        fun i _ ↦ $pr i)
  | _ => throwError "not Finset.expect"
example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j ∈ range n, a j^2 := by positivity
example (a : ULift.{2} ℕ → ℚ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ 𝔼 j ∈ s, a j^2 := by positivity
example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j : Fin 8, 𝔼 i ∈ range n, (a j^2 + i ^ 2) := by positivity
example (n : ℕ) (a : ℕ → ℚ) : 0 < 𝔼 j : Fin (n + 1), (a j^2 + 1) := by positivity
example (a : ℕ → ℚ) : 0 < 𝔼 j ∈ ({1} : Finset ℕ), (a j^2 + 1) := by positivity
end Mathlib.Meta.Positivity