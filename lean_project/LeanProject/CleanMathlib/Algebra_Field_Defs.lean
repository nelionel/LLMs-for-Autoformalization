import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Rat.Init
assert_not_imported Mathlib.Tactic.Common
assert_not_imported Mathlib.Algebra.NeZero
assert_not_exists MonoidHom
open Function Set
universe u
variable {K : Type*}
def NNRat.castRec [NatCast K] [Div K] (q : ℚ≥0) : K := q.num / q.den
def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den
class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K, NNRatCast K where
  protected nnratCast := NNRat.castRec
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  protected nnqsmul : ℚ≥0 → K → K
  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
class DivisionRing (K : Type*)
  extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K where
  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
  protected inv_zero : (0 : K)⁻¹ = 0
  protected nnratCast := NNRat.castRec
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : K) = q.num / q.den := by intros; rfl
  protected nnqsmul : ℚ≥0 → K → K
  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  protected ratCast_def (q : ℚ) : (Rat.cast q : K) = q.num / q.den := by intros; rfl
  protected qsmul : ℚ → K → K
  protected qsmul_def (a : ℚ) (x : K) : qsmul a x = Rat.cast a * x := by intros; rfl
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing K] : DivisionSemiring K :=
  { ‹DivisionRing K› with }
class Semifield (K : Type*) extends CommSemiring K, DivisionSemiring K, CommGroupWithZero K
@[stacks 09FD "first part"]
class Field (K : Type u) extends CommRing K, DivisionRing K
instance (priority := 100) Field.toSemifield [Field K] : Semifield K := { ‹Field K› with }
namespace NNRat
variable [DivisionSemiring K]
instance (priority := 100) smulDivisionSemiring : SMul ℚ≥0 K := ⟨DivisionSemiring.nnqsmul⟩
lemma cast_def (q : ℚ≥0) : (q : K) = q.num / q.den := DivisionSemiring.nnratCast_def _
lemma smul_def (q : ℚ≥0) (a : K) : q • a = q * a := DivisionSemiring.nnqsmul_def q a
variable (K)
@[simp] lemma smul_one_eq_cast (q : ℚ≥0) : q • (1 : K) = q := by rw [NNRat.smul_def, mul_one]
@[deprecated (since := "2024-05-03")] alias smul_one_eq_coe := smul_one_eq_cast
end NNRat
namespace Rat
variable [DivisionRing K]
lemma cast_def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _
lemma cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a / b := cast_def _
instance (priority := 100) smulDivisionRing : SMul ℚ K :=
  ⟨DivisionRing.qsmul⟩
theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x
@[simp]
theorem smul_one_eq_cast (A : Type*) [DivisionRing A] (m : ℚ) : m • (1 : A) = ↑m := by
  rw [Rat.smul_def, mul_one]
@[deprecated (since := "2024-05-03")] alias smul_one_eq_coe := smul_one_eq_cast
end Rat
@[simp]
theorem Rat.ofScientific_eq_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e := rfl