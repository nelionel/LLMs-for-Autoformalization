import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ProjectionNotation
import Mathlib.Tactic.TypeStar
import Batteries.Classes.RatCast
@[inherit_doc] notation "ℚ" => Rat
def NNRat := {q : ℚ // 0 ≤ q}
@[inherit_doc] notation "ℚ≥0" => NNRat
class NNRatCast (K : Type*) where
  protected nnratCast : ℚ≥0 → K
instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q
variable {K : Type*} [NNRatCast K]
@[coe, reducible, match_pattern] protected def NNRat.cast : ℚ≥0 → K := NNRatCast.nnratCast
instance NNRatCast.toCoeTail [NNRatCast K] : CoeTail ℚ≥0 K where coe := NNRat.cast
instance NNRatCast.toCoeHTCT [NNRatCast K] : CoeHTCT ℚ≥0 K where coe := NNRat.cast
instance Rat.instNNRatCast : NNRatCast ℚ := ⟨Subtype.val⟩
namespace NNRat
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs
def den (q : ℚ≥0) : ℕ := (q : ℚ).den
@[simp] lemma num_mk (q : ℚ) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
@[simp] lemma den_mk (q : ℚ) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl
@[norm_cast] lemma cast_id (n : ℚ≥0) : NNRat.cast n = n := rfl
@[simp] lemma cast_eq_id : NNRat.cast = id := rfl
end NNRat
namespace Rat
@[norm_cast] lemma cast_id (n : ℚ) : Rat.cast n = n := rfl
@[simp] lemma cast_eq_id : Rat.cast = id := rfl
end Rat