import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Abel
namespace Mathlib.Tactic.NoncommRing
section nat_lit_mul
variable {R : Type*} [NonAssocSemiring R] (r : R) (n : ℕ)
lemma nat_lit_mul_eq_nsmul [n.AtLeastTwo] : no_index (OfNat.ofNat n) * r = n • r := by
  simp only [nsmul_eq_mul, Nat.cast_eq_ofNat]
lemma mul_nat_lit_eq_nsmul [n.AtLeastTwo] : r * no_index (OfNat.ofNat n) = n • r := by
  simp only [nsmul_eq_mul', Nat.cast_eq_ofNat]
end nat_lit_mul
open Lean.Parser.Tactic
syntax (name := noncomm_ring) "noncomm_ring" optConfig (discharger)?
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic
macro_rules
  | `(tactic| noncomm_ring $cfg:optConfig $[$disch]? $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    let tac ← `(tactic|
      (first | simp $cfg:optConfig $(disch)? only [
          add_mul, mul_add, sub_eq_add_neg,
          mul_assoc,
          pow_one, pow_zero, pow_succ,
          one_mul, mul_one, zero_mul, mul_zero,
          nat_lit_mul_eq_nsmul, mul_nat_lit_eq_nsmul,
          mul_smul_comm, smul_mul_assoc,
          neg_mul, mul_neg,
          $rules',*] |
        fail "`noncomm_ring` simp lemmas don't apply; try `abel` instead") <;>
      first | abel1 | abel_nf)
    if rules.isSome then `(tactic| repeat1 ($tac;)) else `(tactic| $tac)
end Mathlib.Tactic.NoncommRing