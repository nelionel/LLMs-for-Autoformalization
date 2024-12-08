import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.SMulWithZero
import Mathlib.Tactic.Common
variable {G₀ M₀ : Type*}
namespace OrderDual
instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ :=
  ‹SMulWithZero G₀ M₀›
instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ :=
  ‹SMulWithZero G₀ M₀›
instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ :=
  ‹DistribSMul G₀ M₀›
instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ :=
  ‹DistribSMul G₀ M₀›
instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ᵒᵈ M₀ := ‹DistribMulAction G₀ M₀›
instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ M₀ᵒᵈ := ‹DistribMulAction G₀ M₀›
instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ := ‹MulActionWithZero G₀ M₀›
instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ := ‹MulActionWithZero G₀ M₀›
end OrderDual
namespace Lex
instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ :=
  ‹SMulWithZero G₀ M₀›
instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) :=
  ‹SMulWithZero G₀ M₀›
instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ :=
  ‹DistribSMul G₀ M₀›
instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) :=
  ‹DistribSMul G₀ M₀›
instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction (Lex G₀) M₀ := ‹DistribMulAction G₀ M₀›
instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ (Lex M₀) := ‹DistribMulAction G₀ M₀›
instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero (Lex G₀) M₀ := ‹MulActionWithZero G₀ M₀›
instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ (Lex M₀) := ‹MulActionWithZero G₀ M₀›
end Lex