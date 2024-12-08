import Mathlib.Tactic.Basic
import Mathlib.Tactic.ArithMult.Init
namespace ArithmeticFunction
macro "arith_mult" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `IsMultiplicative):ident]))
macro (name := arith_mult) "arith_mult" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { aesop $c* (config :=
    { destructProductsTransparency := .reducible,
      applyHypsTransparency := .default,
      introsTransparency? := some .reducible,
      enableSimp := false } )
  (rule_sets := [$(Lean.mkIdent `IsMultiplicative):ident])})
macro (name := arith_mult?) "arith_mult?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  { show_term { arith_mult $c* } })
end ArithmeticFunction